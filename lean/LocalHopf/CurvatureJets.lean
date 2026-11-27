import LocalHopf.Profiles
import Mathlib.Algebra.Polynomial.Coeff

/-! # Algebra of the coordinate curvature calculation

The inverse identity retains the order-four remainder. The tilt formulas compute
Taylor coefficients of a polynomial curvature operator evaluated on the exterior
product of two moving vectors, as in `verification/quadratic_coefficient.py`.
-/
namespace LocalHopf.CurvatureJets
open Polynomial
noncomputable section

/-- With `A` the inverse background matrix and `E` the perturbation divided by
`s`, this is the inverse expansion used by `inverse_jet`, through order three. -/
def inverseCubic {R : Type*} [Ring R] [Algebra ℝ R] (s : ℝ) (A E : R) : R :=
  let K := s • (A*E)
  (1-K+K^2-K^3)*A

/-- Exact remainder for the true inverse `B`; the identity applies to noncommuting
matrices and to a parameter-dependent `E`. -/
theorem inverse_remainder {R : Type*} [Ring R] [Algebra ℝ R] (s : ℝ) (G A E B : R)
    (hA : A*G = 1) (hB : (G+s • E)*B = 1) :
    B - inverseCubic s A E = s^4 • ((A*E)^4*B) := by
  let K := s • (A*E)
  have h : (1+K)*B = A := by
    calc
      (1+K)*B = (A*(G+s • E))*B := by rw [mul_add, hA, mul_smul_comm]
      _ = A := by rw [mul_assoc, hB, mul_one]
  have ht : (1-K+K^2-K^3)*(1+K) = 1-K^4 := by noncomm_ring
  change B - (1-K+K^2-K^3)*A = _
  conv_lhs => arg 2; arg 2; rw [← h]
  rw [← mul_assoc, ht, sub_mul, one_mul, sub_sub_cancel]
  simp [K, smul_pow]

abbrev Index := {ij : Fin 4 × Fin 4 // ij.1 < ij.2}
abbrev Vector := Fin 4 → ℝ
abbrev Bivector := Index → ℝ
abbrev OperatorJet := Index → Index → ℝ[X]

/-- Six Plücker coordinates in the order-independent `i < j` indexing. -/
def wedge (U V : Vector) (k : Index) : ℝ := U k.val.1*V k.val.2 - U k.val.2*V k.val.1

/-- Coefficients of the bivector of the tilt `(U+sA,V+sB)`. -/
def tilt (W L Q : ℝ) : ℝ[X] := C W + C L * X + C Q * X^2

theorem tilt_eval (U V A B : Vector) (s : ℝ) (i : Index) :
    (tilt (wedge U V i) (wedge A V i + wedge U B i) (wedge A B i)).eval s =
      wedge (U+s • A) (V+s • B) i := by
  simp [tilt, wedge]
  ring

def numerator (R : OperatorJet) (W L Q : Bivector) : ℝ[X] :=
  ∑ i, ∑ j, R i j * tilt (W i) (L i) (Q i) * tilt (W j) (L j) (Q j)

def contract (R : OperatorJet) (n : ℕ) (A B : Bivector) : ℝ :=
  ∑ i, ∑ j, (R i j).coeff n * A i * B j

theorem contract_symm (R : OperatorJet) (hR : ∀ i j, R i j = R j i)
    (n : ℕ) (A B : Bivector) : contract R n A B = contract R n B A := by
  unfold contract
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hR j i]
  ring

private theorem tilt_zero (w l q : ℝ) : (tilt w l q).coeff 0 = w := by simp [tilt]

private theorem tilted_coeff (P : ℝ[X]) (w l q : ℝ) (n : ℕ) :
    (P * tilt w l q).coeff n = P.coeff n * w +
      (if 1 ≤ n then P.coeff (n-1)*l else 0) +
      (if 2 ≤ n then P.coeff (n-2)*q else 0) := by
  cases n <;> simp [tilt, mul_add, ← mul_assoc, coeff_mul_X_pow']

private theorem numerator_eq_sum (R : OperatorJet) (W L Q : Bivector) (n : ℕ) :
    (numerator R W L Q).coeff n = ∑ i, ∑ j,
      ((R i j * tilt (W i) (L i) (Q i)) * tilt (W j) (L j) (Q j)).coeff n := by
  simp [numerator]

/-- The three surviving tilt contributions in addition to the untilted second
coefficient; the convention matches the Hessian factor of two in the scripts. -/
theorem quadratic (R : OperatorJet) (hR : ∀ i j, R i j = R j i) (W L Q : Bivector) :
    (numerator R W L Q).coeff 2 = contract R 2 W W + 2*contract R 1 W L +
      contract R 0 L L + 2*contract R 0 W Q := by
  have h (n : ℕ) (A B : Bivector) := contract_symm R hR n A B
  rw [show 2*contract R 1 W L = contract R 1 W L + contract R 1 L W by rw [h 1 L W]; ring,
    show 2*contract R 0 W Q = contract R 0 W Q + contract R 0 Q W by rw [h 0 Q W]; ring]
  rw [numerator_eq_sum]
  unfold contract
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  norm_num [tilted_coeff, tilt_zero]
  ring

/-- The cubic tilt contributions, including the mixed linear-quadratic tilt
term even when the individual third-order curvature channels vanish. -/
theorem cubic (R : OperatorJet) (hR : ∀ i j, R i j = R j i) (W L Q : Bivector) :
    (numerator R W L Q).coeff 3 = contract R 3 W W + 2*contract R 2 W L +
      contract R 1 L L + 2*contract R 1 W Q + 2*contract R 0 L Q := by
  have h (n : ℕ) (A B : Bivector) := contract_symm R hR n A B
  rw [show 2*contract R 2 W L = contract R 2 W L + contract R 2 L W by rw [h 2 L W]; ring,
    show 2*contract R 1 W Q = contract R 1 W Q + contract R 1 Q W by rw [h 1 Q W]; ring,
    show 2*contract R 0 L Q = contract R 0 L Q + contract R 0 Q L by rw [h 0 Q L]; ring]
  rw [numerator_eq_sum]
  unfold contract
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  norm_num [tilted_coeff, tilt_zero]
  ring

end
end LocalHopf.CurvatureJets
