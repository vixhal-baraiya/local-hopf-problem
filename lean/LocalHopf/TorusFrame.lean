import LocalHopf.PerturbationTensors

/-! # The metric in the longitude-height frame of the curvature scripts

The simultaneous and opposite longitude directions are `K n` and `J n`. The
two height directions are the common great-circle normal in each sphere factor.
-/
namespace LocalHopf.SphereProduct
open Matrix
open scoped ContDiff Manifold
open Profiles
noncomputable section

private theorem moment_KJ (p q n : R3) (hp : p ⬝ᵥ p = 1) (hq : q ⬝ᵥ q = 1)
    (hnp : n ⬝ᵥ p = 0) (hnq : n ⬝ᵥ q = 0) :
    moment p q (K p q n) = (2:ℝ) • n ∧ moment p q (J p q n) = 0 := by
  simp [moment, K, J, cross_cross_eq_smul_sub_smul', hp, hq, hnp, hnq,
    dotProduct_comm q n, two_smul]

theorem operator_longitude (p q n : R3) (t : ℝ) (ht : 0 ≤ t) (hp : p ⬝ᵥ p = 1)
    (hq : q ⬝ᵥ q = 1) (hnp : n ⬝ᵥ p = 0) (hnq : n ⬝ᵥ q = 0) :
    Cheeger.operator p q t ht (K p q n) = (hh t)⁻¹ • K p q n ∧
    Cheeger.operator p q t ht (J p q n) = J p q n := by
  obtain ⟨hk,hj⟩ := moment_KJ p q n hp hq hnp hnq
  have h : hh t ≠ 0 := by unfold hh; linarith
  have hinj := (Cheeger.inverseEquiv p q t ht).injective
  have hK : Cheeger.inverseOperator p q t (K p q n) = hh t • K p q n := by
    rw [Cheeger.inverseOperator_apply, hk]
    simp [K, hh, add_smul, smul_smul, mul_comm t 2]
  have hJ : Cheeger.inverseOperator p q t (J p q n) = J p q n := by
    rw [Cheeger.inverseOperator_apply, hj]; simp [K]
  constructor
  · apply hinj
    change Cheeger.inverseOperator p q t (Cheeger.operator p q t ht _) = Cheeger.inverseOperator p q t _
    rw [Cheeger.inverse_operator, map_smul, hK, smul_smul, inv_mul_cancel₀ h, one_smul]
  · apply hinj
    change Cheeger.inverseOperator p q t (Cheeger.operator p q t ht _) = Cheeger.inverseOperator p q t _
    rw [Cheeger.inverse_operator, hJ]

/-- The inverse background height block. The off-diagonal entry contains the
separation `p · q`, with no division by the sine of the separation. -/
theorem inverse_height (p q n : R3) (t a b : ℝ) (hp : p ⬝ᵥ p = 1) (hq : q ⬝ᵥ q = 1)
    (hnp : n ⬝ᵥ p = 0) (hnq : n ⬝ᵥ q = 0) :
    Cheeger.inverseOperator p q t (a • n, b • n) =
      (((1+t)*a+t*(p ⬝ᵥ q)*b) • n, (t*(p ⬝ᵥ q)*a+(1+t)*b) • n) := by
  rw [Cheeger.inverseOperator_apply]
  simp [K, moment, cross_cross_eq_smul_sub_smul, hp, hq, hnp, hnq, dotProduct_comm q p,
    smul_smul, add_smul, smul_add]
  constructor <;> module

/-- Inversion gives the two height entries used by `jets.py:geometry` for the
background. This holds for singular as well as regular pairs. -/
theorem operator_height (p q n : R3) (t a b : ℝ) (ht : 0 ≤ t) (hp : p ⬝ᵥ p = 1)
    (hq : q ⬝ᵥ q = 1) (hnp : n ⬝ᵥ p = 0) (hnq : n ⬝ᵥ q = 0) (hd : D t (p ⬝ᵥ q) ≠ 0) :
    Cheeger.operator p q t ht (a • n, b • n) =
      ((((1+t)*a - t*(p ⬝ᵥ q)*b)/D t (p ⬝ᵥ q)) • n,
       (((1+t)*b - t*(p ⬝ᵥ q)*a)/D t (p ⬝ᵥ q)) • n) := by
  apply (Cheeger.inverseEquiv p q t ht).injective
  change Cheeger.inverseOperator p q t (Cheeger.operator p q t ht _) = Cheeger.inverseOperator p q t _
  rw [Cheeger.inverse_operator, inverse_height p q n _ _ _ hp hq hnp hnq]
  congr 2 <;> field_simp <;> unfold D <;> ring

/-- On any great-circle torus the covectors of §2 depend only on the torus
normal when evaluated on the two longitude directions. -/
theorem rotationFlat_longitude (t : ℝ) (ht : 0 ≤ t) (p : Base) (n : R3)
    (hnp : n ⬝ᵥ point₁ p = 0) (hnq : n ⬝ᵥ point₂ p = 0) (a : Axis) :
    let U := K (point₁ p) (point₂ p) n
    let V := J (point₁ p) (point₂ p) n
    rotationFlat t ht false a p U = (a p ⬝ᵥ n) / hh t ∧
    rotationFlat t ht false a p V = 0 ∧ rotationFlat t ht true a p U = 0 ∧
    rotationFlat t ht true a p V = a p ⬝ᵥ n := by
  let P := point₁ p
  let Q := point₂ p
  change n ⬝ᵥ P = 0 at hnp
  change n ⬝ᵥ Q = 0 at hnq
  have hp : P ⬝ᵥ P = 1 := (unitSphere.symm p.1).property
  have hq : Q ⬝ᵥ Q = 1 := (unitSphere.symm p.2).property
  obtain ⟨hK,hJ⟩ := operator_longitude P Q n t ht hp hq hnp hnq
  have evalK (W : Cheeger.V) : ambientBackground t p W (K P Q n) =
      (hh t)⁻¹ * gprod (K P Q n) W / 2 := by
    rw [ambientBackground_apply p ht, Cheeger.pairing_symm]
    change gprod (Cheeger.operator P Q t ht (K P Q n)) W / 2 = _
    rw [hK]; simp [gprod, smul_dotProduct, mul_add]
  have evalJ (W : Cheeger.V) : ambientBackground t p W (J P Q n) = gprod (J P Q n) W / 2 := by
    rw [ambientBackground_apply p ht, Cheeger.pairing_symm]
    change gprod (Cheeger.operator P Q t ht (J P Q n)) W / 2 = _
    rw [hJ]
  change ambientBackground t p (K P Q (a p)) (K P Q n) = _ ∧
    ambientBackground t p (K P Q (a p)) (J P Q n) = _ ∧
    ambientBackground t p (J P Q (a p)) (K P Q n) = _ ∧
    ambientBackground t p (J P Q (a p)) (J P Q n) = _
  rw [evalK, evalJ, evalK, evalJ]
  simp [K, J, gprod, cross_dot_cross, hp, hq, hnp, hnq, dotProduct_comm n (a p), div_eq_mul_inv]
  constructor <;> ring

/-- The full first-order tensor pulled back to a great-circle torus, in its
simultaneous/opposite rotation frame. All three coefficients are independent of
the two longitudes (the constancy calculation in Lemma 4.3). -/
theorem firstOrder_on_torus (t : ℝ) (ht : 0 ≤ t) (p : Base) (n : R3)
    (hp : n ⬝ᵥ point₁ p = 0) (hq : n ⬝ᵥ point₂ p = 0) :
    let U := K (point₁ p) (point₂ p) n
    let V := J (point₁ p) (point₂ p) n
    let H := (firstOrderTensor t ht).form p
    H U U = lamC*(n 2/hh t)^2 ∧ H U V = lamD * (n 0/hh t) * n 2 / 2 ∧ H V V = 0 := by
  dsimp only
  let v := point₁ + point₂
  let w := point₂ - point₁
  have hv : v p ⬝ᵥ n = 0 := by
    change (point₁ p + point₂ p) ⬝ᵥ n = 0
    rw [dotProduct_comm, dotProduct_add, hp, hq, add_zero]
  have hw : w p ⬝ᵥ n = 0 := by
    change (point₂ p - point₁ p) ⬝ᵥ n = 0
    rw [dotProduct_comm, dotProduct_sub, hp, hq, sub_self]
  have e (i : Fin 3) : axis i p ⬝ᵥ n = n i := by
    change Pi.single i (1:ℝ) ⬝ᵥ n = n i
    rw [single_dotProduct, one_mul]
  have rot := rotationFlat_longitude t ht p n hp hq
  simp only [firstOrderTensor_apply, (rot _).1, (rot _).2.1, (rot _).2.2.1,
    (rot _).2.2.2, ← show v = point₁+point₂ from rfl, ← show w = point₂-point₁ from rfl,
    hv, hw, e, zero_div, zero_mul, mul_zero, zero_add, add_zero]
  exact ⟨by ring, by ring, trivial⟩


/-- In the scripts the longitudes change by `x-y` and `x+y`, so their second
coordinate vector is the negative of `J n`. -/
theorem firstOrder_script_mixed (t : ℝ) (ht : 0 ≤ t) (p : Base) (n : R3)
    (hp : n ⬝ᵥ point₁ p = 0) (hq : n ⬝ᵥ point₂ p = 0) :
    (firstOrderTensor t ht).form p (K (point₁ p) (point₂ p) n) (-(J (point₁ p) (point₂ p) n)) =
      -(lamD * (n 0/hh t) * n 2 / 2) := by
  rw [map_neg, (firstOrder_on_torus t ht p n hp hq).2.1]


end
end LocalHopf.SphereProduct
