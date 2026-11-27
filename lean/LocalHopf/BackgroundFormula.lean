import LocalHopf.Cheeger
import LocalHopf.Profiles
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The background pairing off the torus in closed form. In particular its
coordinate derivatives require only scalar arithmetic and the sphere chart. -/
namespace LocalHopf.Cheeger
open Matrix Profiles
noncomputable section

/-- Solve the three-dimensional orbit equation using the two dot products with
the sphere points. The denominator stays positive also when the points agree
or are antipodal. -/
def orbitSolve (p q : R3) (t : ℝ) (a : R3) : R3 :=
  let u := p ⬝ᵥ q
  let coeff (x y : R3) := ((1+t)*(x ⬝ᵥ a)+t*u*(y ⬝ᵥ a))/D t u
  (hh t)⁻¹ • (a + t • (coeff p q • p + coeff q p • q))

private theorem solves (p q : R3) {t : ℝ} (ht : 0 ≤ t) (hp : p ⬝ᵥ p = 1) (hq : q ⬝ᵥ q = 1) (a : R3) :
    orbitSolve p q t a + t • orbit p q (orbitSolve p q t a) = a := by
  let u := p ⬝ᵥ q
  let coeff (x y : R3) := ((1+t)*(x ⬝ᵥ a)+t*u*(y ⬝ᵥ a))/D t u
  let b := orbitSolve p q t a
  have pos : 0 ≤ (p ⨯₃ q) ⬝ᵥ (p ⨯₃ q) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg ((p ⨯₃ q) i)
  rw [cross_dot_cross,hp,hq,dotProduct_comm q p] at pos
  have hd : D t u ≠ 0 := (D_pos ht (by dsimp only [u]; nlinarith only [pos])).ne'
  have hh' := (hh_pos ht).ne'
  have dot (x y : R3) (hx : x ⬝ᵥ x = 1) (xy : x ⬝ᵥ y = u)
      (form : b = (hh t)⁻¹ • (a+t • (coeff x y • x+coeff y x • y))) :
      x ⬝ᵥ b = coeff x y := by
    rw [form]
    simp only [dotProduct_smul,dotProduct_add,smul_eq_mul,hx,xy,coeff]
    field_simp [hd,hh']
    unfold hh D
    ring
  have pb := dot p q hp rfl rfl
  have qb := dot q p hq (dotProduct_comm _ _) (by simp only [b,orbitSolve,coeff,u,add_comm])
  change b + t • ((2:ℝ) • b - (p ⬝ᵥ b) • p - (q ⬝ᵥ b) • q) = a
  rw [pb,qb]
  have inv : hh t • b = a+t • (coeff p q • p+coeff q p • q) := by
    change hh t • ((hh t)⁻¹ • _) = _
    rw [smul_smul,mul_inv_cancel₀ hh',one_smul]
  calc
    _ = hh t • b - t • (coeff p q • p+coeff q p • q) := by unfold hh; module
    _ = _ := by rw [inv]; abel

theorem operator_formula (p q : R3) {t : ℝ} (ht : 0 ≤ t) (hp : p ⬝ᵥ p = 1)
    (hq : q ⬝ᵥ q = 1) (X : V) :
    operator p q t ht X = X - t • K p q (orbitSolve p q t (moment p q X)) := by
  let b := orbitSolve p q t (moment p q X)
  have orb : moment p q (K p q b) = orbit p q b := by
    simp [moment,K,orbit,cross_cross_eq_smul_sub_smul',hp,hq,dotProduct_comm b p,dotProduct_comm b q]
    module
  have mo : moment p q (X-t • K p q b) = b := by
    have eq : moment p q (X-t • K p q b) = moment p q X - t • moment p q (K p q b) := by
      simp [moment,smul_add]; abel
    rw [eq,orb,← show b+t • orbit p q b = moment p q X from solves p q ht hp hq _]
    abel
  apply (inverseEquiv p q t ht).injective
  change inverseOperator p q t (operator p q t ht X) = inverseOperator p q t (X-t • K p q b)
  rw [inverse_operator,inverseOperator_apply,mo,sub_add_cancel]

/-- Twice the actual Cheeger background, without an inverse-matrix operation. -/
theorem pairing_formula (p q : R3) {t : ℝ} (ht : 0 ≤ t) (hp : p ⬝ᵥ p = 1)
    (hq : q ⬝ᵥ q = 1) (X Y : V) :
    pairing p q t ht X Y = gprod X Y - t * (moment p q Y ⬝ᵥ orbitSolve p q t (moment p q X)) := by
  rw [pairing,operator_formula p q ht hp hq,← gprod_K_eq_moment]
  simp only [gprod,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,sub_dotProduct,
    smul_dotProduct,smul_eq_mul,dotProduct_comm Y.1,dotProduct_comm Y.2]
  ring


/-- A longitude generator with independent angular speeds on the two spheres. -/
def longitude (p q n : R3) (a b : ℝ) : V := (a • (n ⨯₃ p),b • (n ⨯₃ q))

/-- Pair two longitude generators at any heights z,w and separation u. -/
def longitudeGram (t u z w a b c d : ℝ) :=
  let s := a*d+b*c
  let m := (a+b)*(c+d) - (a*c+s)*z^2 - (b*d+s)*w^2 + s*u*z*w
  let i := z-u*w
  let j := w-u*z
  a*c*(1-z^2)+b*d*(1-w^2) - t/(hh t) *
    (m+t/D t u*((1+t)*(b*d*i^2+a*c*j^2)+t*u*s*i*j))

theorem pairing_longitude (p q n : R3) {t : ℝ} (ht : 0 ≤ t) (hp : p ⬝ᵥ p = 1)
    (hq : q ⬝ᵥ q = 1) (hn : n ⬝ᵥ n = 1) (a b c d : ℝ) :
    pairing p q t ht (longitude p q n a b) (longitude p q n c d) =
      longitudeGram t (p ⬝ᵥ q) (n ⬝ᵥ p) (n ⬝ᵥ q) a b c d := by
  have mm (a b : ℝ) : moment p q (longitude p q n a b) =
      (a+b) • n - (a*(n ⬝ᵥ p)) • p - (b*(n ⬝ᵥ q)) • q := by
    simp [moment,longitude,cross_cross_eq_smul_sub_smul',hp,hq,smul_sub,smul_smul,add_smul]
    abel
  rw [pairing_formula p q ht hp hq,mm,mm]
  simp only [gprod,longitude,orbitSolve,longitudeGram,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    dotProduct_add,sub_dotProduct,dotProduct_sub,cross_dot_cross,hp,hq,hn,
    dotProduct_comm p n,dotProduct_comm q n,dotProduct_comm q p]
  ring

/-- The longitude block of the genuine metric is stationary in every spatial
direction at zero height, even when separation changes along the curve. -/
theorem longitudeGram_stationary (a b c d : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {u z w : ℝ → ℝ} {x : ℝ} (du : DifferentiableAt ℝ u x) (dz : DifferentiableAt ℝ z x)
    (dw : DifferentiableAt ℝ w x) (uz : u x ^ 2 ≤ 1) (hz : z x = 0) (hw : w x = 0) :
    HasDerivAt (fun r => longitudeGram t (u r) (z r) (w r) a b c d) 0 x := by
  have ju := du.hasDerivAt
  have jz := dz.hasDerivAt
  have jw := dw.hasDerivAt
  have ii := jz.sub (ju.mul jw)
  have jj := jw.sub (ju.mul jz)
  have m₀ := (hasDerivAt_const x ((a+b)*(c+d))).sub ((jz.pow 2).const_mul (a*c+(a*d+b*c)))
  have m₁ := m₀.sub ((jw.pow 2).const_mul (b*d+(a*d+b*c)))
  have mm := m₁.add (((ju.const_mul (a*d+b*c)).mul jz).mul jw)
  have den := (hasDerivAt_const x ((1+t)^2)).sub ((ju.pow 2).const_mul (t^2))
  have rat := (hasDerivAt_const x t).div den ((D_pos ht uz).ne')
  have diag := ((ii.pow 2).const_mul (b*d)).add ((jj.pow 2).const_mul (a*c))
  have off := (((ju.const_mul t).mul_const (a*d+b*c)).mul ii).mul jj
  have rem := rat.mul ((diag.const_mul (1+t)).add off)
  have full := ((((jz.pow 2).const_sub 1).const_mul (a*c)).add (((jw.pow 2).const_sub 1).const_mul (b*d))).sub
    ((mm.add rem).const_mul (t/hh t))
  convert full using 1 <;> simp [longitudeGram,D,Pi.sub_apply,Pi.mul_apply,Pi.add_apply,Pi.div_apply,Pi.pow_apply,hz,hw]
  rfl


end
end LocalHopf.Cheeger
