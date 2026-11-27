import LocalHopf.Vectors
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! # The pointwise Cheeger metric

The differential of the submersion in §1 sends `(v, ω)` to `v - K ω`.
The formulas below compute its horizontal lift and the induced metric directly
in the ambient coordinates of the two sphere factors.
-/

namespace LocalHopf.Cheeger

open Matrix
abbrev V := R3 × R3

private def action (p q : R3) : R3 →ₗ[ℝ] V :=
  (crossProduct.flip p).prod (crossProduct.flip q)

private def momentMap (p q : R3) : V →ₗ[ℝ] R3 :=
  (crossProduct p).comp (LinearMap.fst ℝ R3 R3) + (crossProduct q).comp (LinearMap.snd ℝ R3 R3)

/-- The inverse metric endomorphism `I + t K K*` on ambient vectors. -/
def inverseOperator (p q : R3) (t : ℝ) : V →ₗ[ℝ] V :=
  LinearMap.id + t • (action p q).comp (momentMap p q)

theorem inverseOperator_apply (p q : R3) (t : ℝ) (X : V) :
    inverseOperator p q t X = X + t • K p q (moment p q X) := rfl

private theorem prod_comm (X Y : V) : gprod X Y = gprod Y X := by
  simp only [gprod, dotProduct_comm X.1 Y.1, dotProduct_comm X.2 Y.2]

private theorem self_nonneg (X : R3) : 0 ≤ X ⬝ᵥ X :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (X i)

private theorem prod_pos {X : V} (h : X ≠ 0) : 0 < gprod X X := by
  change 0 < X.1 ⬝ᵥ X.1 + X.2 ⬝ᵥ X.2
  by_contra! hle
  apply h
  exact Prod.ext (dotProduct_self_eq_zero.mp (by linarith [self_nonneg X.1, self_nonneg X.2]))
    (dotProduct_self_eq_zero.mp (by linarith [self_nonneg X.1, self_nonneg X.2]))

theorem inverseOperator_pair (p q : R3) (t : ℝ) (X Y : V) :
    gprod (inverseOperator p q t X) Y = gprod X Y + t * (moment p q X ⬝ᵥ moment p q Y) := by
  rw [inverseOperator_apply]
  have h : gprod (K p q (moment p q X)) Y = moment p q X ⬝ᵥ moment p q Y := by
    rw [prod_comm, gprod_K_eq_moment, dotProduct_comm]
  unfold gprod at h ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_dotProduct,
    smul_dotProduct, smul_eq_mul]
  linarith [congrArg (fun r : ℝ => t * r) h]

theorem inverseOperator_pos (p q : R3) {t : ℝ} (ht : 0 ≤ t) {X : V} (hX : X ≠ 0) :
    0 < gprod (inverseOperator p q t X) X := by
  rw [inverseOperator_pair]
  exact add_pos_of_pos_of_nonneg (prod_pos hX) (mul_nonneg ht (self_nonneg _))

/-- The ambient inverse metric endomorphism is invertible also at `t=0`. -/
noncomputable def inverseEquiv (p q : R3) (t : ℝ) (ht : 0 ≤ t) : V ≃ₗ[ℝ] V :=
  let A := inverseOperator p q t
  have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro X hX
    by_contra hn
    have hpos := inverseOperator_pos p q ht hn
    change 0 < gprod (A X) X at hpos
    simp [hX, gprod] at hpos))
  LinearEquiv.ofBijective A ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The Cheeger operator `C_t = (I + t K K*)⁻¹`. -/
noncomputable def operator (p q : R3) (t : ℝ) (ht : 0 ≤ t) : V ≃ₗ[ℝ] V :=
  (inverseEquiv p q t ht).symm

theorem inverse_operator (p q : R3) (t : ℝ) (ht : 0 ≤ t) (X : V) :
    inverseOperator p q t (operator p q t ht X) = X :=
  (inverseEquiv p q t ht).apply_symm_apply X

theorem operator_preserves_tangent (p q : R3) (t : ℝ) (ht : 0 ≤ t) (X : V)
    (hp : X.1 ⬝ᵥ p = 0) (hq : X.2 ⬝ᵥ q = 0) :
    (operator p q t ht X).1 ⬝ᵥ p = 0 ∧ (operator p q t ht X).2 ⬝ᵥ q = 0 := by
  have h := inverse_operator p q t ht X
  rw [inverseOperator_apply] at h
  have h₁ := congrArg (fun Z : V => Z.1 ⬝ᵥ p) h
  have h₂ := congrArg (fun Z : V => Z.2 ⬝ᵥ q) h
  simpa [K, add_dotProduct, smul_dotProduct, cross_dot_right, hp, hq] using And.intro h₁ h₂

/-- Twice the paper’s background pairing `g_t`. -/
noncomputable def pairing (p q : R3) (t : ℝ) (ht : 0 ≤ t) (X Y : V) : ℝ :=
  gprod (operator p q t ht X) Y

theorem pairing_pos (p q : R3) (t : ℝ) (ht : 0 ≤ t) {X : V} (hn : X ≠ 0) :
    0 < pairing p q t ht X X := by
  have hc : operator p q t ht X ≠ 0 := fun h => hn ((operator p q t ht).map_eq_zero_iff.mp h)
  have h := inverseOperator_pos p q ht hc
  rwa [inverse_operator, prod_comm] at h

theorem pairing_zero (p q : R3) (X Y : V) : pairing p q 0 le_rfl X Y = gprod X Y := by
  have h := inverse_operator p q 0 le_rfl X
  rw [inverseOperator_apply, zero_smul, add_zero] at h
  exact congrArg (fun Z => gprod Z Y) h

/-- The lift in the product with Lie algebra metric `Q/t`. -/
noncomputable def lift (p q : R3) (t : ℝ) (ht : 0 ≤ t) (X : V) : V × R3 :=
  let v := operator p q t ht X
  (v, -t • moment p q v)

theorem lift_projects (p q : R3) (t : ℝ) (ht : 0 ≤ t) (X : V) :
    (lift p q t ht X).1 - K p q (lift p q t ht X).2 = X := by
  change _ - action p q (-t • _) = _
  rw [map_smul, neg_smul, sub_neg_eq_add]
  exact inverse_operator p q t ht X

theorem lift_horizontal (p q : R3) {t : ℝ} (ht : 0 < t) (X : V) (ω : R3) :
    gprod (lift p q t ht.le X).1 (K p q ω) + (lift p q t ht.le X).2 ⬝ᵥ ω / t = 0 := by
  simp only [lift, gprod_K_eq_moment, smul_dotProduct, smul_eq_mul]
  field_simp
  ring

theorem lift_pair (p q : R3) {t : ℝ} (ht : 0 < t) (X Y : V) :
    gprod (lift p q t ht.le X).1 (lift p q t ht.le Y).1 +
      (lift p q t ht.le X).2 ⬝ᵥ (lift p q t ht.le Y).2 / t = pairing p q t ht.le X Y := by
  let U := operator p q t ht.le X
  let W := operator p q t ht.le Y
  have h := inverseOperator_pair p q t W U
  rw [show inverseOperator p q t W = Y from inverse_operator .., prod_comm Y U, prod_comm W U,
    dotProduct_comm (moment p q W) (moment p q U)] at h
  change gprod U W + (-t • moment p q U) ⬝ᵥ (-t • moment p q W) / t = gprod U Y
  rw [h, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

theorem pairing_symm (p q : R3) (t : ℝ) (ht : 0 ≤ t) (X Y : V) :
    pairing p q t ht X Y = pairing p q t ht Y X := by
  let U := operator p q t ht X
  let W := operator p q t ht Y
  have hx := inverseOperator_pair p q t U W
  have hy := inverseOperator_pair p q t W U
  rw [show inverseOperator p q t U = X from inverse_operator .., prod_comm X W] at hx
  rw [show inverseOperator p q t W = Y from inverse_operator .., prod_comm Y U, prod_comm W U,
    dotProduct_comm (moment p q W) (moment p q U)] at hy
  exact hy.trans hx.symm

/-- An ambient extension of the Cheeger operator in the base point and the real parameter.
Smoothness is asserted at the invertible parameters. -/
noncomputable def ambientOperator (z : V × ℝ) : V →L[ℝ] V :=
  (inverseOperator z.1.1 z.1.2 z.2).toContinuousLinearMap.inverse

theorem ambientOperator_apply {p q : R3} {t : ℝ} (ht : 0 ≤ t) (X : V) :
    ambientOperator ((p,q),t) X = operator p q t ht X := by
  let e := (inverseEquiv p q t ht).toContinuousLinearEquiv
  change (e : V →L[ℝ] V).inverse X = _
  rw [ContinuousLinearMap.inverse_equiv]
  rfl

open scoped ContDiff

theorem smooth_cross : ContDiff ℝ ∞ (fun z : R3 × R3 => z.1 ⨯₃ z.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [cross_apply] <;> fun_prop

theorem smooth_ambientOperator {p q : R3} {t : ℝ} (ht : 0 ≤ t) :
    ContDiffAt ℝ ∞ ambientOperator ((p,q),t) := by
  have hs : ContDiff ℝ ∞ (fun z : V × ℝ => (inverseOperator z.1.1 z.1.2 z.2).toContinuousLinearMap) := by
    apply contDiff_clm_apply_iff.mpr
    intro X
    change ContDiff ℝ ∞ (fun z : V × ℝ => X + z.2 • K z.1.1 z.1.2 (moment z.1.1 z.1.2 X))
    have hP : ContDiff ℝ ∞ (fun z : V × ℝ => z.1.1) := by fun_prop
    have hQ : ContDiff ℝ ∞ (fun z : V × ℝ => z.1.2) := by fun_prop
    have hm : ContDiff ℝ ∞ (fun z : V × ℝ => moment z.1.1 z.1.2 X) :=
      (smooth_cross.comp (hP.prodMk (contDiff_const (c := X.1)))).add
        (smooth_cross.comp (hQ.prodMk (contDiff_const (c := X.2))))
    exact contDiff_const.add (contDiff_snd.smul
      ((smooth_cross.comp (hm.prodMk hP)).prodMk (smooth_cross.comp (hm.prodMk hQ))))
  let e := (inverseEquiv p q t ht).toContinuousLinearEquiv
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (inverseOperator p q t).toContinuousLinearMap :=
    contDiffAt_map_inverse e
  exact hi.comp ((p,q),t) hs.contDiffAt

open Filter Set Topology

/-- All ambient derivatives of the background operator converge uniformly on compact
base sets as the deformation parameter tends to zero. Evaluating the joint derivative
on directions `(v,0)` gives the spatial derivatives used in §1. -/
theorem uniform_operator_jets (j : ℕ) (S : Set V) (hS : IsCompact S) :
    TendstoUniformlyOn (fun (t : ℝ) (p : V) => iteratedFDeriv ℝ j ambientOperator (p,t))
      (fun p => iteratedFDeriv ℝ j ambientOperator (p,0)) (𝓝 0) S := by
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS,
    tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro p _
  let F := iteratedFDeriv ℝ j ambientOperator
  have hF : ContinuousAt F (p,0) :=
    (smooth_ambientOperator (p := p.1) (q := p.2) (t := 0) le_rfl).continuousAt_iteratedFDeriv (by simp)
  have h₁ : ContinuousAt (fun z : ℝ × V => F (z.2,0)) (0,p) :=
    hF.comp (f := fun z : ℝ × V => (z.2,(0 : ℝ))) (continuousAt_snd.prodMk continuousAt_const)
  have h₂ : ContinuousAt (fun z : ℝ × V => F (z.2,z.1)) (0,p) :=
    hF.comp (f := fun z : ℝ × V => (z.2,z.1)) (continuousAt_snd.prodMk continuousAt_fst)
  exact ((h₁.prodMk h₂).tendsto.mono_right (nhds_le_uniformity _)).mono_left (by
    rw [nhds_prod_eq]
    exact Filter.prod_mono le_rfl nhdsWithin_le_nhds)

end LocalHopf.Cheeger
