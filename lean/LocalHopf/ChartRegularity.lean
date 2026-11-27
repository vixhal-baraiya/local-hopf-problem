import LocalHopf.ChartExpansion
import Mathlib.Analysis.Matrix.Normed

/-! Joint regularity of the intrinsic coordinate curvature expression as the
base point, spanning vectors and metric parameter vary together. -/
namespace LocalHopf.SphereProduct.JetChart
open Matrix Filter Set
open scoped ContDiff Topology Manifold Matrix.Norms.Operator
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem variable_D {C : E → Params → ℝ} {v : E → Params} {x : E} {y : Params}
    (hC : ContDiffAt ℝ ∞ (Function.uncurry C) (x,y)) (hv : ContDiffAt ℝ ∞ v x) :
    ContDiffAt ℝ ∞ (fun w : E × Params => D (v w.1) (C w.1) w.2) (x,y) := by
  have df := hC.fderiv_right (by simp : ∞+1 ≤ ∞)
  have vec : ContDiffAt ℝ ∞ (fun w : E × Params => ((0:E),v w.1)) (x,y) :=
    contDiffAt_const.prodMk (hv.comp _ contDiffAt_fst)
  apply (df.clm_apply vec).congr_of_eventuallyEq
  filter_upwards [(hC.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)] with w hw
  have g : HasFDerivAt (fun z : Params => (w.1,z)) (ContinuousLinearMap.inr ℝ E Params) w.2 :=
    (hasFDerivAt_const w.1 w.2).prodMk (hasFDerivAt_id w.2)
  exact congrArg (fun L : Params →L[ℝ] ℝ => L (v w.1)) (((hw.differentiableAt (by simp)).hasFDerivAt.comp w.2 g).fderiv)

private theorem tensor_joint (r s : E3 ≃ₗᵢ[ℝ] E3) (A : AmbientTensor)
    {a b : E → Params} {x : E} {y : Params} (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x)
    (hy : y ∈ (chart r s).target) :
    ContDiffAt ℝ ∞ (fun w : E × Params => tensor r s A (a w.1) (b w.1) w.2) (x,y) := by
  let e := chart r s
  have f : ContDiffAt ℝ ∞ (ambientPoint ∘ e.symm) y :=
    (ambientPoint_smooth.contMDiffAt.comp y (inv_smooth r s hy)).contDiffAt
  have hL := (f.fderiv_right (by simp : ∞+1 ≤ ∞)).comp (x,y) contDiffAt_snd
  have T : ContDiffAt ℝ ∞ (fun q => A.form (e.symm q)) y :=
    (A.smooth.contMDiffAt.comp y (inv_smooth r s hy)).contDiffAt
  have k := ((T.comp (x,y) contDiffAt_snd).clm_apply (hL.clm_apply (ha.comp (x,y) contDiffAt_fst))).clm_apply
    (hL.clm_apply (hb.comp (x,y) contDiffAt_fst))
  apply k.congr_of_eventuallyEq
  filter_upwards [(e.open_target.preimage continuous_snd).mem_nhds (show (x,y) ∈ _ from hy)] with w hw
  change A.form (e.symm w.2) (ambientVelocityL _ (field r s (a w.1) _)) (ambientVelocityL _ (field r s (b w.1) _)) = _
  rw [ambient_field r s (e.map_target hw),ambient_field r s (e.map_target hw),e.right_inv hw]
  rfl

private theorem symbol_joint (r s : E3 ≃ₗᵢ[ℝ] E3) (A : AmbientTensor)
    {a b d : E → Params} {x : E} {y : Params} (ha : ContDiffAt ℝ ∞ a x)
    (hb : ContDiffAt ℝ ∞ b x) (hd : ContDiffAt ℝ ∞ d x) (hy : y ∈ (chart r s).target) :
    ContDiffAt ℝ ∞ (fun w : E × Params => symbol (tensor r s A) (a w.1) (b w.1) (d w.1) w.2) (x,y) := by
  exact (((variable_D (C := fun z => tensor r s A (b z) (d z)) (tensor_joint r s A hb hd hy) ha).add
    (variable_D (C := fun z => tensor r s A (d z) (a z)) (tensor_joint r s A hd ha hy) hb)).sub
    (variable_D (C := fun z => tensor r s A (a z) (b z)) (tensor_joint r s A ha hb hy) hd)).div_const 2

private theorem second_joint (r s : E3 ≃ₗᵢ[ℝ] E3) (A : AmbientTensor)
    {a b : E → Params} {x : E} {y : Params} (ha : ContDiffAt ℝ ∞ a x)
    (hb : ContDiffAt ℝ ∞ b x) (hy : y ∈ (chart r s).target) :
    ContDiffAt ℝ ∞ (fun w : E × Params => second (tensor r s A) (a w.1) (b w.1) w.2) (x,y) := by
  let T := tensor r s A
  let U := fun z => D (b z) (T (b z) (a z))
  let V := fun z => D (a z) (T (b z) (b z))
  let W := fun z => D (b z) (T (a z) (a z))
  have u : ContDiffAt ℝ ∞ (Function.uncurry U) (x,y) := variable_D (C := fun z => T (b z) (a z)) (tensor_joint r s A hb ha hy) hb
  have v : ContDiffAt ℝ ∞ (Function.uncurry V) (x,y) := variable_D (C := fun z => T (b z) (b z)) (tensor_joint r s A hb hb hy) ha
  have w : ContDiffAt ℝ ∞ (Function.uncurry W) (x,y) := variable_D (C := fun z => T (a z) (a z)) (tensor_joint r s A ha ha hy) hb
  exact (variable_D (C := fun z y => U z y - V z y/2) (u.sub (v.div_const 2)) ha).sub
    (variable_D (C := fun z y => W z y/2) (w.div_const 2) hb)

private theorem smooth_cubic {s : E → ℝ} {f : Fin 4 → E → ℝ} {x : E}
    (hs : ContDiffAt ℝ ∞ s x) (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x) :
    ContDiffAt ℝ ∞ (fun z => cubicValue (s z) (fun i => f i z)) x :=
  (((hf 0).add (hs.mul (hf 1))).add ((hs.pow 2).mul (hf 2))).add ((hs.pow 3).mul (hf 3))

/-- Joint smoothness allows the minimizing plane and its base point to move.
The only nondegeneracy condition is invertibility of the actual Gram matrix. -/
theorem tensorNumerator_smooth (r s : E3 ≃ₗᵢ[ℝ] E3) (A : Fin 4 → AmbientTensor)
    (base : Module.Basis (Fin 4) ℝ Params) {y a b : E → Params} {h : E → ℝ} {x : E}
    (hy : y x ∈ (chart r s).target) (Y : ContDiffAt ℝ ∞ y x) (U : ContDiffAt ℝ ∞ a x)
    (V : ContDiffAt ℝ ∞ b x) (H : ContDiffAt ℝ ∞ h x)
    (det : IsUnit (Matrix.det (fun i j => cubicValue (h x) (fun k => tensor r s (A k) (base i) (base j) (y x))))) :
    ContDiffAt ℝ ∞ (fun z => tensorNumerator r s A base (y z) (a z) (b z) (h z)) x := by
  let G (z : E) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => cubicValue (h z) (fun k => tensor r s (A k) (base i) (base j) (y z))
  have gram (i j : Fin 4) : ContDiffAt ℝ ∞ (fun z => G z i j) x :=
    smooth_cubic H (fun k => (tensor_smooth r s (A k) (base i) (base j) hy).comp x Y)
  have Gs : ContDiffAt ℝ ∞ G x := by
    have eq : G = fun z => ∑ i, ∑ j, G z i j • Matrix.single i j (1:ℝ) := by
      funext z; ext i j
      simp [Matrix.sum_apply, Matrix.single_apply,ite_and,Finset.sum_ite_irrel]
    rw [eq]
    exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => (gram i j).smul contDiffAt_const))
  have unit : IsUnit (G x) := (Matrix.isUnit_iff_isUnit_det (G x)).mpr det
  have inv : ContDiffAt ℝ ∞ Ring.inverse (G x) := unit.unit_spec ▸ contDiffAt_ringInverse ℝ unit.unit
  have GI (i j : Fin 4) : ContDiffAt ℝ ∞ (fun z => (G z)⁻¹ i j) x := by
    let l : Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    have eq : (fun z => (G z)⁻¹ i j) = l ∘ Ring.inverse ∘ G := by
      funext z
      rw [nonsing_inv_eq_ringInverse]
      rfl
    rw [eq]
    exact l.contDiff.contDiffAt.comp x (inv.comp x Gs)
  let J (u w : E → Params) (i : Fin 4) (z : E) :=
    cubicValue (h z) (fun k => symbol (tensor r s (A k)) (u z) (w z) (base i) (y z))
  have js {u w : E → Params} (u' : ContDiffAt ℝ ∞ u x) (w' : ContDiffAt ℝ ∞ w x) (i : Fin 4) :
      ContDiffAt ℝ ∞ (J u w i) x := by
    apply smooth_cubic (f := fun k z => symbol (tensor r s (A k)) (u z) (w z) (base i) (y z)) H
    intro k
    exact (symbol_joint r s (A k) u' w' (contDiffAt_const (c := base i)) hy).comp (f := fun z => (z,y z)) x (contDiffAt_id.prodMk Y)
  have S := smooth_cubic H (fun k => (second_joint r s (A k) U V hy).comp (f := fun z => (z,y z)) x (contDiffAt_id.prodMk Y))
  have pair {u v w d : E → Params} (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x)
      (hw : ContDiffAt ℝ ∞ w x) (hd : ContDiffAt ℝ ∞ d x) :
      ContDiffAt ℝ ∞ (fun z => (fun i => J u v i z) ⬝ᵥ (G z)⁻¹ *ᵥ fun i => J w d i z) x := by
    simp only [dotProduct,Matrix.mulVec]
    exact ContDiffAt.sum (fun i _ => (js hu hv i).mul (ContDiffAt.sum (fun j _ => (GI i j).mul (js hw hd j))))
  exact (S.add (pair U V U V)).sub (pair U U V V)


end
end LocalHopf.SphereProduct.JetChart
