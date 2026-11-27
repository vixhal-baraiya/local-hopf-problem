import LocalHopf.NormalMinimum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Coefficients and normal equation in a moving chart

The coefficient of order `n` is the full differential in the joint direction
`(0, ζ, 1)` divided by `n!`. The linear equation used to select the minimizing
tilt is exactly stationarity of the quadratic coefficient.
-/
namespace LocalHopf.UniformTube
open Set Filter
open scoped ContDiff Topology
noncomputable section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coeff_eq_differential (F : P × E × ℝ → ℝ) {x : P} (v : E) (n : ℕ)
    (hf : ContDiffAt ℝ n F (x,0,0)) :
    coeff F n x v = iteratedFDeriv ℝ n F (x,0,0) (fun _ => (0,v,1)) / n.factorial := by
  let o := ((x,0,0) : P × E × ℝ)
  let d := ((0,v,1) : P × E × ℝ)
  let L := ContinuousLinearMap.toSpanSingleton ℝ d
  let f (w : P × E × ℝ) := F (o+w)
  have h : ContDiffAt ℝ n f 0 :=
    (show ContDiffAt ℝ n F (o+0) by simpa [o] using hf).comp 0
      (f := fun w : P × E × ℝ => o+w) (by fun_prop)
  obtain ⟨S,hsub,ho,h₀⟩ := mem_nhds_iff.mp (h.eventually (by simp))
  have hL : L 0 ∈ S := by simpa using h₀
  have hopen := ho.preimage L.continuous
  have e := L.iteratedFDerivWithin_comp_right (f := f) (n := n)
    (s := S) (fun y hy => (hsub hy).contDiffWithinAt) ho.uniqueDiffOn hopen.uniqueDiffOn hL (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hopen hL,iteratedFDerivWithin_of_isOpen n ho hL] at e
  have eq : (fun r => ray F ((x,v),r)) = f ∘ L := by
    funext r
    simp [f,L,ray,o,d,ContinuousLinearMap.toSpanSingleton_apply]
  change iteratedDeriv n _ 0 / _ = _
  rw [eq,iteratedDeriv_eq_iteratedFDeriv,e]
  change (iteratedFDeriv ℝ n (fun z => F (o+z)) (L 0) fun _ => L 1) / _ = _
  simp only [iteratedFDeriv_comp_add_left,map_zero,add_zero]
  simp [o,d,L]

/-- The normal component of the Hessian equation `H z̄ = -g`, written
without choosing a normal basis or inverting a coordinate matrix. -/
def NormalEquation (F : P × E × ℝ → ℝ) (x : P) (a : E) : Prop :=
  ∀ v : E, fderiv ℝ (fderiv ℝ F) (x,0,0) (0,a,1) (0,v,0) = 0

/-- Restricting the second differential to an affine line of tilt velocities. -/
theorem quadratic_line (F : P × E × ℝ → ℝ) {x : P}
    (hf : ContDiffAt ℝ 2 F (x,0,0)) (a v : E) (s : ℝ) :
    let H := fderiv ℝ (fderiv ℝ F) (x,0,0)
    let A := ((0,a,1) : P × E × ℝ)
    let D := ((0,v,0) : P × E × ℝ)
    coeff F 2 x (a+s • v) = coeff F 2 x a + s*(H A D) + s^2*(H D D / 2) := by
  intro H A D
  have e : A+s • D = (0,a+s • v,1) := by simp [A,D]
  have symm : H D A = H A D := hf.isSymmSndFDerivAt (by norm_num) D A
  rw [coeff_two_eq_hessian F _ hf,coeff_two_eq_hessian F _ hf]
  change H (0,a+s • v,1) (0,a+s • v,1) / 2 = _
  rw [← e,H.map_add,add_apply,map_add,map_add,H.map_smul,smul_apply,smul_apply,map_smul,map_smul]
  simp only [smul_eq_mul,symm]
  change _ = H A A / 2 + _ + _
  ring

theorem normalEquation_of_minimum (F : P × E × ℝ → ℝ) {x : P}
    (hf : ContDiffAt ℝ 2 F (x,0,0)) {a : E}
    (hm : ∀ z, coeff F 2 x a ≤ coeff F 2 x z) : NormalEquation F x a := by
  intro v
  let H := fderiv ℝ (fderiv ℝ F) (x,0,0)
  let b := H (0,a,1) (0,v,0)
  let c := H (0,v,0) (0,v,0) / 2
  have hmin : IsLocalMin (fun r : ℝ => r*b+r^2*c) 0 := by
    apply Eventually.of_forall
    intro r
    have he := quadratic_line F hf a v r
    have hb := hm (a+r • v)
    change _ = _ + r*b+r^2*c at he
    simp only [zero_mul,zero_pow (by decide : 2 ≠ 0),add_zero]
    linarith
  have h := hmin.hasDerivAt_eq_zero (((hasDerivAt_id' (0:ℝ)).mul_const b).add
    (((hasDerivAt_id' (0:ℝ)).pow 2).mul_const c))
  simpa [b,H] using h

/-- Any computed solution of the normal equations gives the two minimized
coefficients, uniquely. The only positivity needed here is background growth. -/
theorem normalEquation_iff_minimum (F : P × E × ℝ → ℝ) {x : P} {δ lam : ℝ}
    (hf : ContDiffAt ℝ 2 F (x,0,0)) (hδ : 0 < δ) (hlam : 0 < lam) (hflat : F (x,0,0) = 0)
    (h₀ : ∀ z : E, ‖z‖ ≤ δ → lam*‖z‖^2 ≤ F (x,z,0)) (a : E) :
    NormalEquation F x a ↔ ∀ z, coeff F 2 x a ≤ coeff F 2 x z := by
  refine ⟨fun h z => ?_,normalEquation_of_minimum F hf⟩
  have e := quadratic_line F hf a (z-a) 1
  have hd := normal_second_lower F hδ hf hflat h₀ (z-a)
  simp only [one_smul,add_sub_cancel,one_mul,one_pow,h (z-a),add_zero] at e
  have hnon : 0 ≤ 2*lam*‖z-a‖^2 := by positivity
  linarith

end
end LocalHopf.UniformTube
