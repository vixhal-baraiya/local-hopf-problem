import LocalHopf.CurvatureMatrix
import LocalHopf.PerturbationTensors

/-! # Perturbation expansion of the actual curvature numerator

At a fixed frame the scalar differential expressions are linear in the metric.
Only inversion of the Gram matrix introduces higher perturbation orders.
-/
namespace LocalHopf.SphereProduct
open Bundle FiberBundle Filter Matrix
open scoped Manifold ContDiff Topology
noncomputable section

/-- Evaluate four Taylor coefficients (without factorials). -/
def cubicValue {E : Type*} [AddCommGroup E] [Module ℝ E] (s : ℝ) (a : Fin 4 → E) : E :=
  a 0 + s • a 1 + s^2 • a 2 + s^3 • a 3

theorem directional_add {f k : Base → ℝ} {p : Base} (U : Field)
    (hf : MDifferentiableAt productModel 𝓘(ℝ,ℝ) f p) (hk : MDifferentiableAt productModel 𝓘(ℝ,ℝ) k p) :
    directional U (f+k) p = directional U f p + directional U k p := by
  simp [directional, mvfderiv_add hf hk]

theorem directional_mul_const {f : Base → ℝ} {p : Base} (U : Field) (c : ℝ)
    (hf : MDifferentiableAt productModel 𝓘(ℝ,ℝ) f p) :
    directional U (c • f) p = c * directional U f p := by
  change mvfderiv productModel ((fun _ => c) * f) p _ = _
  rw [mvfderiv_mul mdifferentiableAt_const hf, mvfderiv_const]
  simp [directional]

private theorem directional_cubic {p : Base} (s : ℝ) (U : Field) (f : Fin 4 → Base → ℝ)
    (hf : ∀ i, MDifferentiableAt productModel 𝓘(ℝ,ℝ) (f i) p) :
    directional U (cubicValue s f) p = cubicValue s (fun i => directional U (f i) p) := by
  have hm (c : ℝ) (i : Fin 4) : MDifferentiableAt productModel 𝓘(ℝ,ℝ) (c • f i) p :=
    (mdifferentiableAt_const (c := c)).mul (hf i)
  unfold cubicValue
  rw [directional_add U (((hf 0).add (hm s 1)).add (hm (s^2) 2)) (hm (s^3) 3),
    directional_add U ((hf 0).add (hm s 1)) (hm (s^2) 2), directional_add U (hf 0) (hm s 1),
    directional_mul_const U _ (hf 1), directional_mul_const U _ (hf 2), directional_mul_const U _ (hf 3)]
  rfl

/-- A local scalar expansion with enough regularity to differentiate spatially. -/
private structure Expansion (s : ℝ) (p : Base) (f : Base → ℝ) (a : Fin 4 → Base → ℝ) : Prop where
  eqNear : f =ᶠ[𝓝 p] cubicValue s a
  smooth : ∀ i, ∀ᶠ q in 𝓝 p, ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ (a i) q

private theorem Expansion.dir {s : ℝ} {p : Base} {f a} (h : Expansion s p f a)
    (U : Field) (hU : ∀ᶠ q in 𝓝 p, FieldSmoothAt U q) :
    Expansion s p (directional U f) (fun i => directional U (a i)) where
  eqNear := by
    have he := h.eqNear.eventuallyEq_nhds
    filter_upwards [he, Filter.eventually_all.mpr h.smooth] with q hq ha
    exact (directional_congr hq).trans (directional_cubic s U a (fun i => (ha i).mdifferentiableAt (by simp)))
  smooth i := by
    filter_upwards [hU,h.smooth i] with q hu ha
    exact directional_smoothAt hu ha

private theorem Expansion.lin {s : ℝ} {p : Base} {f g a b} (hf : Expansion s p f a)
    (hg : Expansion s p g b) (c d : ℝ) :
    Expansion s p (fun q => c*f q + d*g q) (fun i q => c*a i q + d*b i q) where
  eqNear := by
    filter_upwards [hf.eqNear,hg.eqNear] with q h₁ h₂
    rw [h₁,h₂]
    simp [cubicValue]
    ring
  smooth i := by
    filter_upwards [hf.smooth i,hg.smooth i] with q h₁ h₂
    exact ((contMDiffAt_const (c := c)).mul h₁).add ((contMDiffAt_const (c := d)).mul h₂)

def ambientPair (A : AmbientTensor) (U V : Field) (p : Base) : ℝ :=
  A.form p (ambientVelocityL p (U p)) (ambientVelocityL p (V p))

theorem ambientPair_smooth (A : AmbientTensor) {p : Base} {U V : Field}
    (hU : FieldSmoothAt U p) (hV : FieldSmoothAt V p) :
    ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ (ambientPair A U V) p := by
  have hv (W : Field) (hw : FieldSmoothAt W p) :
      ContMDiffAt productModel 𝓘(ℝ,Cheeger.V) ∞ (fun q => ambientVelocityL q (W q)) p := by
    let sectionW : Base → TangentBundle productModel Base := fun q => ⟨q,W q⟩
    have hs : ContMDiffAt productModel productModel.tangent ∞ sectionW p := hw
    exact (ambientVelocity_smooth (sectionW p)).comp p hs
  exact ((A.smooth p).clm_apply (hv U hU)).clm_apply (hv V hV)

/-- Coefficient of the first-kind Christoffel symbol supplied by an ambient tensor. -/
def ambientGamma (A : AmbientTensor) {p : Base} (X Y Z : Tangent p) : ℝ :=
  let U := extend Coordinates X
  let V := extend Coordinates Y
  let W := extend Coordinates Z
  (directional U (ambientPair A V W) p + directional V (ambientPair A U W) p -
    directional W (ambientPair A U V) p)/2

/-- Coefficient of the spatial second-derivative term supplied by an ambient tensor. -/
def ambientSecond (A : AmbientTensor) {p : Base} (X Y : Tangent p) : ℝ :=
  let U := extend Coordinates X
  let V := extend Coordinates Y
  directional U (fun q => directional V (ambientPair A V U) q - directional U (ambientPair A V V) q/2) p -
    directional V (fun q => directional V (ambientPair A U U) q/2) p

/-- The scalar parts of the curvature calculation commute with taking each of
the four metric coefficients, including both spatial derivatives. -/
theorem metric_jet_linear (g : SmoothMetric) (s : ℝ) (A : Fin 4 → AmbientTensor)
    (hg : ∀ (q : Base) (x y : Tangent q), g.inner q x y =
      cubicValue s (fun i => A i |>.form q (ambientVelocityL q x) (ambientVelocityL q y)))
    {p : Base} (X Y : Tangent p) :
    (∀ Z, gamma g X Y Z = cubicValue s (fun i => ambientGamma (A i) X Y Z)) ∧
    secondPart g X Y = cubicValue s (fun i => ambientSecond (A i) X Y) := by
  let E (x : Tangent p) := extend (E := Tangent) Coordinates x
  have hs (x y : Tangent p) : Expansion s p (metricPair g (E x) (E y))
      (fun i => ambientPair (A i) (E x) (E y)) := by
    refine ⟨Eventually.of_forall (fun q => hg q _ _), fun i => ?_⟩
    filter_upwards [extend_smooth_near x, extend_smooth_near y] with q hx hy
    exact ambientPair_smooth (A i) hx hy
  have d (x y z : Tangent p) := (hs y z).dir (E x) (extend_smooth_near x)
  constructor
  · intro Z
    have eq₁ := (d X Y Z).eqNear.self_of_nhds
    have eq₂ := (d Y X Z).eqNear.self_of_nhds
    have eq₃ := (d Z X Y).eqNear.self_of_nhds
    unfold gamma ambientGamma
    dsimp only
    change (_ + _ - _)/2 = _
    rw [eq₁, eq₂, eq₃]
    simp [cubicValue, E]
    ring
  · have h₁ := ((d Y Y X).lin (d X Y Y) 1 (-1/2)).dir (E X) (extend_smooth_near X)
    have h₂ := ((d Y X X).lin (d Y X X) 0 (1/2)).dir (E Y) (extend_smooth_near Y)
    have H := (h₁.lin h₂ 1 (-1)).eqNear.self_of_nhds
    simpa [secondPart, ambientSecond, cubicValue, E, sub_eq_add_neg, div_eq_inv_mul] using H

/-- The frame matrices of the perturbing tensors. -/
def ambientGram (A : AmbientTensor) {p : Base} (b : Frame p) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => A.form p (ambientVelocityL p (b i)) (ambientVelocityL p (b j))

/-- Expansion through cubic order with an exact fourth-order remainder. This
applies to each genuine small-parameter metric of §2. The contracted vectors
use the first derivatives of the individual tensors; the linear term uses their
second derivatives. -/
theorem curvature_expansion (s : ℝ) (g : SmoothMetric) (A : Fin 4 → AmbientTensor)
    (hg : ∀ (q : Base) (x y : Tangent q), g.inner q x y =
      cubicValue s (fun i => (A i).form q (ambientVelocityL q x) (ambientVelocityL q y)))
    {p : Base} (b : Frame p) (X Y : Tangent p) (h₀ : IsUnit (ambientGram (A 0) b).det) :
    let Γ (x y : Tangent p) (j : Fin 4) := cubicValue s (fun i => ambientGamma (A i) x y (b j))
    let H := (ambientGram (A 0) b)⁻¹
    let E := ambientGram (A 1) b + s • ambientGram (A 2) b + s^2 • ambientGram (A 3) b
    let B := CurvatureJets.inverseCubic s H E
    let M := (H*E)^4*(gramMatrix g b)⁻¹
    let pair (N : Matrix (Fin 4) (Fin 4) ℝ) := Γ X Y ⬝ᵥ N *ᵥ Γ X Y - Γ X X ⬝ᵥ N *ᵥ Γ Y Y
    curvatureNumerator g p X Y = cubicValue s (fun i => ambientSecond (A i) X Y) + pair B + s^4 * pair M := by
  intro Γ H E B M pair
  have he : gramMatrix g b = ambientGram (A 0) b + s • E := by
    ext i j
    rw [gramMatrix, hg]
    simp [E, ambientGram, cubicValue]
    ring
  have hinv : (gramMatrix g b)⁻¹ = B + s^4 • M := by
    have h := CurvatureJets.inverse_remainder s (ambientGram (A 0) b) H E (gramMatrix g b)⁻¹
      (nonsing_inv_mul _ h₀) (by rw [← he, mul_nonsing_inv _ (gram_isUnit g b)])
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hc := curvature_from_metric_jet g b X Y
  dsimp only at hc
  rw [hc, (metric_jet_linear g s A hg X Y).2, hinv]
  simp_rw [(metric_jet_linear g s A hg _ _).1]
  change _ + Γ X Y ⬝ᵥ (B + s^4 • M) *ᵥ Γ X Y - Γ X X ⬝ᵥ (B + s^4 • M) *ᵥ Γ Y Y = _
  dsimp only [pair]
  simp [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul]
  ring

end
end LocalHopf.SphereProduct
