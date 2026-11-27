import LocalHopf.ChartConvergence
import LocalHopf.ChartRegularity
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Local smooth evaluation of the intrinsic family on ambient frame data.
The readout differentiates the chart after radial retraction to the spheres. -/
namespace LocalHopf.SphereProduct.JetChart
open Filter Set Metric Matrix Real
open scoped Topology ContDiff Manifold
noncomputable section

private theorem chart_around (p : Base) : ∃ r s : E3 ≃ₗᵢ[ℝ] E3, p ∈ (chart r s).source := by
  let e := equatorPoint 0
  have one (q : Sphere) : ∃ r : E3 ≃ₗᵢ[ℝ] E3, sphereAction r.symm q ∈ LongitudeHeight.source := by
    let r := (ℝ ∙ (e.val-q.val))ᗮ.reflection
    have eq : r e.val = q.val := Submodule.reflection_sub ((mem_sphere_zero_iff_norm.mp e.property).trans
      (mem_sphere_zero_iff_norm.mp q.property).symm)
    have same : sphereAction r.symm q = e := Subtype.ext (r.symm_apply_eq.mpr eq.symm)
    refine ⟨r,?_⟩
    rw [same]
    change 0 < cos 0
    simp
  obtain ⟨r,hr⟩ := one p.1
  obtain ⟨s,hs⟩ := one p.2
  exact ⟨r,s,⟨⟨⟨trivial,hr⟩,trivial,hs⟩,trivial⟩⟩

private def readout (r s : E3 ≃ₗᵢ[ℝ] E3) := (chart r s) ∘ ambientRetract

private theorem readout_smooth (r s : E3 ≃ₗᵢ[ℝ] E3) {p : Base} (hp : p ∈ (chart r s).source) :
    ContDiffAt ℝ ∞ (readout r s) (ambientPoint p) := by
  exact ((chart_smooth r s hp).comp_of_eq (ambientRetract_smooth p) (ambientRetract_point p)).contDiffAt

private theorem readout_vector (r s : E3 ≃ₗᵢ[ℝ] E3) {p : Base} (hp : p ∈ (chart r s).source)
    (X : Tangent p) : field r s (fderiv ℝ (readout r s) (ambientPoint p) (ambientVelocityL p X)) p = X := by
  let e := chart r s
  let F := ambientPoint ∘ e.symm
  let y := e p
  have hy := e.map_source hp
  have point : e.symm y=p := e.left_inv hp
  have H : ContDiffAt ℝ ∞ F y := (ambientPoint_smooth.contMDiffAt.comp y (inv_smooth r s hy)).contDiffAt
  have bg : F y=ambientPoint p := congrArg ambientPoint point
  have left : readout r s ∘ F =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact (congrArg e (ambientRetract_point (e.symm z))).trans (e.right_inv hz)
  have df := (readout_smooth r s hp).differentiableAt (by simp)
  rw [←bg] at df
  have chain := fderiv_comp y df (H.differentiableAt (by simp))
  rw [left.fderiv_eq, fderiv_id] at chain
  obtain ⟨L,hL⟩ := field_equiv r s hp
  obtain ⟨a,rfl⟩ := L.surjective X
  rw [hL a,ambient_field r s hp]
  have lin := congrArg (fun l : Params →L[ℝ] Params => l a) chain.symm
  change fderiv ℝ (readout r s) (F y) (fderiv ℝ F y a) = a at lin
  rw [bg] at lin
  rw [lin]

abbrev AmbientPairData := Cheeger.V × Cheeger.V × Cheeger.V

/-- An actual base point and two tangent velocities, expressed in a fixed vector space. -/
def frameData (w : TangentPair) : AmbientPairData :=
  (ambientPoint w.point,ambientVelocityL w.point w.first,ambientVelocityL w.point w.second)

private def evaluation (r s : E3 ≃ₗᵢ[ℝ] E3) (A : Fin 4 → AmbientTensor)
    (base : Module.Basis (Fin 4) ℝ Params) (q : AmbientPairData × ℝ) :=
  let y := readout r s q.1.1
  let L := fderiv ℝ (readout r s) q.1.1
  tensorNumerator r s A base y (L q.1.2.1) (L q.1.2.2) q.2

private theorem gram_unit (r s : E3 ≃ₗᵢ[ℝ] E3) (base : Module.Basis (Fin 4) ℝ Params)
    {A : Fin 4 → AmbientTensor} {h : ℝ} {g : SmoothMetric} (hg : Realizes g h A)
    {p : Base} (hp : p ∈ (chart r s).source) :
    IsUnit (Matrix.det (fun i j => cubicValue h (fun k => tensor r s (A k) (base i) (base j) ((chart r s) p)))) := by
  obtain ⟨L,hL⟩ := field_equiv r s hp
  let B : Frame p := base.map L.toLinearEquiv
  have e (i) : B i = field r s (base i) p := by simpa [B] using hL (base i)
  have mat : gramMatrix g B = fun i j => cubicValue h (fun k => tensor r s (A k) (base i) (base j) ((chart r s) p)) := by
    ext i j
    simp only [tensor,Function.comp_apply,(chart r s).left_inv hp]
    exact (hg p (B i) (B j)).trans (by simp only [e,ambientPair])
  rw [←mat]
  exact gram_isUnit _ _

/-- Around each genuine pair, a single smooth function of the ambient data
evaluates all nearby intrinsic curvature numerators throughout the metric window. -/
theorem local_numerator {A : Fin 4 → AmbientTensor} {s₀ : ℝ}
    (window : ∀ᶠ h in 𝓝 s₀, ∃ g : SmoothMetric, Realizes g h A) (w₀ : TangentPair) :
    ∃ F : AmbientPairData × ℝ → ℝ, ContDiffAt ℝ ∞ F (frameData w₀,s₀) ∧
      ∀ᶠ z in 𝓝 (frameData w₀,s₀), ∀ w : TangentPair, frameData w=z.1 → w.numerator A z.2 = F z := by
  obtain ⟨r,s,hp⟩ := chart_around w₀.point
  have dim : Module.finrank ℝ Params = 4 := by simp [Params,Module.finrank_prod]
  let base := (Module.finBasis ℝ Params).reindex (finCongr dim)
  let e := chart r s
  let o := (frameData w₀,s₀)
  let B := fun z : AmbientPairData × ℝ => z.1.1
  let u := fun z : AmbientPairData × ℝ => z.1.2.1
  let v := fun z : AmbientPairData × ℝ => z.1.2.2
  have cb : ContDiff ℝ ∞ B := by unfold B; fun_prop
  have i : readout r s (B o) = e w₀.point := congrArg e (ambientRetract_point _)
  have y := (readout_smooth r s hp).comp (f := B) o cb.contDiffAt
  have d := ((readout_smooth r s hp).fderiv_right (by simp : ∞+1 ≤ ∞)).comp (f := B) o cb.contDiffAt
  obtain ⟨g,hg⟩ := window.self_of_nhds
  refine ⟨evaluation r s A base,?_,?_⟩
  · apply tensorNumerator_smooth r s A base (y := readout r s ∘ B) (a := fun z => fderiv ℝ (readout r s) (B z) (u z))
      (b := fun z => fderiv ℝ (readout r s) (B z) (v z)) (h := Prod.snd)
    · change readout r s (B o) ∈ e.target
      rw [i]
      exact e.map_source hp
    · exact y
    · exact d.clm_apply (by unfold u; fun_prop)
    · exact d.clm_apply (by unfold v; fun_prop)
    · exact contDiffAt_snd
    · change IsUnit (Matrix.det (fun i j => cubicValue s₀ (fun k => tensor r s (A k) (base i) (base j) (readout r s (B o)))))
      rw [i]
      exact gram_unit r s base hg hp
  · have ok : ∀ᶠ z in 𝓝 o, ambientRetract (B z) ∈ e.source := by
      have cont := (ambientRetract_smooth w₀.point).continuousAt.comp (x := o) cb.continuous.continuousAt
      exact cont.preimage_mem_nhds (e.open_source.mem_nhds (show ambientRetract (B o) ∈ e.source by rwa [show B o = ambientPoint w₀.point from rfl,ambientRetract_point]))
    filter_upwards [ok, (continuous_snd.continuousAt (x := o)).preimage_mem_nhds window] with z hz gh
    intro w eq
    obtain ⟨g,hg⟩ := gh
    rcases z with ⟨data,h⟩
    change frameData w = data at eq
    subst data
    change ambientRetract (ambientPoint w.point) ∈ e.source at hz
    rw [ambientRetract_point] at hz
    let L := fderiv ℝ (readout r s) (ambientPoint w.point)
    let a := L (ambientVelocityL w.point w.first)
    let b := L (ambientVelocityL w.point w.second)
    have eqv := tensorNumerator_realizes r s hg (e.map_source hz) base a b
    rw [e.left_inv hz] at eqv
    dsimp only at eqv
    rw [show field r s a w.point = w.first from readout_vector r s hz w.first,
      show field r s b w.point = w.second from readout_vector r s hz w.second] at eqv
    rw [w.numerator_eq hg]
    change _ = tensorNumerator r s A base (e (ambientRetract (ambientPoint w.point))) a b h
    rw [ambientRetract_point]
    exact eqv


theorem moving_numerator_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {w : E → TangentPair} {h : E → ℝ} {A : Fin 4 → AmbientTensor}
    (window : ∀ᶠ s in 𝓝 (h x), ∃ g : SmoothMetric, Realizes g s A)
    (hw : ContDiffAt ℝ ∞ (frameData ∘ w) x) (hh : ContDiffAt ℝ ∞ h x) :
    ContDiffAt ℝ ∞ (fun z => (w z).numerator A (h z)) x := by
  obtain ⟨F,reg,eq⟩ := local_numerator window (w x)
  let k := fun z => (frameData (w z),h z)
  have sm : ContDiffAt ℝ ∞ k x := hw.prodMk hh
  apply (reg.comp (f := k) x sm).congr_of_eventuallyEq
  filter_upwards [sm.continuousAt.preimage_mem_nhds eq] with z hz using hz (w z) rfl

theorem moving_numerator_continuous {E : Type*} [TopologicalSpace E]
    {x : E} {w : E → TangentPair} {h : E → ℝ} {A : Fin 4 → AmbientTensor}
    (window : ∀ᶠ s in 𝓝 (h x), ∃ g : SmoothMetric, Realizes g s A)
    (hw : ContinuousAt (frameData ∘ w) x) (hh : ContinuousAt h x) :
    ContinuousAt (fun z => (w z).numerator A (h z)) x := by
  obtain ⟨F,reg,eq⟩ := local_numerator window (w x)
  let k := fun z => (frameData (w z),h z)
  have sm : ContinuousAt k x := hw.prodMk hh
  apply (reg.continuousAt.comp (f := k) sm).congr_of_eventuallyEq
  filter_upwards [sm.preimage_mem_nhds eq] with z hz using hz (w z) rfl


end
end LocalHopf.SphereProduct.JetChart
