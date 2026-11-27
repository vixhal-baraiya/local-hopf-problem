import LocalHopf.MetricRealization

/-! # Differentiating the curvature numerator

Lowering the outer covariant derivatives by metric compatibility gives the two
first-kind Christoffel derivatives and the quadratic connection terms. This is
the intrinsic calculation underlying the coordinate formula in `verification/jets.py`.
-/

namespace LocalHopf.SphereProduct

open Bundle FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section

abbrev Field := (p : Base) → Tangent p

abbrev FieldDiffAt (V : Field) (p : Base) :=
  MDifferentiableAt productModel productModel.tangent (fun q => TotalSpace.mk' Coordinates q (V q)) p

/-- Differentiate a vector field along another using the given metric. -/
def nabla (g : SmoothMetric) (U V : Field) : Field :=
  letI : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  fun p => CovariantDerivative.leviCivitaConnection productModel Base V p (U p)

def metricPair (g : SmoothMetric) (U V : Field) (p : Base) : ℝ := g.inner p (U p) (V p)

def directional (U : Field) (f : Base → ℝ) (p : Base) : ℝ := mvfderiv productModel f p (U p)

/-- The first-kind Christoffel symbol on three local vector fields. -/
def firstKind (g : SmoothMetric) (U V W : Field) := metricPair g (nabla g U V) W

theorem firstKind_koszul (g : SmoothMetric) (U V W : Field) (p : Base)
    (hU : FieldDiffAt U p) (hV : FieldDiffAt V p) (hW : FieldDiffAt W p) :
    firstKind g U V W p =
      (directional U (metricPair g V W) p + directional V (metricPair g W U) p -
        directional W (metricPair g U V) p - metricPair g V (VectorField.mlieBracket productModel U W) p -
        metricPair g W (VectorField.mlieBracket productModel V U) p +
        metricPair g U (VectorField.mlieBracket productModel W V) p) / 2 := by
  let : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  exact CovariantDerivative.leviCivitaConnection_apply_inner productModel hU hV hW

private theorem derivative_metricPair (g : SmoothMetric) (U V W : Field) (p : Base)
    (hV : FieldDiffAt V p) (hW : FieldDiffAt W p) :
    directional U (metricPair g V W) p =
      metricPair g (nabla g U V) W p + metricPair g V (nabla g U W) p := by
  let : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.isMetricCompatible_leviCivitaConnection productModel (M := Base)
    ).mvfderiv_inner_eq U hV hW

abbrev FieldSmoothAt (V : Field) (p : Base) :=
  ContMDiffAt productModel productModel.tangent ∞ (fun q => TotalSpace.mk' Coordinates q (V q)) p

private theorem pair_smooth (g : SmoothMetric) {U V : Field} {p : Base}
    (hU : FieldSmoothAt U p) (hV : FieldSmoothAt V p) :
    ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ (metricPair g U V) p := by
  let : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  exact hU.inner_bundle hV

theorem directional_smoothAt {U : Field} {f : Base → ℝ} {p : Base}
    (hU : FieldSmoothAt U p) (hf : ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ f p) :
    ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ (directional U f) p := by
  let w : TangentBundle productModel Base := ⟨p,U p⟩
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ,ℝ)).contMDiffAt.comp p
    ((hf.contMDiffAt_tangentMap (X := w) (m := ∞) (by simp)).comp p hU)

private theorem smooth_bracket {U V : Field} {p : Base}
    (hU : FieldSmoothAt U p) (hV : FieldSmoothAt V p) :
    FieldSmoothAt (VectorField.mlieBracket productModel U V) p :=
  hU.mlieBracket_vectorField hV (by simp)

private theorem smooth_firstKind (g : SmoothMetric) {U V W : Field} {p : Base}
    (hU : ∀ᶠ q in 𝓝 p, FieldSmoothAt U q) (hV : ∀ᶠ q in 𝓝 p, FieldSmoothAt V q)
    (hW : ∀ᶠ q in 𝓝 p, FieldSmoothAt W q) :
    ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ (firstKind g U V W) p := by
  have u := hU.self_of_nhds
  have v := hV.self_of_nhds
  have w := hW.self_of_nhds
  have F := (((((directional_smoothAt u (pair_smooth g v w)).add (directional_smoothAt v (pair_smooth g w u))).sub
    (directional_smoothAt w (pair_smooth g u v))).sub (pair_smooth g v (smooth_bracket u w))).sub
    (pair_smooth g w (smooth_bracket v u))).add (pair_smooth g u (smooth_bracket w v))
  apply (F.mul (contMDiffAt_const (c := (2:ℝ)⁻¹))).congr_of_eventuallyEq
  filter_upwards [hU,hV,hW] with q u v w
  rw [firstKind_koszul g U V W q (u.mdifferentiableAt (by simp)) (v.mdifferentiableAt (by simp))
    (w.mdifferentiableAt (by simp)), div_eq_mul_inv]
  rfl

/-- Locally invert the Gram matrix to recover the vector-valued connection from
its first-kind coefficients. The argument uses only smoothness and positivity of the metric. -/
theorem nabla_smoothAt (g : SmoothMetric) {U V : Field} {p : Base}
    (hU : ∀ᶠ q in 𝓝 p, FieldSmoothAt U q) (hV : ∀ᶠ q in 𝓝 p, FieldSmoothAt V q) :
    FieldSmoothAt (nabla g U V) p := by
  let e := trivializationAt Coordinates (TangentSpace productModel : Base → Type) p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt' p
  let coord (x : Coordinates) : Field := fun q => e.symmL ℝ q x
  have hcoord (x : Coordinates) : ∀ᶠ q in 𝓝 p, FieldSmoothAt (coord x) q := by
    filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
    rw [FieldSmoothAt, e.contMDiffAt_section_iff hq]
    apply (contMDiffAt_const (c := x)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hq] with z hz
    simp [coord, hz]
  let G (q : Base) : Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ :=
    letI : IsNormableSpace ℝ (Tangent q) := inferInstanceAs (IsNormableSpace ℝ Coordinates)
    (g.inner q).bilinearComp (e.symmL ℝ q) (e.symmL ℝ q)
  have hG : ContMDiffAt productModel 𝓘(ℝ, Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ) ∞ G p := by
    apply smoothAt_clm_of_apply
    intro x
    apply smoothAt_clm_of_apply
    intro y
    exact pair_smooth g (hcoord x).self_of_nhds (hcoord y).self_of_nhds
  have equivG (q : Base) (hq : q ∈ e.baseSet) :
      ∃ L : Coordinates ≃L[ℝ] (Coordinates →L[ℝ] ℝ), (L : Coordinates →L[ℝ] _) = G q := by
    have hinj : Function.Injective (G q) := by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      change G q x = 0 at hx
      by_contra hn
      have ne : e.symmL ℝ q x ≠ 0 := by
        rw [← e.symm_continuousLinearEquivAt_eq' hq]
        exact (e.continuousLinearEquivAt ℝ q hq).symm.map_ne_zero_iff.mpr hn
      have hpos : 0 < G q x x := g.pos q _ ne
      simp [hx] at hpos
    have hr : Module.finrank ℝ Coordinates = Module.finrank ℝ (Coordinates →L[ℝ] ℝ) :=
      Subspace.dual_finrank_eq.symm.trans (LinearMap.toContinuousLinearMap.finrank_eq)
    exact ⟨(LinearEquiv.ofInjectiveOfFinrankEq (G q).toLinearMap hinj hr).toContinuousLinearEquiv, rfl⟩
  obtain ⟨L,hL⟩ := equivG p hp
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G p) := hL ▸ contDiffAt_map_inverse L
  let α (q : Base) : Coordinates →L[ℝ] ℝ := (g.inner q (nabla g U V q)).comp (e.symmL ℝ q)
  have hα : ContMDiffAt productModel 𝓘(ℝ, Coordinates →L[ℝ] ℝ) ∞ α p := by
    apply smoothAt_clm_of_apply
    exact fun x => smooth_firstKind g hU hV (hcoord x)
  rw [FieldSmoothAt, e.contMDiffAt_section_iff hp]
  apply ((hi.contMDiffAt.comp p hG).clm_apply hα).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
  obtain ⟨L,hL⟩ := equivG q hq
  change (e ⟨q,nabla g U V q⟩).2 = (G q).inverse (α q)
  rw [← hL, ContinuousLinearMap.inverse_equiv]
  apply L.injective
  change L _ = L (L.symm (α q))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change L.toContinuousLinearMap _ = α q
  rw [hL]
  apply ContinuousLinearMap.ext
  intro y
  change g.inner q (e.symmL ℝ q (e ⟨q,nabla g U V q⟩).2) _ = _
  simp [e.symmL_apply hq, α, hq]

theorem extend_smooth_near {p : Base} (v : Tangent p) :
    ∀ᶠ q in 𝓝 p, FieldSmoothAt (extend Coordinates v) q := by
  obtain ⟨s, hs, h⟩ := exists_contMDiffOn_extend (k := ∞) productModel Coordinates v
  filter_upwards [eventually_eventually_nhds.mpr hs] with q hq
  exact h.contMDiffAt hq


/-- Metric compatibility expands the curvature numerator of any smooth metric
on the sphere product into derivatives and contractions of first-kind symbols. -/
theorem curvatureNumerator_firstKind (g : SmoothMetric) (p : Base) (X Y : Tangent p) :
    let U := extend Coordinates X
    let V := extend Coordinates Y
    curvatureNumerator g p X Y =
      directional U (firstKind g V V U) p - directional V (firstKind g U V U) p +
      metricPair g (nabla g U V) (nabla g V U) p -
      metricPair g (nabla g V V) (nabla g U U) p -
      firstKind g (VectorField.mlieBracket productModel U V) V U p := by
  dsimp only
  let U := extend (E := Tangent) Coordinates X
  let V := extend (E := Tangent) Coordinates Y
  have hU : FieldDiffAt U p := mdifferentiableAt_extend productModel Coordinates X
  have hVV := (nabla_smoothAt g (extend_smooth_near Y) (extend_smooth_near Y)).mdifferentiableAt (by simp)
  have hUV := (nabla_smoothAt g (extend_smooth_near X) (extend_smooth_near Y)).mdifferentiableAt (by simp)
  have h₁ := derivative_metricPair g U (nabla g V V) U p hVV hU
  have h₂ := derivative_metricPair g V (nabla g U V) U p hUV hU
  have hr : curvatureNumerator g p X Y =
      metricPair g (nabla g U (nabla g V V)) U p -
      metricPair g (nabla g V (nabla g U V)) U p -
      metricPair g (nabla g (VectorField.mlieBracket productModel U V) V) U p := by
    simp [curvatureNumerator, metricPair, nabla, U, V, map_sub]
    rfl
  change _ = directional U (metricPair g (nabla g V V) U) p -
    directional V (metricPair g (nabla g U V) U) p + _ - _ - _
  rw [hr, h₁, h₂]
  unfold firstKind
  ring

end
end LocalHopf.SphereProduct
