import LocalHopf.GeometricStatement
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.Algebra.Structures

/-! # Smooth metrics obtained by restricting ambient bilinear forms to the sphere product -/

namespace LocalHopf.SphereProduct

open Set Bundle FiberBundle Filter NormedSpace Bornology
open scoped ContDiff Manifold Topology EuclideanSpace
noncomputable section

abbrev AmbientForm := Cheeger.V →L[ℝ] Cheeger.V →L[ℝ] ℝ

def ambientPoint (p : Base) : Cheeger.V := (p.1.val.ofLp, p.2.val.ofLp)

def ambientVelocityL (p : Base) : Tangent p →L[ℝ] Cheeger.V :=
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
  (e.comp (velocity p.1)).prodMap (e.comp (velocity p.2))

theorem ambientVelocityL_apply (p : Base) (X : Tangent p) :
    ambientVelocityL p X = ambientVelocity p (X.1,X.2) := rfl

theorem ambientPoint_smooth : ContMDiff productModel 𝓘(ℝ, Cheeger.V) ∞ ambientPoint := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hi : ContMDiff (𝓡 2) 𝓘(ℝ,E3) ∞ (Subtype.val : Sphere → E3) := contMDiff_coe_sphere
  have h : ContMDiff (𝓡 2) 𝓘(ℝ, R3) ∞ (fun p : Sphere => p.val.ofLp) :=
    e.contDiff.contMDiff.comp hi
  exact (h.comp contMDiff_fst).prodMk_space (h.comp contMDiff_snd)

theorem ambientVelocity_smooth : ContMDiff productModel.tangent 𝓘(ℝ, Cheeger.V) ∞
    (fun w : TangentBundle productModel Base => ambientVelocityL w.1 w.2) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have h := e.contDiff.contMDiff.comp smooth_velocity
  have h₁ := h.comp (contMDiff_fst (I := (𝓡 2).tangent) (J := (𝓡 2).tangent)
    (M := TangentBundle (𝓡 2) Sphere) (N := TangentBundle (𝓡 2) Sphere))
  have h₂ := h.comp (contMDiff_snd (I := (𝓡 2).tangent) (J := (𝓡 2).tangent)
    (M := TangentBundle (𝓡 2) Sphere) (N := TangentBundle (𝓡 2) Sphere))
  intro w
  exact (h₁.prodMk_space h₂).contMDiffAt.comp w (contMDiff_equivTangentBundleProd w)

theorem ambientVelocityL_injective (p : Base) : Function.Injective (ambientVelocityL p) := by
  intro X Y h
  apply Prod.ext
  · exact velocity_injective _ (congrArg (fun z : Cheeger.V => WithLp.toLp 2 z.1) h)
  · exact velocity_injective _ (congrArg (fun z : Cheeger.V => WithLp.toLp 2 z.2) h)

theorem smoothAt_clm_of_apply {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Base → E →L[ℝ] F} {p : Base}
    (h : ∀ v, ContMDiffAt productModel 𝓘(ℝ,F) ∞ (fun q => f q v) p) :
    ContMDiffAt productModel 𝓘(ℝ,E →L[ℝ] F) ∞ f p := by
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt, contDiffWithinAt_clm_apply]
  intro v
  exact contMDiffWithinAt_iff_contDiffWithinAt.mp (contMDiffAt_iff_source.mp (h v))

private def restrictForm (A : Base → AmbientForm) (p : Base) :
    Tangent p →L[ℝ] Tangent p →L[ℝ] ℝ :=
  letI : IsNormableSpace ℝ (Tangent p) := inferInstanceAs (IsNormableSpace ℝ Coordinates)
  (A p).bilinearComp (ambientVelocityL p) (ambientVelocityL p)

private theorem smooth_restrictForm (A : Base → AmbientForm)
    (hA : ContMDiff productModel 𝓘(ℝ,AmbientForm) ∞ A) :
    ContMDiff productModel (productModel.prod 𝓘(ℝ, Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk' (Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ) p (restrictForm A p)) := by
  intro p
  rw [contMDiffAt_section_iff]
  apply smoothAt_clm_of_apply
  intro X
  apply smoothAt_clm_of_apply
  intro Y
  let e := trivializationAt Coordinates (TangentSpace productModel : Base → Type) p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt' p
  have he (v : Coordinates) : ContMDiffAt productModel productModel.tangent ∞
      (fun q : Base => TotalSpace.mk' Coordinates q (e.symm q v)) p := by
    rw [e.contMDiffAt_section_iff hp]
    apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
    simp [hq]
  have h := (hA p).clm_apply (ambientVelocity_smooth.contMDiffAt.comp p (he X))
  apply (h.clm_apply (ambientVelocity_smooth.contMDiffAt.comp p (he Y))).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hq hq (Set.mem_univ _)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]
  rfl

private theorem bounded_unit_ellipsoid (B : Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ)
    (hpos : ∀ v ≠ 0, 0 < B v v) : IsVonNBounded ℝ {v | B v v < 1} := by
  have hs := isCompact_sphere (0 : Coordinates) 1
  obtain ⟨u, hu, hmin⟩ := hs.exists_isMinOn (NormedSpace.sphere_nonempty.mpr zero_le_one)
    (B.continuous.clm_apply continuous_id).continuousOn
  have hm := hpos u (ne_zero_of_mem_unit_sphere ⟨u, hu⟩)
  rw [NormedSpace.isVonNBounded_iff']
  refine ⟨max 1 (1 / B u u), fun v hv => ?_⟩
  by_cases small : ‖v‖ ≤ 1
  · exact small.trans (le_max_left ..)
  have hn : 0 < ‖v‖ := by linarith
  have hunit : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Coordinates) 1 := by
    simp [norm_smul, hn.ne']
  have hl := hmin hunit
  change B u u ≤ B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) at hl
  simp only [map_smul, smul_apply, smul_eq_mul] at hl
  field_simp [hn.ne'] at hl
  apply le_trans _ (le_max_right ..)
  rw [le_div_iff₀ hm]
  change B v v < 1 at hv
  nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge small)) (mul_nonneg hn.le hm.le)]

/-- Restrict a smooth ambient tensor to the tangent bundle. Positive definiteness
is required only on nonzero tangent vectors. -/
def metricOfAmbient (A : Base → AmbientForm) (hA : ContMDiff productModel 𝓘(ℝ,AmbientForm) ∞ A)
    (hsym : ∀ p X Y, A p X Y = A p Y X)
    (hpos : ∀ (p : Base) (X : Tangent p), X ≠ 0 → 0 < A p (ambientVelocityL p X) (ambientVelocityL p X)) :
    SmoothMetric where
  inner := restrictForm A
  symm p X Y := hsym p (ambientVelocityL p X) (ambientVelocityL p Y)
  pos := hpos
  isVonNBounded p := bounded_unit_ellipsoid (restrictForm A p) (hpos p)
  contMDiff := smooth_restrictForm A hA

/-- The product Euclidean pairing on the two ambient coordinate spaces. -/
def ambientRoundForm : AmbientForm :=
  let e (i : Fin 3) : R3 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let a i := (e i).comp (ContinuousLinearMap.fst ℝ R3 R3)
  let b i := (e i).comp (ContinuousLinearMap.snd ℝ R3 R3)
  (∑ i, (a i).smulRight (a i)) + ∑ i, (b i).smulRight (b i)

theorem ambientRoundForm_apply (X Y : Cheeger.V) : ambientRoundForm X Y = gprod X Y := by
  simp [ambientRoundForm, gprod, dotProduct, Fin.sum_univ_three]

/-- The background tensor before restriction to tangent vectors. -/
def ambientBackground (t : ℝ) (p : Base) : AmbientForm :=
  (1 / 2 : ℝ) • ambientRoundForm.comp (Cheeger.ambientOperator (ambientPoint p, t))

theorem ambientBackground_apply (p : Base) {t : ℝ} (ht : 0 ≤ t) (X Y : Cheeger.V) :
    ambientBackground t p X Y = Cheeger.pairing (ambientPoint p).1 (ambientPoint p).2 t ht X Y / 2 := by
  simp [ambientBackground, ambientRoundForm_apply, ambientPoint, Cheeger.ambientOperator_apply ht,
    Cheeger.pairing, div_eq_inv_mul]

theorem ambientBackground_smooth {t : ℝ} (ht : 0 ≤ t) :
    ContMDiff productModel 𝓘(ℝ,AmbientForm) ∞ (ambientBackground t) := by
  intro p
  have h := (Cheeger.smooth_ambientOperator (p := (ambientPoint p).1) (q := (ambientPoint p).2) ht
    ).contMDiffAt.comp p ((ambientPoint_smooth p).prodMk_space (contMDiffAt_const (c := t)))
  apply smoothAt_clm_of_apply
  intro X
  apply smoothAt_clm_of_apply
  intro Y
  have hx := h.clm_apply (contMDiffAt_const (c := X))
  have hpair : ContMDiffAt productModel 𝓘(ℝ, ℝ) ∞
      (fun q => ambientRoundForm (Cheeger.ambientOperator (ambientPoint q, t) X) Y) p :=
    (ambientRoundForm.flip Y).contDiff.contMDiff.contMDiffAt.comp p hx
  exact (contMDiffAt_const (c := (1/2 : ℝ))).mul hpair

/-- The smooth Riemannian metric half the Cheeger deformation. -/
def backgroundMetric (t : ℝ) (ht : 0 ≤ t) : SmoothMetric :=
  metricOfAmbient (ambientBackground t) (ambientBackground_smooth ht)
    (fun p X Y => by rw [ambientBackground_apply p ht, ambientBackground_apply p ht,
      Cheeger.pairing_symm _ _ _ ht X Y])
    (fun p X hX => by
      rw [ambientBackground_apply p ht]
      exact backgroundPair_pos p t ht (X := (X.1, X.2)) hX)

theorem backgroundMetric_inner (t : ℝ) (ht : 0 ≤ t) (p : Base) (X Y : Tangent p) :
    (backgroundMetric t ht).inner p X Y = backgroundPair p t ht (X.1, X.2) (Y.1, Y.2) :=
  ambientBackground_apply p ht _ _

theorem twice_backgroundMetric_zero (p : Base) (X Y : Tangent p) :
    2 * (backgroundMetric 0 le_rfl).inner p X Y = roundPair p (X.1, X.2) (Y.1, Y.2) := by
  rw [backgroundMetric_inner]
  exact twice_backgroundPair_zero p _ _


end
end LocalHopf.SphereProduct
