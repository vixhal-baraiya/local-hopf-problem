import LocalHopf.CurvatureFields

/-! # Curvature in the coordinate frame

The coordinate extensions in `curvatureNumerator` commute. Consequently its
two derivative terms use only the scalar metric coefficients and their first
and second derivatives. The quadratic Christoffel terms have the signs used
by `verification/jets.py`.
-/
namespace LocalHopf.SphereProduct
open Bundle FiberBundle Filter Set VectorField
open scoped Manifold ContDiff Topology
noncomputable section

private abbrev Icoord := 𝓘(ℝ, Coordinates)

set_option backward.isDefEq.respectTransparency false in
theorem extend_commute {p : Base} (X Y : Tangent p) :
    ∀ᶠ q in 𝓝 p, mlieBracket productModel (extend Coordinates X) (extend Coordinates Y) q = 0 := by
  let e := trivializationAt Coordinates (TangentSpace productModel : Base → Type) p
  let φ := extChartAt productModel p
  let C (x : Tangent p) (z : Coordinates) : TangentSpace Icoord z := (e ⟨p,x⟩).2
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt' p
  have hpb (x : Tangent p) : (extend (E := Tangent) Coordinates x : Field) =ᶠ[𝓝 p] mpullback productModel Icoord φ (C x) := by
    filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
    change @Eq (Tangent q) (e.symm q _) ((mfderiv productModel Icoord φ q).inverse _)
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hq,
      ← e.coe_continuousLinearEquivAt_eq' hq, ContinuousLinearMap.inverse_equiv]
    change e.symm q _ = (e.continuousLinearEquivAt ℝ q hq).symm _
    rw [← e.symmL_apply (R := ℝ) hq, ← e.symm_continuousLinearEquivAt_eq' hq]
    rfl
  have hmd (x : Tangent p) (z : Coordinates) :
      MDifferentiableAt Icoord Icoord.tangent
        (fun z => TotalSpace.mk' Coordinates z (C x z)) z :=
    (contMDiffAt_vectorSpace_iff_contDiffAt.mpr (contDiffAt_const (n := 1))).mdifferentiableAt one_ne_zero
  have hcv : mlieBracket Icoord (C X) (C Y) = 0 := by
    rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
    ext1 z
    simp [lieBracketWithin, C]
  filter_upwards [(hpb X).mlieBracket_vectorField (hpb Y), e.open_baseSet.mem_nhds hp] with q he hq
  rw [he, ← mpullback_mlieBracket (hmd X _) (hmd Y _) (contMDiffAt_extChartAt' (I := productModel)
    (n := ∞) hq) (by simp), hcv, mpullback_apply]
  exact map_zero _

/-- The coordinate formula for the true Levi-Civita curvature on `S² × S²`.
For commuting fields the last two terms are the squared norm of Γ(U,V) and
the negative pairing of Γ(U,U) with Γ(V,V). -/
theorem curvatureNumerator_coordinates (g : SmoothMetric) (p : Base) (X Y : Tangent p) :
    let U := extend Coordinates X
    let V := extend Coordinates Y
    curvatureNumerator g p X Y =
      directional U (fun q => directional V (metricPair g V U) q -
        directional U (metricPair g V V) q / 2) p -
      directional V (fun q => directional V (metricPair g U U) q / 2) p +
      metricPair g (nabla g U V) (nabla g U V) p -
      metricPair g (nabla g U U) (nabla g V V) p := by
  simpa only [extend_apply_self] using curvatureNumerator_commuting g p
    (extend Coordinates X) (extend Coordinates Y) (extend_smooth_near X) (extend_smooth_near Y)
    (extend_commute X Y)

end
end LocalHopf.SphereProduct
