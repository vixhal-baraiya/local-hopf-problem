import LocalHopf.CoordinateCurvature
import LocalHopf.CurvatureJets
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Curvature of a smooth metric from its coordinate two-jet

The six-by-six curvature operator in the verification scripts is computed using
the inverse of the four-by-four metric matrix. The identity below evaluates its
sectional numerator directly on two tangent vectors.
-/
namespace LocalHopf.SphereProduct
open Bundle FiberBundle Filter Matrix
open scoped Manifold ContDiff Topology
noncomputable section

abbrev Frame (p : Base) := Module.Basis (Fin 4) ℝ (Tangent p)

/-- A basis of the four-dimensional intrinsic tangent space at every sphere pair. -/
def coordinateFrame (p : Base) : Frame p := by
  let : FiniteDimensional ℝ (Tangent p) := inferInstanceAs (FiniteDimensional ℝ Coordinates)
  have h : Module.finrank ℝ (Tangent p) = 4 := by
    change Module.finrank ℝ Coordinates = 4
    simp [Coordinates, Module.finrank_prod]
  exact (Module.finBasis ℝ (Tangent p)).reindex (finCongr h)

def gramMatrix (g : SmoothMetric) {p : Base} (b : Frame p) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => g.inner p (b i) (b j)

def frameCovector (g : SmoothMetric) {p : Base} (b : Frame p) (Z : Tangent p) (i : Fin 4) :=
  g.inner p (b i) Z

private theorem gram_mulVec (g : SmoothMetric) {p : Base} (b : Frame p) (x : Fin 4 → ℝ) :
    gramMatrix g b *ᵥ x = frameCovector g b (b.equivFun.symm x) := by
  ext i
  simp [gramMatrix, mulVec, dotProduct, frameCovector, b.equivFun_symm_apply, mul_comm]

private theorem lower_pair (g : SmoothMetric) {p : Base} (b : Frame p) (X Y : Tangent p) :
    frameCovector g b X ⬝ᵥ b.equivFun Y = g.inner p X Y := by
  calc
    _ = g.inner p X (b.equivFun.symm (b.equivFun Y)) := by
      simp only [b.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul, frameCovector, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      rw [g.symm p (b i) X, mul_comm]
    _ = _ := by rw [b.equivFun.symm_apply_apply]

theorem gram_isUnit (g : SmoothMetric) {p : Base} (b : Frame p) : IsUnit (gramMatrix g b).det := by
  apply (gramMatrix g b).isUnit_iff_isUnit_det.mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  rw [gram_mulVec, gram_mulVec] at h
  apply b.equivFun.symm.injective
  let X := b.equivFun.symm x
  let Y := b.equivFun.symm y
  by_contra hne
  have H := congrArg (fun z : Fin 4 → ℝ => z ⬝ᵥ b.equivFun (X-Y)) h
  change frameCovector g b X ⬝ᵥ _ = frameCovector g b Y ⬝ᵥ _ at H
  rw [lower_pair, lower_pair] at H
  have hn := g.pos p (X-Y) (sub_ne_zero.mpr hne)
  rw [show g.inner p (X-Y) = g.inner p X - g.inner p Y from map_sub _ _ _, sub_apply, H, sub_self] at hn
  exact (lt_irrefl _ hn)

/-- Pairing of two vectors from their covariant components and the inverse Gram matrix. -/
theorem metric_inverse_pair (g : SmoothMetric) {p : Base} (b : Frame p) (X Y : Tangent p) :
    g.inner p X Y = frameCovector g b X ⬝ᵥ (gramMatrix g b)⁻¹ *ᵥ frameCovector g b Y := by
  have he : (gramMatrix g b) *ᵥ b.equivFun Y = frameCovector g b Y := by
    rw [gram_mulVec, b.equivFun.symm_apply_apply]
  rw [← he, mulVec_mulVec, nonsing_inv_mul _ (gram_isUnit g b), one_mulVec, lower_pair]

/-- The first-kind symbol in the chart, using only spatial derivatives of the metric. -/
def gamma (g : SmoothMetric) {p : Base} (X Y Z : Tangent p) :=
  let U := extend Coordinates X
  let V := extend Coordinates Y
  let W := extend Coordinates Z
  (directional U (metricPair g V W) p + directional V (metricPair g U W) p -
    directional W (metricPair g U V) p)/2

theorem gamma_eq (g : SmoothMetric) {p : Base} (X Y Z : Tangent p) :
    gamma g X Y Z = g.inner p (nabla g (extend Coordinates X) (extend Coordinates Y) p) Z := by
  let U := extend (E := Tangent) Coordinates X
  let V := extend (E := Tangent) Coordinates Y
  let W := extend (E := Tangent) Coordinates Z
  have h := firstKind_koszul g U V W p (mdifferentiableAt_extend productModel Coordinates X)
    (mdifferentiableAt_extend productModel Coordinates Y) (mdifferentiableAt_extend productModel Coordinates Z)
  have hs : metricPair g W U = metricPair g U W := funext fun q => g.symm q _ _
  rw [hs] at h
  have hb (a b : Tangent p) := (extend_commute a b).self_of_nhds
  simpa [gamma, firstKind, metricPair, U, V, W, hb] using h.symm

/-- The spatial second-derivative part in the (U,V) plane. -/
def secondPart (g : SmoothMetric) {p : Base} (X Y : Tangent p) : ℝ :=
  let U := extend Coordinates X
  let V := extend Coordinates Y
  directional U (fun q => directional V (metricPair g V U) q - directional U (metricPair g V V) q/2) p -
    directional V (fun q => directional V (metricPair g U U) q/2) p

/-- The intrinsic Levi-Civita numerator equals the scalar metric second-derivative
part plus the two signed contractions of first-kind symbols used in `jets.curvature`. -/
theorem curvature_from_metric_jet (g : SmoothMetric) {p : Base} (b : Frame p) (X Y : Tangent p) :
    let G := (gramMatrix g b)⁻¹
    let Γ (A B : Tangent p) (i : Fin 4) := gamma g A B (b i)
    curvatureNumerator g p X Y = secondPart g X Y + Γ X Y ⬝ᵥ G *ᵥ Γ X Y -
      Γ X X ⬝ᵥ G *ᵥ Γ Y Y := by
  have h (A B : Tangent p) :
      frameCovector g b (nabla g (extend Coordinates A) (extend Coordinates B) p) =
        fun i => gamma g A B (b i) := by
    funext i
    rw [gamma_eq, frameCovector, g.symm]
  rw [curvatureNumerator_coordinates]
  dsimp only
  change secondPart g X Y + g.inner p _ _ - g.inner p _ _ = _
  rw [metric_inverse_pair g b, metric_inverse_pair g b]
  simp only [h]

end
end LocalHopf.SphereProduct
