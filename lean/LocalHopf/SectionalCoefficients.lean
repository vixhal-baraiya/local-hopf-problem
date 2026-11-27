import LocalHopf.MetricCurvatureExpansion
import Mathlib.Algebra.Polynomial.Div

/-! # The raw quadratic and cubic curvature coefficients

In a fixed frame the metric determinant is nonzero at the background. Exact
division of the two coordinate polynomials therefore produces the first four
Taylor coefficients, with a continuous remainder at zero. Normal minimization
and evaluation of the certificate are subsequent operations.
-/
namespace LocalHopf.SphereProduct
open Polynomial Matrix Bundle Filter
open scoped Topology Manifold ContDiff
noncomputable section

private def poly (a : Fin 4 → ℝ) : ℝ[X] :=
  C (a 0) + X*C (a 1) + X^2*C (a 2) + X^3*C (a 3)

private theorem eval_poly (s : ℝ) (a : Fin 4 → ℝ) :
    (poly a).eval s = cubicValue s a := by simp [poly, cubicValue]; ring

def metricPolynomial (A : Fin 4 → AmbientTensor) {p : Base} (b : Frame p) :
    Matrix (Fin 4) (Fin 4) ℝ[X] :=
  fun i j => poly (fun k => ambientGram (A k) b i j)

theorem eval_metricPolynomial_zero (A : Fin 4 → AmbientTensor) {p : Base} (b : Frame p) :
    (metricPolynomial A b).map (evalRingHom 0) = ambientGram (A 0) b := by
  ext i j
  simp [metricPolynomial, poly]

/-- Clear the denominator in the coordinate curvature formula by the adjugate identity. -/
def numeratorPolynomial (A : Fin 4 → AmbientTensor) {p : Base} (b : Frame p)
    (X Y : Tangent p) : ℝ[X] :=
  let G := metricPolynomial A b
  let Γ (x y : Tangent p) (j : Fin 4) := poly (fun k => ambientGamma (A k) x y (b j))
  poly (fun k => ambientSecond (A k) X Y) * G.det +
    Γ X Y ⬝ᵥ G.adjugate *ᵥ Γ X Y - Γ X X ⬝ᵥ G.adjugate *ᵥ Γ Y Y

def Realizes (g : SmoothMetric) (s : ℝ) (A : Fin 4 → AmbientTensor) : Prop :=
  ∀ (q : Base) (x y : Tangent q), g.inner q x y =
    cubicValue s (fun i => (A i).form q (ambientVelocityL q x) (ambientVelocityL q y))

private theorem eval_gram {s : ℝ} {g : SmoothMetric} {A : Fin 4 → AmbientTensor}
    (hg : Realizes g s A) {p : Base} (b : Frame p) :
    (metricPolynomial A b).map (evalRingHom s) = gramMatrix g b := by
  ext i j
  exact (eval_poly s _).trans (hg p (b i) (b j)).symm

private theorem eval_pair (s : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ[X]) (a d : Fin 4 → ℝ[X]) :
    (a ⬝ᵥ M *ᵥ d).eval s =
      (fun i => (a i).eval s) ⬝ᵥ (M.map (evalRingHom s)) *ᵥ (fun i => (d i).eval s) := by
  simp [dotProduct, mulVec, eval_finsetSum]

/-- Evaluate the numerator before Taylor division. Only the scalar metric jets
depend on the two vectors when the sphere pair and frame are fixed. -/
theorem eval_numeratorPolynomial (A : Fin 4 → AmbientTensor) {p : Base} (b : Frame p)
    (X Y : Tangent p) (s : ℝ) :
    let G := metricPolynomial A b
    let J (x y : Tangent p) (j : Fin 4) := cubicValue s (fun k => ambientGamma (A k) x y (b j))
    let M := G.adjugate.map (evalRingHom s)
    (numeratorPolynomial A b X Y).eval s = cubicValue s (fun k => ambientSecond (A k) X Y) * G.det.eval s +
      J X Y ⬝ᵥ M *ᵥ J X Y - J X X ⬝ᵥ M *ᵥ J Y Y := by
  simp only [numeratorPolynomial, eval_sub, eval_add, eval_mul, eval_pair, eval_poly]

theorem curvature_rational {s : ℝ} {g : SmoothMetric} {A : Fin 4 → AmbientTensor}
    (hg : Realizes g s A) {p : Base} (b : Frame p) (X Y : Tangent p) :
    curvatureNumerator g p X Y = (numeratorPolynomial A b X Y).eval s /
      (metricPolynomial A b).det.eval s := by
  let G := metricPolynomial A b
  have hG := eval_gram hg b
  have hd : G.det.eval s = (gramMatrix g b).det := ((evalRingHom s).map_det G).trans (congrArg det hG)
  have ha : G.adjugate.map (evalRingHom s) = (gramMatrix g b).adjugate := by
    rw [← hG]; exact (evalRingHom s).map_adjugate G
  have hΓ (x y : Tangent p) (i : Fin 4) :
      cubicValue s (fun k => ambientGamma (A k) x y (b i)) = gamma g x y (b i) :=
    ((metric_jet_linear g s A hg x y).1 (b i)).symm
  have hn := (gram_isUnit g b).ne_zero
  rw [curvature_from_metric_jet]
  dsimp only [numeratorPolynomial]
  simp only [eval_sub, eval_add, eval_mul, eval_pair, eval_poly, hΓ, ← (metric_jet_linear g s A hg X Y).2]
  dsimp only [G] at hd ha
  rw [hd, ha, Matrix.inv_def, Ring.inverse_eq_inv]
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul]
  field_simp

/-- One step of Taylor division at the origin. -/
def quotientCoeff (N D : ℝ[X]) := N.coeff 0 / D.coeff 0
def quotientNext (N D : ℝ[X]) := (N - C (quotientCoeff N D) * D).divX

theorem quotient_step (N D : ℝ[X]) (hD : D.coeff 0 ≠ 0) :
    C (quotientCoeff N D) * D + X * quotientNext N D = N := by
  have h : (N - C (quotientCoeff N D) * D).coeff 0 = 0 := by
    simp [quotientCoeff, hD]
  have H := X_mul_divX_add (N - C (quotientCoeff N D) * D)
  rw [h, map_zero, add_zero] at H
  unfold quotientNext
  rw [H]; ring

/-- The numerator after `n` exact steps; only the first four are needed here. -/
def residual (N D : ℝ[X]) : ℕ → ℝ[X]
  | 0 => N
  | n+1 => quotientNext (residual N D n) D

def sectionalCoeff (A : Fin 4 → AmbientTensor) {p : Base} (b : Frame p)
    (X Y : Tangent p) (n : ℕ) : ℝ :=
  let D := (metricPolynomial A b).det
  quotientCoeff (residual (numeratorPolynomial A b X Y) D n) D

theorem curvature_four_coefficients {A : Fin 4 → AmbientTensor} {p : Base}
    (b : Frame p) (X Y : Tangent p) (h₀ : IsUnit (ambientGram (A 0) b).det) :
    ∃ r : ℝ → ℝ, ContinuousAt r 0 ∧ ∀ (s : ℝ) (g : SmoothMetric), Realizes g s A →
      curvatureNumerator g p X Y = cubicValue s (fun i => sectionalCoeff A b X Y i.val) + s^4*r s := by
  let N := numeratorPolynomial A b X Y
  let D := (metricPolynomial A b).det
  have he := eval_metricPolynomial_zero A b
  have hd : D.eval 0 = (ambientGram (A 0) b).det := ((evalRingHom (0:ℝ)).map_det (metricPolynomial A b)).trans (congrArg det he)
  have hD : D.coeff 0 ≠ 0 := by rw [coeff_zero_eq_eval_zero]; exact hd.trans_ne h₀.ne_zero
  refine ⟨fun s => (residual N D 4).eval s / D.eval s, ?_, ?_⟩
  · exact (residual N D 4).continuous.continuousAt.div D.continuous.continuousAt (hd.trans_ne h₀.ne_zero)
  intro s g hg
  have hden : D.eval s ≠ 0 := by
    have h := ((evalRingHom s).map_det (metricPolynomial A b)).trans (congrArg det (eval_gram hg b))
    exact h.trans_ne (gram_isUnit g b).ne_zero
  have step (n : ℕ) : quotientCoeff (residual N D n) D * D.eval s +
      s*(residual N D (n+1)).eval s = (residual N D n).eval s := by
    simpa [residual, eval_add, eval_mul] using congrArg (Polynomial.eval s) (quotient_step (residual N D n) D hD)
  have H := step 0
  rw [curvature_rational hg]
  change N.eval s / D.eval s = cubicValue s (fun i => quotientCoeff (residual N D i.val) D) + _
  change N.eval s / D.eval s = quotientCoeff (residual N D 0) D +
    s * quotientCoeff (residual N D 1) D + s^2 * quotientCoeff (residual N D 2) D +
    s^3 * quotientCoeff (residual N D 3) D + s^4 * ((residual N D 4).eval s / D.eval s)
  field_simp
  change _ + _ = N.eval s at H
  linear_combination -H - s*(step 1) - s^2*(step 2) - s^3*(step 3)

def paperCoefficients (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) : Fin 4 → AmbientTensor :=
  ![backgroundTensor t ht, firstOrderTensor t ht, secondOrderTensor t ht, thirdOrderTensor t ht χ]

theorem paper_metrics_realize (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∃ g : SmoothMetric, Realizes g s (paperCoefficients t ht χ) := by
  filter_upwards [exists_paper_metric t ht χ] with s hs
  obtain ⟨g,hg⟩ := hs
  refine ⟨g, fun p X Y => (hg p X Y).trans ?_⟩
  change backgroundPair p t ht _ _ + _ + _ + _ = ambientBackground t p _ _ + _ + _ + _
  rw [ambientBackground_apply p ht]
  rfl

/-- On each fixed plane of the concrete manifold these are the raw curvature
coefficients of the prescribed metrics, before minimization over tilted planes. -/
theorem paper_curvature_coefficients (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) {p : Base}
    (b : Frame p) (X Y : Tangent p) :
    let A := paperCoefficients t ht χ
    ∃ r : ℝ → ℝ, ContinuousAt r 0 ∧ ∀ᶠ s in 𝓝 (0 : ℝ), ∃ g : SmoothMetric,
      Realizes g s A ∧ curvatureNumerator g p X Y =
        cubicValue s (fun i => sectionalCoeff A b X Y i.val) + s^4*r s := by
  intro A
  have h₀ : ambientGram (A 0) b = gramMatrix (backgroundMetric t ht) b := rfl
  obtain ⟨r,hr,h⟩ := curvature_four_coefficients (A := A) b X Y (h₀ ▸ gram_isUnit _ b)
  refine ⟨r,hr,?_⟩
  filter_upwards [paper_metrics_realize t ht χ] with s hs
  obtain ⟨g,hg⟩ := hs
  exact ⟨g,hg,h s g hg⟩

end
end LocalHopf.SphereProduct
