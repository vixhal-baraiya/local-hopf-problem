import LocalHopf.SphereProduct
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-! # The unconditional geometric statement

These definitions spell out the target theorem on the sphere product. The convergence
test uses all tensor coefficients in stereographic product charts and all derivative
orders on compact subsets of their targets (§7).
-/

namespace LocalHopf.SphereProduct

open Bundle Set Filter
open scoped Manifold ContDiff

noncomputable section

abbrev Coordinates := EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)
abbrev productModel := (𝓡 2).prod (𝓡 2)
abbrev Tangent (p : Base) := TangentSpace productModel p

/-- `g(R(X,Y)Y,X)` for the Levi-Civita connection, using local extensions constant
in a bundle trivialization at the given point. -/
def curvatureNumerator (g : SmoothMetric) (p : Base) (X Y : Tangent p) : ℝ :=
  letI : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  let cov := CovariantDerivative.leviCivitaConnection productModel Base
  let U := FiberBundle.extend (E := Tangent) Coordinates X
  let V := FiberBundle.extend (E := Tangent) Coordinates Y
  let A := cov (fun q => cov V q (V q)) p X
  let B := cov (fun q => cov V q (U q)) p Y
  let C := cov V p (VectorField.mlieBracket productModel U V p)
  g.inner p (A - B - C) X

/-- On an orthonormal pair the sectional curvature equals the curvature numerator. -/
def PositiveSectionalCurvature (g : SmoothMetric) : Prop :=
  ∀ (p : Base) (X Y : Tangent p), g.inner p X X = 1 → g.inner p Y Y = 1 →
    g.inner p X Y = 0 → 0 < curvatureNumerator g p X Y

/-- Evaluate a covariant two-tensor on constant coordinate vectors in the chart at `p`.
Only points in the open chart target enter the convergence test. -/
def chartCoefficient (pair : (q : Base) → Tangent q → Tangent q → ℝ)
    (p : Base) (a b z : Coordinates) : ℝ :=
  let e := (extChartAt productModel p).symm
  let D := mfderiv 𝓘(ℝ, Coordinates) productModel e z
  pair (e z) (D a) (D b)

/-- Compact-open convergence of every order of derivative of the metric coefficients
to the coefficients of the round product pairing. -/
def ConvergesToRound (g : ℕ → SmoothMetric) : Prop :=
  ∀ (p : Base) (a b : Coordinates) (j : ℕ) (K : Set Coordinates),
    IsCompact K → K ⊆ (extChartAt productModel p).target →
    TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ j (chartCoefficient (fun q X Y => (g n).inner q X Y) p a b))
      (iteratedFDeriv ℝ j (chartCoefficient (fun q X Y => roundPair q (X.1, X.2) (Y.1, Y.2)) p a b))
      atTop K

/-- The full Local Hopf Problem I on the concrete manifold. Proving this proposition
requires constructing the metrics and identifying their curvature and convergence. -/
def LocalHopfProblem : Prop :=
  ∃ g : ℕ → SmoothMetric, (∀ n, PositiveSectionalCurvature (g n)) ∧ ConvergesToRound g

end
end LocalHopf.SphereProduct
