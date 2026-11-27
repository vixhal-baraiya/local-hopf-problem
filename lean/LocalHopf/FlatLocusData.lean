import Mathlib.Topology.Compactness.Compact
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Instances.Real.Lemmas

namespace LocalHopf

open Set Matrix

/-- The topological and frame data used in the positivity argument.
`FlatLocus.data` constructs these data on the incidence space of §1. -/
structure FlatLocusData where
  /-- The parameter space of the flat locus (§1). -/
  Z : Type
  [topZ : TopologicalSpace Z]
  [compactZ : CompactSpace Z]
  /-- `ρ = 1 - ⟨n, e_z⟩²` on `Z`. -/
  ρ : Z → ℝ
  ρ_cont : Continuous ρ
  ρ_nonneg : ∀ x, 0 ≤ ρ x
  /-- The planes over regular pairs `p₁ ≠ ± p₂`. -/
  Ω : Set Z
  /-- **[geometry]** `Ω` is dense in `Z` (§3). -/
  Ω_dense : Dense Ω
  /-- **[geometry]** `Σ ∩ Ω` is dense in `Σ = {ρ = 0}` (regular pairs are dense in the equatorial
  torus). -/
  Sig_dense : ∀ x, ρ x = 0 → x ∈ closure {y | y ∈ Ω ∧ ρ y = 0}
  /-- Frame data at a regular plane: the components `n_x, n_y, n_z` of the unit normal, the
  projections `x', z'` of `e_x, e_z` to the plane of `Γ` (in an orthonormal basis of that plane),
  and `u = ⟨p₁, p₂⟩`. -/
  nx : Z → ℝ
  ny : Z → ℝ
  nz : Z → ℝ
  xp : Z → Fin 2 → ℝ
  zp : Z → Fin 2 → ℝ
  sep : Z → ℝ
  /-- **[geometry]** Elementary facts about the frame (§5): `n` is a unit vector,
  `ρ = n_x² + n_y² = |z'|²`, `|x'| ≤ 1`, and `u ∈ [-1, 1]`. -/
  frame : ∀ x ∈ Ω, nx x ^ 2 + ny x ^ 2 = ρ x ∧ nx x ^ 2 + ny x ^ 2 + nz x ^ 2 = 1 ∧
    zp x ⬝ᵥ zp x = ρ x ∧ xp x ⬝ᵥ xp x ≤ 1 ∧ sep x ∈ Icc (-1 : ℝ) 1

attribute [instance] FlatLocusData.topZ FlatLocusData.compactZ

end LocalHopf
