/-
Copyright (c) 2026. Released under the MIT License (see ../../LICENSE).

# Theorem 3.4 (perturbation theorem on the bundle of planes)

Let `u : 𝒩 × [0, s₀] → ℝ`. PROOF.md, Theorem 3.4, shows `min u(·, s) > 0` for small `s > 0` from

* **away from `Z`** (from (H0)): `u ≥ a - C s` where `d(·, Z) ≥ δ`, with `a = σδ² > 0`;
* **in the tube** (from Lemma 3.1, Definition 3.2): `u(E(x,w), s) ≥ s² U₂(x) + s³ U₃(x) - C s⁴`;
* **(H2)**: `U₂ ≥ κρ` on `Z`, and `U₃ ≥ κ` on `Σ = {ρ = 0}`, with `ρ ≥ 0`, `ρ, U₃` continuous
  and `Z` compact.

`eventually_positive` is exactly this argument, with the two regions abstracted as a predicate
`far` and a projection `proj : 𝒩 → Z` onto the core of the tube.
-/
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

namespace LocalHopf

open Set

/-- On the compact set `{U₃ ≤ κ/2}`, `ρ` has a positive lower bound (step 4 of Theorem 3.4). -/
theorem exists_rho_lower {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (U₃ ρ : Z → ℝ) (hU₃ : Continuous U₃) (hρ : Continuous ρ) (κ : ℝ) (hκ : 0 < κ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hSig : ∀ x, ρ x = 0 → κ ≤ U₃ x) :
    ∃ ρ₀ > 0, ∀ x, U₃ x ≤ κ / 2 → ρ₀ ≤ ρ x := by
  set Kset := {x | U₃ x ≤ κ / 2}
  have hK : IsCompact Kset := (isClosed_le hU₃ continuous_const).isCompact
  rcases Kset.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    have : x ∈ Kset := hx
    rw [he] at this; simp at this
  · obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hne hρ.continuousOn
    refine ⟨ρ x₀, ?_, fun x hx => hmin hx⟩
    rcases (hρ0 x₀).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hSig x₀ h.symm
      have h2 : U₃ x₀ ≤ κ / 2 := hx₀K
      linarith

/-- **Theorem 3.4.** Positivity of `u(·, s)` for all sufficiently small `s > 0`. -/
theorem eventually_positive {𝒩 Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (u : 𝒩 → ℝ → ℝ) (U₂ U₃ ρ : Z → ℝ) (hU₃ : Continuous U₃) (hρ : Continuous ρ)
    (κ : ℝ) (hκ : 0 < κ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hU₂ : ∀ x, κ * ρ x ≤ U₂ x) (hSig : ∀ x, ρ x = 0 → κ ≤ U₃ x)
    (far : 𝒩 → Prop) (proj : 𝒩 → Z) (a C s₁ : ℝ) (ha : 0 < a) (hs₁ : 0 < s₁)
    (hfar : ∀ π s, 0 < s → s ≤ s₁ → far π → a - C * s ≤ u π s)
    (hnear : ∀ π s, 0 < s → s ≤ s₁ → ¬ far π →
      s ^ 2 * U₂ (proj π) + s ^ 3 * U₃ (proj π) - C * s ^ 4 ≤ u π s) :
    ∃ s₀ > 0, ∀ π s, 0 < s → s < s₀ → 0 < u π s := by
  obtain ⟨ρ₀, hρ₀, hρlow⟩ := exists_rho_lower U₃ ρ hU₃ hρ κ hκ hρ0 hSig
  -- `U₃` is bounded below on the compact space `Z`
  obtain ⟨m, hm⟩ := (isCompact_univ.image hU₃).bddBelow
  have hm' : ∀ x, m ≤ U₃ x := fun x => hm ⟨x, mem_univ _, rfl⟩
  set c := |C| + 1 with hc
  have hcpos : 0 < c := by positivity
  set e := |m| + |C| + 1 with he
  have hepos : 0 < e := by positivity
  refine ⟨min (min s₁ 1) (min (a / c) (min (κ / (2 * c)) (κ * ρ₀ / (2 * e)))), ?_, ?_⟩
  · apply lt_min (lt_min hs₁ one_pos)
    apply lt_min (div_pos ha hcpos) (lt_min (by positivity) (by positivity))
  intro π s hs hs₀
  simp only [lt_min_iff] at hs₀
  obtain ⟨⟨hss₁, hs1⟩, hsa, hsκ, hsκρ⟩ := hs₀
  have hCs : C * s ≤ |C| * s := mul_le_mul_of_nonneg_right (le_abs_self C) hs.le
  by_cases hπ : far π
  · -- away from `Z`: `u ≥ a - C s > 0`
    have h := hfar π s hs hss₁.le hπ
    have : c * s < a := by rwa [lt_div_iff₀ hcpos, mul_comm] at hsa
    nlinarith
  · have h := hnear π s hs hss₁.le hπ
    set x := proj π
    have hU₂x : 0 ≤ U₂ x := le_trans (mul_nonneg hκ.le (hρ0 x)) (hU₂ x)
    have hs2 : 0 < s ^ 2 := by positivity
    have hs3 : 0 < s ^ 3 := by positivity
    have hsplit : s ^ 2 * U₂ x + s ^ 3 * U₃ x - C * s ^ 4
        = s ^ 2 * U₂ x + s ^ 3 * (U₃ x - C * s) := by ring
    by_cases hx : κ / 2 < U₃ x
    · -- near `Σ`: the cubic term wins
      have : c * s < κ / 2 := by
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * c)] at hsκ; nlinarith
      have hpos : 0 < U₃ x - C * s := by nlinarith
      have := mul_pos hs3 hpos
      have := mul_nonneg hs2.le hU₂x
      linarith
    · -- on `Z \ A`: `ρ ≥ ρ₀` and the quadratic term wins
      push Not at hx
      have hρx := hρlow x hx
      have hU₂ρ : κ * ρ₀ ≤ U₂ x := le_trans (mul_le_mul_of_nonneg_left hρx hκ.le) (hU₂ x)
      have hes : e * s < κ * ρ₀ / 2 := by
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * e)] at hsκρ; nlinarith
      -- `U₂ + s U₃ - C s² ≥ κρ₀ - s(|m| + |C|) > 0`
      have hmU : -|m| ≤ U₃ x := le_trans (neg_abs_le m) (hm' x)
      have hs2le : s ^ 2 ≤ s := by nlinarith
      have hCs2 : C * s ^ 2 ≤ |C| * s := by
        calc C * s ^ 2 ≤ |C| * s ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
          _ ≤ |C| * s := mul_le_mul_of_nonneg_left hs2le (abs_nonneg C)
      have hsU : -|m| * s ≤ s * U₃ x := by nlinarith
      have hinner : 0 < U₂ x + s * U₃ x - C * s ^ 2 := by nlinarith
      have hfac : s ^ 2 * U₂ x + s ^ 3 * U₃ x - C * s ^ 4
          = s ^ 2 * (U₂ x + s * U₃ x - C * s ^ 2) := by ring
      have := mul_pos hs2 hinner
      linarith

end LocalHopf
