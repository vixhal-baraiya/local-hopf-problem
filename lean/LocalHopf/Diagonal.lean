/-
Copyright (c) 2026. Released under the MIT License (see ../../LICENSE).

# Section 7: the diagonal argument

At fixed positive `t`, the scaled perturbations `2 G_{t,s}` are metrics on a positive
interval of `s` and converge to `2 g_t` in each `C^j` as `s → 0⁺`. The backgrounds converge
to the round product as `t → 0⁺`. Section 7 chooses parameters in these intervals.

`C^∞` convergence is modelled by a family of distances `d_j` (the `C^j` distances), increasing in
`j`, with the triangle inequality: `x_n → g` in `C^∞` iff `d_j(x_n, g) → 0` for every `j`.
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace LocalHopf

open Filter Topology Set

/-- The `C^j` distances on a space of metrics. -/
structure CkDistances (Met : Type*) where
  /-- `d j a b` is the `C^j` distance. -/
  d : ℕ → Met → Met → ℝ
  nonneg : ∀ j a b, 0 ≤ d j a b
  triangle : ∀ j a b c, d j a c ≤ d j a b + d j b c
  mono : ∀ a b, Monotone fun j => d j a b

/-- `C^∞` convergence: convergence in every `C^j`. -/
def CkDistances.TendstoCInf {Met : Type*} (D : CkDistances Met) (x : ℕ → Met) (g : Met) : Prop :=
  ∀ j, Tendsto (fun n => D.d j (x n) g) atTop (𝓝 0)

/-- Section 7, including both parameter sequences and the metric window at each `t`. -/
theorem diagonal_parameters {Met : Type*} (D : CkDistances Met) (Pos : Met → Prop)
    (t₀ : ℝ) (ht₀ : 0 < t₀) (radius : Ioc 0 t₀ → Ioi (0 : ℝ))
    (G : (t : Ioc 0 t₀) → Ioo 0 (radius t).1 → Met) (g : Ioc 0 t₀ → Met) (gprod : Met)
    (hpos : ∀ t, ∃ s₀ > 0, ∀ s : Ioo 0 (radius t).1, (s : ℝ) < s₀ → Pos (G t s))
    (hG : ∀ t j, Tendsto (fun s => D.d j (G t s) (g t)) (comap Subtype.val (𝓝[>] 0)) (𝓝 0))
    (hg : ∀ j, Tendsto (fun t => D.d j (g t) gprod) (comap Subtype.val (𝓝[>] 0)) (𝓝 0)) :
    ∃ (tn : ℕ → Ioc 0 t₀) (sn : (n : ℕ) → Ioo 0 (radius (tn n)).1),
      StrictAnti (fun n => (tn n : ℝ)) ∧ Tendsto (fun n => (tn n : ℝ)) atTop (𝓝[>] 0) ∧
      Tendsto (fun n => (sn n : ℝ)) atTop (𝓝[>] 0) ∧ (∀ n, Pos (G (tn n) (sn n))) ∧
      D.TendstoCInf (fun n => G (tn n) (sn n)) gprod := by
  let tn (n : ℕ) : Ioc 0 t₀ := ⟨t₀ / ((n : ℝ) + 1), by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  have hchoose (n : ℕ) : ∃ s : Ioo 0 (radius (tn n)).1,
      (s : ℝ) < 1 / (n + 1) ∧ Pos (G (tn n) s) ∧
      D.d n (G (tn n) s) (g (tn n)) < 1 / (n + 1) := by
    obtain ⟨s₀, hs₀, hP⟩ := hpos (tn n)
    let L := comap (Subtype.val : Ioo 0 (radius (tn n)).1 → ℝ) (𝓝[>] 0)
    have : L.NeBot := comap_coe_neBot_of_le_principal (le_principal_iff.2
      (Ioo_mem_nhdsGT (radius (tn n)).2))
    have hsmall : ∀ᶠ (s : Ioo 0 (radius (tn n)).1) in L, (s : ℝ) < min s₀ (1 / (n + 1)) :=
      (tendsto_comap.mono_right nhdsWithin_le_nhds).eventually
        (gt_mem_nhds (lt_min hs₀ (by positivity)))
    have hclose := (hG (tn n) n).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (n + 1) by positivity))
    obtain ⟨s, hs, hd⟩ := (hsmall.and hclose).exists
    exact ⟨s, (lt_min_iff.mp hs).2, hP s (lt_min_iff.mp hs).1, hd⟩
  choose sn hsn hsnP hsnd using hchoose
  have hanti : StrictAnti (fun n => (tn n : ℝ)) := by
    intro i j hij
    exact div_lt_div_of_pos_left ht₀ (by positivity) (by exact_mod_cast Nat.add_lt_add_right hij 1)
  -- `t_n → 0⁺`
  have htn0 : Tendsto (fun n => (tn n : ℝ)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, Eventually.of_forall fun n => (tn n).2.1⟩
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul t₀
    rw [mul_zero] at this
    exact Tendsto.congr (fun n => by simp only [tn]; ring) this
  have hsn0 : Tendsto (fun n => (sn n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2
      ⟨squeeze_zero (fun n => (sn n).2.1.le) (fun n => (hsn n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => (sn n).2.1⟩
  refine ⟨tn, sn, hanti, htn0, hsn0, hsnP, fun j => ?_⟩
  have hgn := (hg j).comp (tendsto_comap_iff.2 htn0)
  -- squeeze: `d_j(x_n, g_prod) ≤ 1/(n+1) + d_j(g_{t_n}, g_prod)` for `n ≥ j`
  have hbound : ∀ᶠ n in atTop, D.d j (G (tn n) (sn n)) gprod ≤
      1 / ((n : ℝ) + 1) + D.d j (g (tn n)) gprod := by
    filter_upwards [eventually_ge_atTop j] with n hn
    have h1 := D.triangle j (G (tn n) (sn n)) (g (tn n)) gprod
    have h2 : D.d j (G (tn n) (sn n)) (g (tn n)) ≤ D.d n (G (tn n) (sn n)) (g (tn n)) :=
      D.mono _ _ hn
    have h3 := hsnd n
    linarith
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) + D.d j (g (tn n)) gprod) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.add hgn
  exact squeeze_zero' (Eventually.of_forall fun n => D.nonneg _ _ _) hbound hlim

/-- The metric-sequence conclusion for families supplied on the full real parameter space. -/
theorem diagonal_sequence {Met : Type*} (D : CkDistances Met) (Pos : Met → Prop)
    (G : ℝ → ℝ → Met) (g : ℝ → Met) (gprod : Met) (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hpos : ∀ t ∈ Ioc 0 t₀, ∃ s₀ > 0, ∀ s, 0 < s → s < s₀ → Pos (G t s))
    (hG : ∀ t ∈ Ioc 0 t₀, ∀ j, Tendsto (fun s => D.d j (G t s) (g t)) (𝓝[>] 0) (𝓝 0))
    (hg : ∀ j, Tendsto (fun t => D.d j (g t) gprod) (𝓝[>] 0) (𝓝 0)) :
    ∃ x : ℕ → Met, (∀ n, Pos (x n)) ∧ D.TendstoCInf x gprod := by
  obtain ⟨tn, sn, _, _, _, hp, hd⟩ := diagonal_parameters D Pos t₀ ht₀
    (fun _ => ⟨1, (zero_lt_one : (0 : ℝ) < 1)⟩) (fun t s => G t s) (fun t => g t) gprod
    (fun t => by
      obtain ⟨s₀, hs₀, h⟩ := hpos t t.2
      exact ⟨s₀, hs₀, fun s hs => h s s.2.1 hs⟩)
    (fun t j => (hG t t.2 j).comp tendsto_comap) (fun j => (hg j).comp tendsto_comap)
  exact ⟨fun n => G (tn n) (sn n), hp, hd⟩

end LocalHopf
