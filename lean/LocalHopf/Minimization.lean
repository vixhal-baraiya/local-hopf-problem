/-
Copyright (c) 2026. Released under the MIT License (see ../../LICENSE).

# Lemma 3.1 (minimization), quantitative form

PROOF.md, Lemma 3.1, expands `min_{|z| ≤ δ} F(z, s)` to order `s³`. Theorem 3.4 only uses the
*lower* bound
  `F(z, s) ≥ s² W₂ + s³ W₃ - C s⁴`   for all `|z| ≤ δ`,
and this file proves that lower bound from two explicit estimates which are what the Taylor
expansion of a `C⁴` function provides:

* (a) **coercivity**: `F(z, s) ≥ λ|z|² - A s|z| - A s²`  (from `F(z,0) ≥ λ|z|²`, `F₁(z) = O(|z|)`);
* (b) **rescaled expansion**: for `|ζ| ≤ R`,
      `F(sζ, s) ≥ s² Qf(ζ) + s³ Pf(ζ) - C s⁴`
  with `Qf(ζ) ≥ W₂ + λ'|ζ - z̄|²` and `Pf(ζ) ≥ Pf(z̄) - L|ζ - z̄|`.

It also proves the completing-the-square identity (`complete_square`) given a solution of
`H z̄ = -g`. The modules `UniformTube` and `NormalMinimum` derive these estimates with uniform
constants on compact chart families and prove the two-sided expansion of the fiber minimum.
The `tube` field in `Main.lean` assumes the resulting near-region lower bound and the separate
far-region estimate.

The proof follows PROOF.md: minimizers are `O(s)` (`norm_le_of_small_value`), and the key
inequality is `s²λa² - C s³a ≥ -C² s⁴ / (4λ)` (`quad_lower`).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace LocalHopf

/-- Step 4 of Lemma 3.1: `s² λ a² - C s³ a ≥ -C² s⁴ / (4λ)`. -/
theorem quad_lower {lam : ℝ} (hlam : 0 < lam) (C s a : ℝ) :
    -(C ^ 2 * s ^ 4 / (4 * lam)) ≤ s ^ 2 * lam * a ^ 2 - C * s ^ 3 * a := by
  have e : s ^ 2 * lam * a ^ 2 - C * s ^ 3 * a + C ^ 2 * s ^ 4 / (4 * lam)
      = (2 * lam * s * a - C * s ^ 2) ^ 2 / (4 * lam) := by
    field_simp; ring
  have : 0 ≤ (2 * lam * s * a - C * s ^ 2) ^ 2 / (4 * lam) := by positivity
  linarith

/-- Step 4 of Lemma 3.1, for one rescaled point `ζ`. -/
theorem rescaled_lower_bound {E : Type*} [NormedAddCommGroup E] (W₂ lam L C s : ℝ)
    (hlam : 0 < lam) (hs : 0 ≤ s) (zbar ζ : E) (Qf Pf : E → ℝ)
    (hQf : W₂ + lam * ‖ζ - zbar‖ ^ 2 ≤ Qf ζ) (hPf : Pf zbar - L * ‖ζ - zbar‖ ≤ Pf ζ)
    (val : ℝ) (hval : s ^ 2 * Qf ζ + s ^ 3 * Pf ζ - C * s ^ 4 ≤ val) :
    s ^ 2 * W₂ + s ^ 3 * Pf zbar - (C + L ^ 2 / (4 * lam)) * s ^ 4 ≤ val := by
  set a := ‖ζ - zbar‖
  have hq := quad_lower hlam L s a
  have h2 : s ^ 2 * (W₂ + lam * a ^ 2) ≤ s ^ 2 * Qf ζ :=
    mul_le_mul_of_nonneg_left hQf (by positivity)
  have h3 : s ^ 3 * (Pf zbar - L * a) ≤ s ^ 3 * Pf ζ :=
    mul_le_mul_of_nonneg_left hPf (by positivity)
  have e : (C + L ^ 2 / (4 * lam)) * s ^ 4 = C * s ^ 4 + L ^ 2 * s ^ 4 / (4 * lam) := by ring
  rw [e]
  nlinarith [hq, h2, h3]

/-- Step 1 of Lemma 3.1: points where `F` is at most `B s²` satisfy `|z| ≤ (1 + (2A+B)/λ) s`. -/
theorem norm_le_of_small_value {lam A B s r val : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hlow : lam * r ^ 2 - A * s * r - A * s ^ 2 ≤ val) (hval : val ≤ B * s ^ 2) :
    r ≤ (1 + (2 * A + B) / lam) * s := by
  have hk : 0 ≤ (2 * A + B) / lam := by positivity
  rcases le_or_gt r s with hrs | hrs
  · nlinarith
  · -- `λ r² ≤ A s r + (A + B) s² ≤ (2A + B) s r`
    have hrpos : 0 < r := lt_of_le_of_lt hs hrs
    have hss : s * s ≤ s * r := mul_le_mul_of_nonneg_left hrs.le hs
    have hAB : (A + B) * (s * s) ≤ (A + B) * (s * r) :=
      mul_le_mul_of_nonneg_left hss (add_nonneg hA hB)
    have h1 : lam * r ^ 2 ≤ (2 * A + B) * s * r := by nlinarith
    have h2 : lam * r ≤ (2 * A + B) * s := by
      have := h1; nlinarith
    have h3 : r ≤ (2 * A + B) / lam * s := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam]; linarith
    nlinarith

/-- **Lemma 3.1, lower bound.** Under the coercivity estimate (a) and the rescaled expansion (b),
`F(z, s) ≥ s² W₂ + s³ Pf(z̄) - C' s⁴` for all `|z| ≤ δ` and `0 ≤ s ≤ min(s₀, 1)`, where `W₃ = Pf(z̄)`
and `C' = C + L²/(4λ')`. -/
theorem minimization_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ → ℝ) (δ s₀ lam lam' A C L W₂ : ℝ) (zbar : E) (Qf Pf : E → ℝ)
    (hlam : 0 < lam) (hlam' : 0 < lam') (hA : 0 ≤ A) (hC : 0 ≤ C)
    -- (a) coercivity
    (hcoer : ∀ z s, ‖z‖ ≤ δ → 0 ≤ s → s ≤ s₀ →
      lam * ‖z‖ ^ 2 - A * s * ‖z‖ - A * s ^ 2 ≤ F z s)
    -- (b) rescaled expansion on the ball of radius `R`
    (hexp : ∀ ζ s, ‖ζ‖ ≤ 1 + (2 * A + (|W₂| + |Pf zbar|)) / lam → ‖s • ζ‖ ≤ δ → 0 < s → s ≤ s₀ →
      s ^ 2 * Qf ζ + s ^ 3 * Pf ζ - C * s ^ 4 ≤ F (s • ζ) s)
    (hQf : ∀ ζ, W₂ + lam' * ‖ζ - zbar‖ ^ 2 ≤ Qf ζ)
    (hPf : ∀ ζ, ‖ζ‖ ≤ 1 + (2 * A + (|W₂| + |Pf zbar|)) / lam →
      Pf zbar - L * ‖ζ - zbar‖ ≤ Pf ζ) :
    ∀ z s, ‖z‖ ≤ δ → 0 ≤ s → s ≤ s₀ → s ≤ 1 →
      s ^ 2 * W₂ + s ^ 3 * Pf zbar - (C + L ^ 2 / (4 * lam')) * s ^ 4 ≤ F z s := by
  intro z s hz hs hs₀ hs1
  set B := |W₂| + |Pf zbar| with hBdef
  have hB : 0 ≤ B := by positivity
  set R := 1 + (2 * A + B) / lam
  have hC' : 0 ≤ C + L ^ 2 / (4 * lam') := by positivity
  -- the target is at most `B s²` (uses `s ≤ 1`)
  have htarget : s ^ 2 * W₂ + s ^ 3 * Pf zbar - (C + L ^ 2 / (4 * lam')) * s ^ 4 ≤ B * s ^ 2 := by
    have h1 : s ^ 2 * W₂ ≤ s ^ 2 * |W₂| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    have h2 : s ^ 3 * Pf zbar ≤ s ^ 2 * |Pf zbar| := by
      have : s ^ 3 ≤ s ^ 2 := by nlinarith [pow_nonneg hs 2]
      calc s ^ 3 * Pf zbar ≤ s ^ 3 * |Pf zbar| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        _ ≤ s ^ 2 * |Pf zbar| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have h3 : 0 ≤ (C + L ^ 2 / (4 * lam')) * s ^ 4 := by positivity
    rw [hBdef]; nlinarith
  by_cases hzR : ‖z‖ ≤ R * s
  · -- minimizer region: rescale `z = s ζ`
    rcases eq_or_lt_of_le hs with h0 | hspos
    · -- `s = 0` forces `z = 0`
      subst h0
      have hz0 : ‖z‖ = 0 := le_antisymm (by simpa using hzR) (norm_nonneg _)
      have := hcoer z 0 hz le_rfl hs₀
      simp [hz0] at this ⊢
      linarith
    · set ζ := s⁻¹ • z
      have hzζ : s • ζ = z := by simp [ζ, smul_smul, hspos.ne']
      have hζR : ‖ζ‖ ≤ R := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hspos, inv_mul_le_iff₀ hspos]
        linarith [hzR, mul_comm R s]
      have hF := hexp ζ s hζR (by rwa [hzζ]) hspos hs₀
      rw [hzζ] at hF
      exact rescaled_lower_bound W₂ lam' L C s hlam' hs zbar ζ Qf Pf (hQf ζ) (hPf ζ hζR) _ hF
  · -- far from the origin `F > B s²` by step 1
    push Not at hzR
    by_contra hcon
    push Not at hcon
    have := norm_le_of_small_value hlam hA hB hs (hcoer z s hz hs hs₀)
      (le_trans hcon.le htarget)
    linarith

/-- **Completing the square** (definition of `W₂` and `z̄` in Lemma 3.1). If `H` is symmetric and
`H z̄ = -g`, then `F₂ + ⟨g, ζ⟩ + ½⟨ζ, Hζ⟩ = W₂ + ½⟨ζ - z̄, H(ζ - z̄)⟩` with `W₂ = F₂ + ½⟨g, z̄⟩`. -/
theorem complete_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →ₗ[ℝ] E) (hH : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y)) (g zbar : E)
    (hz : H zbar = -g) (F₂ : ℝ) (ζ : E) :
    F₂ + inner ℝ g ζ + (1 / 2) * inner ℝ ζ (H ζ)
      = (F₂ + (1 / 2) * inner ℝ g zbar) + (1 / 2) * inner ℝ (ζ - zbar) (H (ζ - zbar)) := by
  have e1 : inner ℝ ζ (H zbar) = - inner ℝ g ζ := by
    rw [hz, inner_neg_right, real_inner_comm]
  have e2 : inner ℝ zbar (H ζ) = - inner ℝ g ζ := by
    rw [← hH, hz, inner_neg_left]
  have e3 : inner ℝ zbar (H zbar) = - inner ℝ g zbar := by
    rw [hz, inner_neg_right, real_inner_comm]
  simp only [map_sub, inner_sub_left, inner_sub_right, e1, e2, e3]
  ring

/-- With a coercive Hessian, `Qf(ζ) ≥ W₂ + λ|ζ - z̄|²` (hypothesis `hQf` above). -/
theorem complete_square_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →ₗ[ℝ] E) (hH : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y)) (g zbar : E)
    (hz : H zbar = -g) (F₂ lam : ℝ) (hcoer : ∀ x, 2 * lam * ‖x‖ ^ 2 ≤ inner ℝ x (H x)) (ζ : E) :
    (F₂ + (1 / 2) * inner ℝ g zbar) + lam * ‖ζ - zbar‖ ^ 2
      ≤ F₂ + inner ℝ g ζ + (1 / 2) * inner ℝ ζ (H ζ) := by
  rw [complete_square H hH g zbar hz F₂ ζ]
  have := hcoer (ζ - zbar)
  linarith

end LocalHopf
