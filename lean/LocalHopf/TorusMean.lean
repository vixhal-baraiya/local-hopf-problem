/-
Copyright (c) 2026. Released under the MIT License (see ../../LICENSE).

# Section 6: the rotation mean of the cubic coefficient

On the equatorial torus, rotating the fixed axes about `e_z` by `φ` turns `V⁽³⁾` into a
trigonometric polynomial of degree `≤ 3` in `φ` (each first-order tensor carries at most one factor
of `e_x, e_y`, each second-order tensor at most two). PROOF.md then computes its mean from the four
rotations `φ ∈ {0, π/2, π, 3π/2}`. This file proves that step: for a trigonometric polynomial of
degree `≤ 3`, the four-point average and the mean `(1/2π) ∫₀^{2π}` both equal the constant term.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace LocalHopf

open Real intervalIntegral

/-- A real trigonometric polynomial of degree `≤ 3`. -/
noncomputable def trig3 (a₀ a₁ b₁ a₂ b₂ a₃ b₃ φ : ℝ) : ℝ :=
  a₀ + a₁ * cos φ + b₁ * sin φ + a₂ * cos (2 * φ) + b₂ * sin (2 * φ)
    + a₃ * cos (3 * φ) + b₃ * sin (3 * φ)

/-- The average over the four rotations `0, π/2, π, 3π/2` is the constant term. -/
theorem trig3_four_point_mean (a₀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) :
    (trig3 a₀ a₁ b₁ a₂ b₂ a₃ b₃ 0 + trig3 a₀ a₁ b₁ a₂ b₂ a₃ b₃ (π / 2)
      + trig3 a₀ a₁ b₁ a₂ b₂ a₃ b₃ π + trig3 a₀ a₁ b₁ a₂ b₂ a₃ b₃ (3 * π / 2)) / 4 = a₀ := by
  simp only [trig3, cos_two_mul, sin_two_mul, cos_three_mul, sin_three_mul]
  rw [show 3 * π / 2 = π / 2 + π by ring]
  simp [cos_add_pi, sin_add_pi]
  ring

theorem integral_cos_nat_mul (n : ℕ) (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..2 * π, cos ((n : ℝ) * x) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) hn', integral_cos]
  have : (n : ℝ) * (2 * π) = ((2 * n : ℕ) : ℝ) * π := by push_cast; ring
  simp only [this, mul_zero, sin_zero, sub_zero, smul_eq_mul, sin_nat_mul_pi]

theorem integral_sin_nat_mul (n : ℕ) (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..2 * π, sin ((n : ℝ) * x) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [intervalIntegral.integral_comp_mul_left (fun x => sin x) hn', integral_sin]
  have : (n : ℝ) * (2 * π) = ((2 * n : ℕ) : ℝ) * π := by push_cast; ring
  have hc : cos (((2 * n : ℕ) : ℝ) * π) = 1 := by rw [cos_nat_mul_pi, pow_mul]; norm_num
  simp only [this, hc, mul_zero, cos_zero, sub_self, smul_eq_mul]

/-- The mean `(1/2π) ∫₀^{2π}` is the constant term. -/
theorem trig3_integral_mean (a₀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) :
    (∫ φ in (0 : ℝ)..2 * π, trig3 a₀ a₁ b₁ a₂ b₂ a₃ b₃ φ) / (2 * π) = a₀ := by
  have c : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f MeasureTheory.volume 0 (2 * π) :=
    fun f hf => hf.intervalIntegrable _ _
  have hc1 := integral_cos_nat_mul 1 one_ne_zero
  have hc2 := integral_cos_nat_mul 2 two_ne_zero
  have hc3 := integral_cos_nat_mul 3 (by norm_num)
  have hs1 := integral_sin_nat_mul 1 one_ne_zero
  have hs2 := integral_sin_nat_mul 2 two_ne_zero
  have hs3 := integral_sin_nat_mul 3 (by norm_num)
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at hc1 hc2 hc3 hs1 hs2 hs3
  unfold trig3
  rw [integral_add (c _ (by fun_prop)) (c _ (by fun_prop)),
    integral_add (c _ (by fun_prop)) (c _ (by fun_prop)),
    integral_add (c _ (by fun_prop)) (c _ (by fun_prop)),
    integral_add (c _ (by fun_prop)) (c _ (by fun_prop)),
    integral_add (c _ (by fun_prop)) (c _ (by fun_prop)),
    integral_add (c _ (by fun_prop)) (c _ (by fun_prop))]
  simp only [integral_const_mul, hc1, hc2, hc3, hs1, hs2, hs3, intervalIntegral.integral_const,
    smul_eq_mul, sub_zero, mul_zero, add_zero]
  field_simp

end LocalHopf
