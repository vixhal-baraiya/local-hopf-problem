/-
Copyright (c) 2026. Released under the MIT License (see ../../LICENSE).

# Proposition 5.2: from the normal form of `V⁽²⁾` to the bound `V⁽²⁾ ≥ ρ 𝒢`

Proposition 5.1 (certified by `full_metric_check.py`, part A) writes the quadratic coefficient at
a regular pair as
  `V⁽²⁾ = n_x² F^x + n_y² F^y + λ_c n_z [n_x A·z' + n_y B·z'] + λ_d² [2 n_z n_x x'ᵀM¹z' + n_x² z'ᵀM²z']`,
where `n` is the unit normal, `z', x'` are the projections of `e_z, e_x` to the plane of `Γ`, and
`ρ = n_x² + n_y² = |z'|²`. PROOF.md then deduces `V⁽²⁾ ≥ ρ 𝒢` with
  `𝒢 = min(F^x, F^y) - λ_c √(|A|² + |B|²) - λ_d² (2|M¹|_F + |M²|_F)`.

`V2_ge_rho_G` is that deduction, with all Cauchy–Schwarz and Frobenius-norm steps proved.
The numerical input `𝒢 ≥ 3/10` (ball arithmetic in `t0_certificate.py`) enters only in
`V2_ge_kappa_rho`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace LocalHopf

open Matrix Finset

/-- The Frobenius norm `|M|_F`. -/
noncomputable def frob {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

theorem dot_self_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- Cauchy–Schwarz for `⬝ᵥ`. -/
theorem dot_sq_le {n : ℕ} (x y : Fin n → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) x y
  simpa [dotProduct, sq] using h

/-- `(xᵀ M z)² ≤ |M|_F² |x|² |z|²`. -/
theorem bilin_sq_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (z : Fin n → ℝ) :
    (x ⬝ᵥ (M *ᵥ z)) ^ 2 ≤ (∑ i, ∑ j, M i j ^ 2) * ((x ⬝ᵥ x) * (z ⬝ᵥ z)) := by
  have e1 : x ⬝ᵥ (M *ᵥ z) = ∑ p : Fin m × Fin n, M p.1 p.2 * (x p.1 * z p.2) := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ p : Fin m × Fin n, M p.1 p.2 ^ 2 = ∑ i, ∑ j, M i j ^ 2 :=
    Fintype.sum_prod_type _
  have e3 : ∑ p : Fin m × Fin n, (x p.1 * z p.2) ^ 2 = (x ⬝ᵥ x) * (z ⬝ᵥ z) := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, ← e2, ← e3]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem frob_sq {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    frob M ^ 2 = ∑ i, ∑ j, M i j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem frob_nonneg {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frob M := Real.sqrt_nonneg _

theorem abs_le_of_sq_le {y b : ℝ} (hb : 0 ≤ b) (h : y ^ 2 ≤ b ^ 2) : |y| ≤ b := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hb] at this

/-- The normal form of Proposition 5.1. -/
def V2form (lamC lamD Fx Fy nx ny nz : ℝ) (A B x' z' : Fin 2 → ℝ)
    (M1 M2 : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  nx ^ 2 * Fx + ny ^ 2 * Fy + lamC * nz * (nx * (A ⬝ᵥ z') + ny * (B ⬝ᵥ z'))
    + lamD ^ 2 * (2 * nz * nx * (x' ⬝ᵥ (M1 *ᵥ z')) + nx ^ 2 * (z' ⬝ᵥ (M2 *ᵥ z')))

/-- `𝒢 = min(F^x, F^y) - λ_c √(|A|² + |B|²) - λ_d² (2|M¹|_F + |M²|_F)`. -/
noncomputable def Gcal (lamC lamD Fx Fy : ℝ) (A B : Fin 2 → ℝ)
    (M1 M2 : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  min Fx Fy - lamC * Real.sqrt (A ⬝ᵥ A + B ⬝ᵥ B) - lamD ^ 2 * (2 * frob M1 + frob M2)

/-- **Proposition 5.2, deduction step.** For a unit normal `n` with `ρ = n_x² + n_y² = |z'|²` and
`|x'| ≤ 1`, the normal form satisfies `V⁽²⁾ ≥ ρ 𝒢`. -/
theorem V2_ge_rho_G (lamC lamD Fx Fy nx ny nz ρ : ℝ) (A B x' z' : Fin 2 → ℝ)
    (M1 M2 : Matrix (Fin 2) (Fin 2) ℝ) (hlamC : 0 ≤ lamC)
    (hρ : nx ^ 2 + ny ^ 2 = ρ) (hunit : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1)
    (hz' : z' ⬝ᵥ z' = ρ) (hx' : x' ⬝ᵥ x' ≤ 1) :
    ρ * Gcal lamC lamD Fx Fy A B M1 M2 ≤ V2form lamC lamD Fx Fy nx ny nz A B x' z' M1 M2 := by
  have hρ0 : 0 ≤ ρ := hz' ▸ dot_self_nonneg z'
  have hnx : nx ^ 2 ≤ ρ := by nlinarith [sq_nonneg ny]
  have hρ1 : ρ ≤ 1 := by nlinarith [sq_nonneg nz]
  have hnz : nz ^ 2 ≤ 1 := by nlinarith [sq_nonneg nx, sq_nonneg ny]
  have hnzabs : |nz| ≤ 1 := abs_le_of_sq_le zero_le_one (by simpa using hnz)
  -- (1) the diagonal part
  set μ := min Fx Fy
  have T1 : ρ * μ ≤ nx ^ 2 * Fx + ny ^ 2 * Fy := by
    have a1 : nx ^ 2 * μ ≤ nx ^ 2 * Fx := mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
    have a2 : ny ^ 2 * μ ≤ ny ^ 2 * Fy := mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _)
    rw [← hρ]; linarith
  -- (2) the `λ_c` part: `|n_x A·z' + n_y B·z'| ≤ ρ √(|A|² + |B|²)`
  set S := Real.sqrt (A ⬝ᵥ A + B ⬝ᵥ B)
  have hSnn : 0 ≤ A ⬝ᵥ A + B ⬝ᵥ B := add_nonneg (dot_self_nonneg A) (dot_self_nonneg B)
  have hS2 : S ^ 2 = A ⬝ᵥ A + B ⬝ᵥ B := Real.sq_sqrt hSnn
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set α := A ⬝ᵥ z'
  set β := B ⬝ᵥ z'
  have hα : α ^ 2 ≤ (A ⬝ᵥ A) * ρ := hz' ▸ dot_sq_le A z'
  have hβ : β ^ 2 ≤ (B ⬝ᵥ B) * ρ := hz' ▸ dot_sq_le B z'
  set y := nx * α + ny * β
  have hy2 : y ^ 2 ≤ (ρ * S) ^ 2 := by
    have cs : y ^ 2 ≤ (nx ^ 2 + ny ^ 2) * (α ^ 2 + β ^ 2) := by
      nlinarith [sq_nonneg (nx * β - ny * α)]
    rw [hρ] at cs
    have : (nx ^ 2 + ny ^ 2) * (α ^ 2 + β ^ 2) ≤ ρ * (ρ * (A ⬝ᵥ A + B ⬝ᵥ B)) := by
      rw [hρ]; apply mul_le_mul_of_nonneg_left _ hρ0; nlinarith
    rw [hρ] at this
    calc y ^ 2 ≤ ρ * (α ^ 2 + β ^ 2) := cs
      _ ≤ ρ * (ρ * (A ⬝ᵥ A + B ⬝ᵥ B)) := this
      _ = (ρ * S) ^ 2 := by rw [mul_pow, hS2]; ring
  have hy : |y| ≤ ρ * S := abs_le_of_sq_le (mul_nonneg hρ0 hS0) hy2
  have T2 : -(lamC * (ρ * S)) ≤ lamC * nz * y := by
    have h1 : |nz * y| ≤ ρ * S := by
      rw [abs_mul]; calc |nz| * |y| ≤ 1 * |y| := mul_le_mul_of_nonneg_right hnzabs (abs_nonneg _)
        _ ≤ ρ * S := by rw [one_mul]; exact hy
    have h2 := neg_abs_le (nz * y)
    have h3 : -(lamC * (ρ * S)) ≤ lamC * (nz * y) := by
      rw [← mul_neg]; apply mul_le_mul_of_nonneg_left _ hlamC; linarith
    linarith [mul_assoc lamC nz y]
  -- (3) the `λ_d²` part
  set f1 := frob M1
  set f2 := frob M2
  set μ1 := x' ⬝ᵥ (M1 *ᵥ z')
  set μ2 := z' ⬝ᵥ (M2 *ᵥ z')
  have hμ1 : (nz * nx * μ1) ^ 2 ≤ (ρ * f1) ^ 2 := by
    have b := bilin_sq_le M1 x' z'
    rw [← frob_sq, hz'] at b
    have b' : μ1 ^ 2 ≤ f1 ^ 2 * ρ := by
      calc μ1 ^ 2 ≤ f1 ^ 2 * ((x' ⬝ᵥ x') * ρ) := b
        _ ≤ f1 ^ 2 * (1 * ρ) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right hx' hρ0
        _ = f1 ^ 2 * ρ := by ring
    calc (nz * nx * μ1) ^ 2 = nz ^ 2 * (nx ^ 2 * μ1 ^ 2) := by ring
      _ ≤ 1 * (ρ * (f1 ^ 2 * ρ)) := by
          apply mul_le_mul hnz _ (by positivity) zero_le_one
          exact mul_le_mul hnx b' (sq_nonneg _) hρ0
      _ = (ρ * f1) ^ 2 := by ring
  have hμ2 : μ2 ^ 2 ≤ (f2 * ρ) ^ 2 := by
    have b := bilin_sq_le M2 z' z'
    rw [← frob_sq, hz'] at b
    calc μ2 ^ 2 ≤ f2 ^ 2 * (ρ * ρ) := b
      _ = (f2 * ρ) ^ 2 := by ring
  have hf1 : 0 ≤ f1 := frob_nonneg M1
  have hf2 : 0 ≤ f2 := frob_nonneg M2
  have a1 : |nz * nx * μ1| ≤ ρ * f1 := abs_le_of_sq_le (mul_nonneg hρ0 hf1) hμ1
  have a2 : |μ2| ≤ f2 * ρ := abs_le_of_sq_le (mul_nonneg hf2 hρ0) hμ2
  have a3 : |nx ^ 2 * μ2| ≤ ρ * f2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg nx)]
    have hnx1 : nx ^ 2 ≤ 1 := le_trans hnx hρ1
    calc nx ^ 2 * |μ2| ≤ 1 * (f2 * ρ) :=
          mul_le_mul hnx1 a2 (abs_nonneg _) zero_le_one
      _ = ρ * f2 := by ring
  have T3 : -(lamD ^ 2 * (ρ * (2 * f1 + f2))) ≤
      lamD ^ 2 * (2 * nz * nx * μ1 + nx ^ 2 * μ2) := by
    have inner : -(ρ * (2 * f1 + f2)) ≤ 2 * nz * nx * μ1 + nx ^ 2 * μ2 := by
      have := neg_abs_le (nz * nx * μ1)
      have := neg_abs_le (nx ^ 2 * μ2)
      nlinarith
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left inner (sq_nonneg lamD)
  -- (4) combine
  unfold V2form Gcal
  have : ρ * (μ - lamC * S - lamD ^ 2 * (2 * f1 + f2))
      = ρ * μ - lamC * (ρ * S) - lamD ^ 2 * (ρ * (2 * f1 + f2)) := by ring
  rw [this]
  linarith [T1, T2, T3]

/-- **Proposition 5.2.** If the certified bound `𝒢 ≥ κ₂` holds, then `V⁽²⁾ ≥ κ₂ ρ`. -/
theorem V2_ge_kappa_rho (lamC lamD Fx Fy nx ny nz ρ κ₂ : ℝ) (A B x' z' : Fin 2 → ℝ)
    (M1 M2 : Matrix (Fin 2) (Fin 2) ℝ) (hlamC : 0 ≤ lamC)
    (hρ : nx ^ 2 + ny ^ 2 = ρ) (hunit : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1)
    (hz' : z' ⬝ᵥ z' = ρ) (hx' : x' ⬝ᵥ x' ≤ 1)
    (hcert : κ₂ ≤ Gcal lamC lamD Fx Fy A B M1 M2) :
    κ₂ * ρ ≤ V2form lamC lamD Fx Fy nx ny nz A B x' z' M1 M2 := by
  have hρ0 : 0 ≤ ρ := hz' ▸ dot_self_nonneg z'
  calc κ₂ * ρ ≤ Gcal lamC lamD Fx Fy A B M1 M2 * ρ := mul_le_mul_of_nonneg_right hcert hρ0
    _ = ρ * Gcal lamC lamD Fx Fy A B M1 M2 := mul_comm _ _
    _ ≤ _ := V2_ge_rho_G lamC lamD Fx Fy nx ny nz ρ A B x' z' M1 M2 hlamC hρ hunit hz' hx'

end LocalHopf
