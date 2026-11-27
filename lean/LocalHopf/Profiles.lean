/-
Copyright (c) 2026. Released under the MIT License (see ../../LICENSE).

# Closed-form facts about the scalar profiles (sections 2, 5, 6 and DERIVATIONS.md)

Everything here is an exact identity or inequality between explicit rational
functions, proved from scratch:

* `weight_ode`            : `P₀, Q` solve the soft-gradient ODE of DERIVATIONS §2.
* `D_ge_h`, `D_pos`       : `D = (1+t)² - t²u² ≥ h = 1 + 2t > 0`, so `φ_t, ψ_t, h_cd` are smooth.
* `normalCorrection_denom_pos` : the denominators of `M_t, N_t` are positive.
* `varphi_pos`            : `φ_t > 0`.
* `dd_weight_at_one`      : the `d,d` weight `1/(4h)` equals the Brendle–Hung weight `1/12` at `t = 1`.
* `Mt_zero_ne`            : the odd slope `λ_d M_t(0)` of DERIVATIONS §4 is nonzero.
* `bh_cd_defect_ne`       : the Brendle–Hung `c,d` defect of DERIVATIONS §5 is nonzero on `0 < t < 1`.
* `A0B0_eq`, `A0B0_lt`    : `|A₀|² + |B₀|²` has the closed form of §5 and is `< 100` on `[-1, 1]`.
* `cubic_mean_eq`         : `μ_t = λ_c λ_d² / (4h²) = 1 / (40000 h²)` (Prop. 6.1).
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace LocalHopf.Profiles

noncomputable section

/-- The perturbation amplitudes `λ_c = 1/100`, `λ_d = 1/10` of section 2. -/
def lamC : ℝ := 1 / 100
def lamD : ℝ := 1 / 10

/-- `h = 1 + 2t`. -/
def hh (t : ℝ) : ℝ := 1 + 2 * t

/-- First-order weights at `t = 0` (DERIVATIONS §2). -/
def P0 (u : ℝ) : ℝ := 16 / 5 + u / 2 - 2 * u ^ 2 / 5
def Q (u : ℝ) : ℝ := 2 * u ^ 2 - 7 * u / 10 - 4

/-- `P_t(u) = P₀(u) (1 - t²(1+u)²)`. -/
def Pt (t u : ℝ) : ℝ := P0 u * (1 - t ^ 2 * (1 + u) ^ 2)

theorem Pt_zero (u : ℝ) : Pt 0 u = P0 u := by simp [Pt]

theorem hasDerivAt_P0 (u : ℝ) : HasDerivAt P0 (1 / 2 - 4 * u / 5) u := by
  have h := (((hasDerivAt_id u).div_const 2).const_add (16 / 5 : ℝ)).sub
    (((hasDerivAt_pow 2 u).const_mul (2 : ℝ)).div_const 5)
  convert h using 1
  · funext v; simp [P0, mul_div_assoc]
  · simp; ring

theorem hasDerivAt_P0' (u : ℝ) : HasDerivAt (fun v => 1 / 2 - 4 * v / 5) (-4 / 5) u := by
  have h := ((hasDerivAt_id u).const_mul (4 : ℝ)).div_const 5 |>.const_sub (1 / 2 : ℝ)
  convert h using 1
  · funext v; simp
  · simp; ring

/-- `(1-u) Q(u) = -2u³ + 27u²/10 + 33u/10 - 4`, with derivative `-6u² + 27u/5 + 33/10`. -/
theorem hasDerivAt_oneSubQ (u : ℝ) :
    HasDerivAt (fun v => (1 - v) * Q v) (-6 * u ^ 2 + 27 * u / 5 + 33 / 10) u := by
  have e : (fun v : ℝ => (1 - v) * Q v) = fun v => -2 * v ^ 3 + 27 / 10 * v ^ 2 + 33 / 10 * v - 4 := by
    funext v; simp [Q]; ring
  rw [e]
  have h := ((((hasDerivAt_pow 3 u).const_mul (-2 : ℝ)).add
    ((hasDerivAt_pow 2 u).const_mul (27 / 10 : ℝ))).add
    ((hasDerivAt_id u).const_mul (33 / 10 : ℝ))).sub_const (4 : ℝ)
  exact h.congr_deriv (by norm_num; ring)

/-- **DERIVATIONS §2.** The weights `P₀, Q` satisfy
`2(1-u²) P'' + (3-5u) P' - P + ((1-u) Q)' = 0`, the condition that the tilt gradient along the
product-flat direction vanishes at `t = 0`. -/
theorem weight_ode (u : ℝ) :
    2 * (1 - u ^ 2) * deriv (deriv P0) u + (3 - 5 * u) * deriv P0 u - P0 u
      + deriv (fun v => (1 - v) * Q v) u = 0 := by
  have d1 : deriv P0 = fun v => 1 / 2 - 4 * v / 5 := funext fun v => (hasDerivAt_P0 v).deriv
  rw [d1, (hasDerivAt_P0' u).deriv, (hasDerivAt_oneSubQ u).deriv]
  simp [P0]; ring

/-- `D = (1+t)² - t²u²`. -/
def D (t u : ℝ) : ℝ := (1 + t) ^ 2 - t ^ 2 * u ^ 2

/-- `D ≥ h` for `|u| ≤ 1` (section 2). -/
theorem D_ge_h (t u : ℝ) (hu : u ^ 2 ≤ 1) : hh t ≤ D t u := by
  unfold D hh; nlinarith [sq_nonneg t]

theorem hh_pos {t : ℝ} (ht : 0 ≤ t) : 0 < hh t := by unfold hh; linarith

theorem D_pos {t u : ℝ} (ht : 0 ≤ t) (hu : u ^ 2 ≤ 1) : 0 < D t u :=
  lt_of_lt_of_le (hh_pos ht) (D_ge_h t u hu)

/-- `φ_t = ((1+t)² + t²u²) / (h D²)`. -/
def varphi (t u : ℝ) : ℝ := ((1 + t) ^ 2 + t ^ 2 * u ^ 2) / (hh t * D t u ^ 2)

/-- `ψ_t = -(1+t)(h² + 6ht²u² + t⁴(u⁴-1)) / (h² D³)`. -/
def psi (t u : ℝ) : ℝ :=
  -((1 + t) * (hh t ^ 2 + 6 * hh t * t ^ 2 * u ^ 2 + t ^ 4 * (u ^ 4 - 1))) / (hh t ^ 2 * D t u ^ 3)

theorem varphi_pos {t u : ℝ} (ht : 0 ≤ t) (hu : u ^ 2 ≤ 1) : 0 < varphi t u := by
  unfold varphi
  have := D_pos ht hu
  have := hh_pos ht
  positivity

/-- The denominators `80 h² (1 + t(1+u))` and `80 h² (1 + t(1+u))²` of `M_t, N_t` are positive
for `t ≥ 0`, `u ∈ [-1, 1]`, so `h_ad, h_bd` are smooth. -/
theorem normalCorrection_denom_pos {t u : ℝ} (ht : 0 ≤ t) (hu : -1 ≤ u) :
    0 < 80 * hh t ^ 2 * (1 + t * (1 + u)) ∧ 0 < 80 * hh t ^ 2 * (1 + t * (1 + u)) ^ 2 := by
  have h1 : 0 < 1 + t * (1 + u) := by nlinarith
  have := hh_pos ht
  constructor <;> positivity

/-- **DERIVATIONS §3.** The `d,d` weight `1/(4h)` agrees with the Brendle–Hung weight `1/12`
at `t = 1`. -/
theorem dd_weight_at_one : 1 / (4 * hh 1) = 1 / 12 := by norm_num [hh]

/-- **DERIVATIONS §4.** `M_t(0) = -(106t³ + 37t² + 18t + 67) / (40 (1+t)(1+2t)²)`. -/
def Mt0 (t : ℝ) : ℝ := -(106 * t ^ 3 + 37 * t ^ 2 + 18 * t + 67) / (40 * (1 + t) * (1 + 2 * t) ^ 2)

/-- The odd slope `λ_d M_t(0)` is nonzero for every `t ≥ 0`, so the normal correction of `h_bd`
is necessary. -/
theorem Mt_zero_ne {t : ℝ} (ht : 0 ≤ t) : lamD * Mt0 t ≠ 0 := by
  unfold Mt0 lamD
  have hnum : 0 < 106 * t ^ 3 + 37 * t ^ 2 + 18 * t + 67 := by positivity
  have hden : 0 < 40 * (1 + t) * (1 + 2 * t) ^ 2 := by positivity
  have : -(106 * t ^ 3 + 37 * t ^ 2 + 18 * t + 67) / (40 * (1 + t) * (1 + 2 * t) ^ 2) < 0 :=
    div_neg_of_neg_of_pos (by linarith) hden
  exact mul_ne_zero (by norm_num) this.ne

/-- **DERIVATIONS §5.** The `c,d` normal-derivative coefficient of the Brendle–Hung tensor `h_cd`,
`(1-t)(3t+1) / (4(1+t)²(1+2t)²)`, is nonzero for `0 < t < 1`. -/
theorem bh_cd_defect_ne {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (1 - t) * (3 * t + 1) / (4 * (1 + t) ^ 2 * (1 + 2 * t) ^ 2) ≠ 0 := by
  have : 0 < (1 - t) * (3 * t + 1) / (4 * (1 + t) ^ 2 * (1 + 2 * t) ^ 2) := by
    apply div_pos
    · apply mul_pos <;> linarith
    · positivity
  exact this.ne'

/-- The `λ_c`-channel profile at `t = 0` (DERIVATIONS §6):
`f(v) = (-168v³ + 154v² + 148v - 99) / 20`. -/
def fc (v : ℝ) : ℝ := (-168 * v ^ 3 + 154 * v ^ 2 + 148 * v - 99) / 20

/-- With `A₀ = f(u)(p₂+p₁)`, `B₀ = f(-u)(p₂-p₁)` and `|p₂ ± p₁|² = 2 ± 2u`,
`|A₀|² + |B₀|² = (9801 - 37892u² + 52836u⁴ - 23520u⁶)/100`, as stated in section 5. -/
theorem A0B0_eq (u : ℝ) :
    fc u ^ 2 * (2 + 2 * u) + fc (-u) ^ 2 * (2 - 2 * u)
      = (9801 - 37892 * u ^ 2 + 52836 * u ^ 4 - 23520 * u ^ 6) / 100 := by
  unfold fc; ring

/-- `|A₀|² + |B₀|² < 100` on `[-1, 1]` (section 5). -/
theorem A0B0_lt {u : ℝ} (hu : u ^ 2 ≤ 1) :
    (9801 - 37892 * u ^ 2 + 52836 * u ^ 4 - 23520 * u ^ 6) / 100 < 100 := by
  set x := u ^ 2 with hx
  have hx0 : 0 ≤ x := sq_nonneg u
  have h4 : u ^ 4 = x ^ 2 := by rw [hx]; ring
  have h6 : u ^ 6 = x ^ 3 := by rw [hx]; ring
  rw [h4, h6]
  -- `-199 - 37892x + 52836x² - 23520x³ = -199 - x q(x)` with `q > 0`:
  -- `x q(x) = 23520 x (x - c)² + (52825.92 - 52836) x² + (37892 - 23520 c²) x`, `c = 1.123`.
  nlinarith [mul_nonneg hx0 (sub_nonneg.2 hu), mul_nonneg hx0 (sq_nonneg (x - 1123 / 1000))]

/-- **Proposition 6.1 (value).** `μ_t = λ_c λ_d² / (4h²) = 1 / (40000 h²)`. -/
def mu (t : ℝ) : ℝ := lamC * lamD ^ 2 / (4 * hh t ^ 2)

theorem cubic_mean_eq (t : ℝ) : mu t = 1 / (40000 * hh t ^ 2) := by
  unfold mu lamC lamD
  rcases eq_or_ne (hh t) 0 with h | h
  · simp [h]
  · field_simp; ring

theorem mu_pos {t : ℝ} (ht : 0 ≤ t) : 0 < mu t := by
  rw [cubic_mean_eq]; have := hh_pos ht; positivity

end

end LocalHopf.Profiles
