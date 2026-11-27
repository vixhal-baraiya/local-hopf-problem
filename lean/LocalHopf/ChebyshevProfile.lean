import LocalHopf.Profiles
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Smoothness of the infinite Chebyshev profile of §2, including the endpoints -/
namespace LocalHopf.Profiles
open Polynomial Set
open scoped ContDiff
noncomputable section

def chebK : ℝ := 4 - Real.sqrt 15

private theorem k_bounds : 0 < chebK ∧ chebK < 1/5 := by
  unfold chebK
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)
  constructor <;> nlinarith [Real.sqrt_nonneg 15]

private def T (n : ℕ) (z : ℂ) := (Chebyshev.T ℂ n).eval z

private theorem cheb_bound {z : ℂ} (hz : ‖z‖ < 2) (n : ℕ) : ‖T n z‖ ≤ (5:ℝ)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [T]
  | one => simpa [T] using (show ‖z‖ ≤ 5 by linarith)
  | more n hn hn' =>
    have h : T (n+2) z = 2*z*T (n+1) z - T n z := by simp [T, Nat.cast_add]
    rw [h]
    calc
      _ ≤ ‖2*z*T (n+1) z‖ + ‖T n z‖ := norm_sub_le ..
      _ ≤ 2 * 2 * (5:ℝ)^(n+1) + 5^n := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat]
        gcongr
      _ ≤ _ := by rw [pow_succ (5:ℝ) (n+1), pow_succ (5:ℝ) n]; nlinarith [pow_pos (by norm_num : 0 < (5:ℝ)) n]

private def term (n : ℕ) (z : ℂ) : ℂ :=
  (chebK : ℂ)^(n+1) * T (n+1) z / ((n+1 : ℕ) : ℂ)^2

private theorem term_bound {z : ℂ} (hz : ‖z‖ < 2) (n : ℕ) :
    ‖term n z‖ ≤ (5 * chebK)^(n+1) := by
  have hn : (1:ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 n
  unfold term
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos k_bounds.1,
    norm_pow, Complex.norm_natCast]
  apply le_trans (div_le_self (mul_nonneg (pow_nonneg k_bounds.1.le _) (norm_nonneg _)) (by nlinarith : 1 ≤ ((n+1 : ℕ):ℝ)^2))
  rw [mul_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (cheb_bound hz _) (pow_nonneg k_bounds.1.le _)

private def complexTail (z : ℂ) := ∑' n : ℕ, term n z

private theorem tail_analytic {z : ℂ} (hz : ‖z‖ < 2) : AnalyticAt ℂ complexTail z := by
  let U := Metric.ball (0 : ℂ) 2
  have hs : Summable (fun n : ℕ => (5 * chebK)^(n+1)) := by
    apply (summable_nat_add_iff 1).mpr
    exact summable_geometric_of_lt_one (by positivity [k_bounds.1]) (by linarith [k_bounds.2])
  have hd : DifferentiableOn ℂ complexTail U :=
    Complex.differentiableOn_tsum_of_summable_norm hs (fun n => by unfold term T; fun_prop)
      Metric.isOpen_ball (fun n z h => term_bound (by simpa [U] using h) n)
  exact hd.analyticOnNhd Metric.isOpen_ball z (by simpa [U] using hz)

/-- Real Chebyshev series with the six finite coefficients and the geometrically
decaying tail from §2. The complexification supplies a neighborhood of both endpoints. -/
def fbb (u : ℝ) : ℝ :=
  let Tn (n : ℕ) := (Chebyshev.T ℝ n).eval u
  2203841/1920*Tn 1 + 5579141/153600*Tn 2 + 214597/103680*Tn 3 +
    48211/307200*Tn 4 + 251/19200*Tn 5 + 25/165888*Tn 6 -
    (42025/6 * Real.sqrt (5/3)) * (complexTail u).re

theorem smoothAt_fbb {u : ℝ} (hu : |u| < 2) : ContDiffAt ℝ ∞ fbb u := by
  have hz : ‖(u:ℂ)‖ < 2 := by simpa using hu
  have h := (tail_analytic hz).re_ofReal.contDiffAt (n := ∞)
  have hp (n : ℕ) : ContDiffAt ℝ ∞ (fun x : ℝ => (Chebyshev.T ℝ n).eval x) u := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      ((Chebyshev.T ℝ n).contDiff_aeval (𝕜 := ℝ) (n := ∞)).contDiffAt (x := u)
  unfold fbb
  dsimp only
  fun_prop (disch := first | apply hp | assumption)

/-- On the physical interval the complexification used for smoothness evaluates
to the real Chebyshev series in §2, term for term. -/
theorem fbb_eq_real {u : ℝ} (hu : |u| ≤ 1) :
    let Tn (n : ℕ) := (Chebyshev.T ℝ n).eval u
    fbb u = 2203841/1920*Tn 1 + 5579141/153600*Tn 2 + 214597/103680*Tn 3 +
      48211/307200*Tn 4 + 251/19200*Tn 5 + 25/165888*Tn 6 -
      (42025/6 * Real.sqrt (5/3)) * ∑' n : ℕ, chebK^(n+1)*Tn (n+1)/((n+1:ℕ):ℝ)^2 := by
  have hu' : ‖(u:ℂ)‖ < 2 := by simpa using (hu.trans_lt (by norm_num : (1:ℝ) < 2))
  have hs : Summable (fun n : ℕ => (5 * chebK)^(n+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by positivity [k_bounds.1])
      (by linarith [k_bounds.2]))
  have ht : Summable (fun n => term n (u:ℂ)) := hs.of_norm_bounded (fun n => term_bound hu' n)
  have hT (n : ℕ) : T n (u:ℂ) = ((Chebyshev.T ℝ n).eval u : ℝ) := by
    unfold T
    rw [← Chebyshev.map_T Complex.ofRealHom]
    exact Polynomial.eval_map_apply Complex.ofRealHom u
  have he (n : ℕ) : (term n (u:ℂ)).re =
      chebK^(n+1)*(Chebyshev.T ℝ (n+1:ℕ)).eval u/((n+1:ℕ):ℝ)^2 := by
    unfold term
    rw [hT]
    norm_cast
  have htail := Complex.reCLM.map_tsum ht
  change (complexTail u).re = ∑' n, (term n (u:ℂ)).re at htail
  simp only [fbb, htail, he]


end
end LocalHopf.Profiles
