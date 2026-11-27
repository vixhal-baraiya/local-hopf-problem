import Mathlib.Analysis.Calculus.SmoothSeries
import LocalHopf.ChebyshevProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-! The profile enters the quadratic certificate through its angular second derivative. -/

namespace LocalHopf.Profiles
open Real
noncomputable section

private def w (n : ℕ) : ℝ := (n + 1 : ℕ)
private theorem w_one (n : ℕ) : 1 ≤ w n := by unfold w; exact_mod_cast Nat.le_add_left 1 n
private def cosTerm (n : ℕ) (x : ℝ) := chebK^(n+1) * cos (w n*x) / (w n)^2
private def sinTerm (n : ℕ) (x : ℝ) := -(chebK^(n+1) * sin (w n*x) / w n)
private def cosGeom (n : ℕ) (x : ℝ) := chebK^(n+1) * cos (w n*x)

private theorem geomSummable : Summable (fun n : ℕ => chebK^(n+1)) := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)
  apply (summable_nat_add_iff 1).mpr
  apply summable_geometric_of_lt_one <;> unfold chebK <;> nlinarith [Real.sqrt_nonneg 15]

private theorem k_nonneg : 0 ≤ chebK := by
  unfold chebK; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)]

private theorem cosTerm_deriv (n : ℕ) (x : ℝ) : HasDerivAt (cosTerm n) (sinTerm n x) x := by
  have h := (((Real.hasDerivAt_cos _).comp x ((hasDerivAt_id x).const_mul (w n))).const_mul
    (chebK^(n+1))).div_const ((w n)^2)
  apply h.congr_deriv
  unfold sinTerm
  have hn := w_one n
  dsimp
  field_simp [show w n ≠ 0 by linarith]

private theorem sinTerm_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (sinTerm n) (-cosGeom n x) x := by
  have h := ((((Real.hasDerivAt_sin _).comp x ((hasDerivAt_id x).const_mul (w n))).const_mul
    (chebK^(n+1))).div_const (w n)).neg
  apply h.congr_deriv
  unfold cosGeom
  have hn := w_one n
  dsimp
  field_simp [show w n ≠ 0 by linarith]

private theorem term_bounds (n : ℕ) (x : ℝ) :
    ‖cosTerm n x‖ ≤ chebK^(n+1) ∧ ‖sinTerm n x‖ ≤ chebK^(n+1) ∧
    ‖-cosGeom n x‖ ≤ chebK^(n+1) := by
  have hn := w_one n
  have hp : 0 ≤ chebK^(n+1) := pow_nonneg k_nonneg _
  simp only [cosTerm, sinTerm, cosGeom, Real.norm_eq_abs, abs_neg, abs_div, abs_mul,
    abs_pow, abs_of_nonneg k_nonneg, abs_of_nonneg (by linarith : 0 ≤ w n)]
  refine ⟨?_, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < (w n)^2)).2
    exact mul_le_mul_of_nonneg_left ((abs_cos_le_one _).trans (by nlinarith)) hp
  · apply (div_le_iff₀ (by linarith : 0 < w n)).2
    exact mul_le_mul_of_nonneg_left ((abs_sin_le_one _).trans hn) hp
  · simpa using mul_le_mul_of_nonneg_left (abs_cos_le_one (w n*x)) hp

private theorem tail_deriv (x : ℝ) :
    HasDerivAt (fun y => ∑' n, cosTerm n y) (∑' n, sinTerm n x) x :=
  hasDerivAt_tsum geomSummable cosTerm_deriv (fun n y => (term_bounds n y).2.1)
    (geomSummable.of_norm_bounded (fun n => (term_bounds n 0).1)) x

private theorem tail_second (x : ℝ) :
    HasDerivAt (fun y => ∑' n, sinTerm n y) (-(∑' n, cosGeom n x)) x := by
  simpa only [tsum_neg] using hasDerivAt_tsum geomSummable sinTerm_deriv
    (fun n y => (term_bounds n y).2.2)
    (geomSummable.of_norm_bounded (fun n => (term_bounds n 0).2.1)) x


private theorem cosGeom_sum (x : ℝ) :
    (∑' n, cosGeom n x) = -1/2 + sqrt 15 / (2*(4-cos x)) := by
  let f (n : ℕ) := chebK^n * cos ((n:ℝ)*x)
  have hk := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)
  have hs : Summable f :=
    (summable_geometric_of_lt_one k_nonneg (show chebK < 1 by unfold chebK; nlinarith [sqrt_nonneg 15])).of_norm_bounded
      (fun n => by simp only [f, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg k_nonneg]
                   simpa using mul_le_mul_of_nonneg_left (abs_cos_le_one ((n:ℝ)*x)) (pow_nonneg k_nonneg n))
  have hs₁ := (summable_nat_add_iff 1).mpr hs
  have hs₂ := (summable_nat_add_iff 1).mpr hs₁
  have h0 := hs.tsum_eq_zero_add
  have h1 := hs₁.tsum_eq_zero_add
  have hrec (n : ℕ) : f (n+1+1) + chebK^2*f n = (2*chebK*cos x)*f (n+1) := by
    have hc := Real.cos_add_cos (((n:ℝ)+2)*x) ((n:ℝ)*x)
    ring_nf at hc
    simp only [f, pow_succ, Nat.cast_succ]
    ring_nf
    linear_combination (chebK^n * chebK^2) * hc
  have he := congrArg (fun g : ℕ → ℝ => ∑' n, g n) (funext hrec)
  rw [hs₂.tsum_add (hs.mul_left _), tsum_mul_left, tsum_mul_left] at he
  change (∑' n, f (n+1)) = _
  have hzero : f 0 = 1 := by simp [f]
  have hone : f 1 = chebK*cos x := by simp [f]
  rw [hzero] at h0
  rw [hone] at h1
  have hden : 4-cos x ≠ 0 := by linarith [cos_le_one x]
  have hp : 0 < chebK := by unfold chebK; nlinarith [sqrt_nonneg 15]
  have halg : chebK^2+1 = 8*chebK := by unfold chebK; nlinarith
  have hsum : (2*chebK) * (4-cos x) * (∑' n, f (n+1)) = chebK*(cos x-chebK) := by
    linear_combination he + h1 - (chebK^2)*h0 - (∑' n, f (n+1))*halg
  have hsimp : (∑' n, f (n+1)) = (cos x-chebK)/(2*(4-cos x)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hden)).2
    apply mul_left_cancel₀ (ne_of_gt hp)
    linear_combination hsum
  rw [hsimp, chebK]
  field_simp; ring


open Polynomial
open scoped ContDiff

private def finiteP : ℝ[X] :=
  C (25/5184)*X^6 + C (251/1200)*X^5 + C (431399/345600)*X^4 +
  C (10391/1296)*X^3 + C (8224391/115200)*X^2 + C (246605/216)*X - C (299973167/8294400)

private def amp : ℝ := 42025/6 * sqrt (5/3)

private theorem angular_series (x : ℝ) :
    fbb (cos x) = finiteP.eval (cos x) - amp * ∑' n, cosTerm n x := by
  rw [fbb_eq_real (abs_cos_le_one _)]
  dsimp only
  have ht (n : ℕ) : chebK^(n+1)*(Chebyshev.T ℝ (n+1:ℕ)).eval (cos x)/((n+1:ℕ):ℝ)^2 =
      cosTerm n x := by simp [cosTerm, w]
  simp_rw [ht]
  congr 1
  have step (n : ℤ) := Chebyshev.T_add_two ℝ n
  have h₂ := step 0
  have h₃ := step 1
  have h₄ := step 2
  have h₅ := step 3
  have h₆ := step 4
  norm_num at h₂ h₃ h₄ h₅ h₆
  simp [h₆, h₅, h₄, h₃, h₂, finiteP]
  ring

/-- The polynomial part of the angular profile after multiplication of mode n by n². -/
def jetPolynomial (u : ℝ) : ℝ :=
  25*u^6/144 + 251*u^5/48 + 7931*u^4/400 + 48943*u^3/720 +
  27059*u^2/100 + 13123*u/12 - 8224391/57600

private theorem polynomial_jet (u : ℝ) : u*finiteP.derivative.eval u +
    (u^2-1)*finiteP.derivative.derivative.eval u = jetPolynomial u := by
  simp [finiteP, jetPolynomial, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring

/-- The exact combination of first and second profile derivatives used by both
diagonal quadratic channels. This includes the two singular base pairs. -/
theorem fbb_jet {u : ℝ} (hu : |u| ≤ 1) :
    u*deriv fbb u + (u^2-1)*deriv (deriv fbb) u =
    jetPolynomial u + 42025/36 * (sqrt 15 - 15/(4-u)) := by
  let x := arccos u
  have hcos : cos x = u := cos_arccos (abs_le.mp hu).1 (abs_le.mp hu).2
  have hd (y : ℝ) := smoothAt_fbb ((abs_cos_le_one y).trans_lt (by norm_num : (1:ℝ) < 2))
  have hdiff (y : ℝ) := ((hd y).differentiableAt (by simp)).hasDerivAt
  have hdiff₂ := (((hd x).derivWithin (m := 1) (by simp)).differentiableAt one_ne_zero).hasDerivAt
  have hfirst (y : ℝ) :
      deriv fbb (cos y)*(-sin y) = finiteP.derivative.eval (cos y)*(-sin y) -
        amp * ∑' n, sinTerm n y := by
    have hf := (hdiff y).comp y (hasDerivAt_cos y)
    have hg := ((finiteP.hasDerivAt _).comp y (hasDerivAt_cos y)).sub ((tail_deriv y).const_mul amp)
    apply hf.unique
    exact hg.congr_of_eventuallyEq (Filter.Eventually.of_forall angular_series)
  have hf := ((hdiff₂.comp x (hasDerivAt_cos x)).mul (hasDerivAt_sin x).neg)
  have hg := (((finiteP.derivative.hasDerivAt _).comp x (hasDerivAt_cos x)).mul
    (hasDerivAt_sin x).neg).sub ((tail_second x).const_mul amp)
  have he := hf.unique (hg.congr_of_eventuallyEq (Filter.Eventually.of_forall hfirst))
  simp only [Function.comp_apply, Pi.neg_apply, cosGeom_sum, hcos] at he
  have hsin := sin_sq_add_cos_sq x
  rw [hcos] at hsin
  have hden : 4-u ≠ 0 := by linarith [(abs_le.mp hu).2]
  have hA : amp = 42025/18 * sqrt 15 := by
    unfold amp
    rw [show (5/3:ℝ) = 15/3^2 by norm_num, Real.sqrt_div' _ (sq_nonneg _),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
    ring
  calc
    _ = jetPolynomial u - amp * (-1/2 + sqrt 15 / (2*(4-u))) := by
      rw [← polynomial_jet]
      linear_combination -he + (deriv (deriv fbb) u - finiteP.derivative.derivative.eval u)*hsin
    _ = _ := by
      rw [hA]
      field_simp [hden]
      ring_nf
      norm_num [sq_sqrt]
      ring

/-- Reflection gives the aa jet at both endpoints as well as on the regular stratum. -/
theorem faa_jet {u : ℝ} (hu : |u| ≤ 1) :
    u*deriv (fun v => fbb (-v)) u + (u^2-1)*deriv (deriv (fun v => fbb (-v))) u =
    jetPolynomial (-u) + 42025/36 * (sqrt 15 - 15/(4-(-u))) := by
  have smooth (v : ℝ) (hv : |v| < 2) := smoothAt_fbb (u := -v) (by simpa using hv)
  have hv : |u| < 2 := hu.trans_lt (by norm_num)
  have hnear : deriv (fun y => fbb (-y)) =ᶠ[nhds u] (fun v => -(deriv fbb (-v))) := by
    filter_upwards [continuous_abs.continuousAt.eventually_lt_const hv] with v h
    have hcomp := ((smooth v h).differentiableAt (by simp)).hasDerivAt.comp v (hasDerivAt_id v).neg
    simpa [Function.comp_def] using hcomp.deriv
  have hd₂ := (((smooth u hv).derivWithin (m := 1) (by simp)).differentiableAt one_ne_zero).hasDerivAt
  have he : deriv (deriv (fun v => fbb (-v))) u = deriv (deriv fbb) (-u) := by
    rw [hnear.deriv_eq]
    simpa [Function.comp_def] using ((hd₂.comp u (hasDerivAt_id u).neg).neg).deriv
  rw [he, hnear.eq_of_nhds]
  convert fbb_jet (u := -u) (by simpa using hu) using 1
  ring

end
end LocalHopf.Profiles
