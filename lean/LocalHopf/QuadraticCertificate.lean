import LocalHopf.ProfileOperator
import LocalHopf.QuadraticData
import LocalHopf.QuadraticBound

/-! Proposition 5.2 for the exported quadratic coefficient functions. -/
namespace LocalHopf.Certificate
set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
private theorem certifiedLowerY : Box.bisect (Quotient.test true (1/2) lowerY) 9 ⟨-1,1⟩ = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
private theorem certifiedSc : Box.bisect (Quotient.test false 144 sc) 3 ⟨-1,1⟩ = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
private theorem certifiedN1 : Box.bisect (Quotient.test false 4 n1) 0 ⟨-1,1⟩ = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
private theorem certifiedN2 : Box.bisect (Quotient.test false 4 n2) 0 ⟨-1,1⟩ = true := by decide +kernel


open Profiles

noncomputable section

/-- Scalar channels with the profile jets and multipliers in the quadratic export. -/
def Fy (t u : ℝ) : ℝ := baseY.value t u + 18/(hh t)^2 *
  (u*deriv fbb u + (u^2-1)*deriv (deriv fbb) u)

def Fx (t u : ℝ) : ℝ := baseY.value t (-u) + 18/(hh t)^2 *
  (u*deriv (fun v => fbb (-v)) u + (u^2-1)*deriv (deriv (fun v => fbb (-v))) u)

private theorem lower_exact {t u : ℝ} (ht : 0 ≤ t) (hu : |u| ≤ 1) :
    lowerY.value t u = baseY.value t u + 18/(hh t)^2 *
    (jetPolynomial u + 42025/36 * (3872983346207/1000000000000 - 15/(4-u))) := by
  have h₁ : 0 < 1+2*t := by positivity
  have h₂ : 0 < 2+2*t-t*u := by nlinarith [mul_nonneg ht (sub_nonneg.mpr (abs_le.mp hu).2)]
  have h₃ : 0 < 4-u := by linarith [(abs_le.mp hu).2]
  have d₁ : eval₂ baseY.den t u = 3200*(1+2*t)^2*(2+2*t-t*u) := by
    norm_num [baseY, eval₂, horner, List.foldr]; ring
  have d₂ : eval₂ lowerY.den t u = 80000000000*(1+2*t)^2*(4-u)*(2+2*t-t*u) := by
    norm_num [lowerY, eval₂, horner, List.foldr]; ring
  have n : eval₂ lowerY.num t u =
      25000000*(4-u)*eval₂ baseY.num t u + 1440000000000*(2+2*t-t*u)*
      ((4-u)*(jetPolynomial u + 42025/36*(3872983346207/1000000000000)) - 42025/36*15) := by
    norm_num [lowerY, baseY, eval₂, horner, List.foldr, jetPolynomial]
    ring
  rw [Quotient.value, Quotient.value, d₁, d₂, n, hh]
  generalize 1+2*t = a at h₁ ⊢
  generalize 2+2*t-t*u = b at h₂ ⊢
  generalize 4-u = d at h₃ ⊢
  field_simp [ne_of_gt h₁, ne_of_gt h₂, ne_of_gt h₃]
  ring

theorem channels_ge_half {t u : ℝ} (ht : t ∈ Set.Icc 0 (1/100)) (hu : |u| ≤ 1) :
    1/2 ≤ Fx t u ∧ 1/2 ≤ Fy t u := by
  have hroot : (3872983346207/1000000000000 : ℝ) ≤ Real.sqrt 15 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15), Real.sqrt_nonneg 15]
  have h (v : ℝ) (hv : |v| ≤ 1) : (1:ℝ)/2 ≤ Fy t v := by
    have b := Quotient.bound true (c := 1/2) (by norm_num) lowerY 9 certifiedLowerY ht hv
    norm_num only [↓reduceIte, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at b
    rw [lower_exact ht.1 hv] at b
    rw [Fy, fbb_jet hv]
    exact b.trans (by gcongr)
  have hx : Fx t u = Fy t (-u) := by
    rw [Fx, Fy, faa_jet hu, fbb_jet (by simpa using hu)]
  exact ⟨hx ▸ h (-u) (by simpa using hu), h u hu⟩

/-- Proposition 5.2 for the scalar functions exported by the curvature calculation,
including t = 0 and both endpoints in separation. -/
theorem quadratic_certificate {t u : ℝ} (ht : t ∈ Set.Icc 0 (1/100)) (hu : |u| ≤ 1) :
    3/10 ≤ min (Fx t u) (Fy t u) - lamC * Real.sqrt (sc.value t u) -
      lamD^2 * (2*Real.sqrt (n1.value t u) + Real.sqrt (n2.value t u)) := by
  have s := Quotient.bound false (c := 144) (by decide) sc 3 certifiedSc ht hu
  have a := Quotient.bound false (c := 4) (by decide) n1 0 certifiedN1 ht hu
  have b := Quotient.bound false (c := 4) (by decide) n2 0 certifiedN2 ht hu
  norm_num at a b s
  have sq₁ : Real.sqrt (sc.value t u) ≤ 12 := (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have sq₂ : Real.sqrt (n1.value t u) ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have sq₃ : Real.sqrt (n2.value t u) ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hm := le_min (channels_ge_half ht hu).1 (channels_ge_half ht hu).2
  unfold lamC lamD
  linarith

/-- The certificate in the vector and matrix form used by the normal-form theorem.
Only the three norm identities from the geometric calculation are needed here. -/
theorem gcal_ge {t u : ℝ} (ht : t ∈ Set.Icc 0 (1/100)) (hu : |u| ≤ 1)
    (A B : Fin 2 → ℝ) (M₁ M₂ : Matrix (Fin 2) (Fin 2) ℝ)
    (hab : A ⬝ᵥ A + B ⬝ᵥ B = sc.value t u)
    (hm₁ : (∑ i, ∑ j, M₁ i j^2) = n1.value t u)
    (hm₂ : (∑ i, ∑ j, M₂ i j^2) = n2.value t u) :
    3/10 ≤ Gcal lamC lamD (Fx t u) (Fy t u) A B M₁ M₂ := by
  simpa only [Gcal, frob, hab, hm₁, hm₂] using quadratic_certificate ht hu

end
end LocalHopf.Certificate
