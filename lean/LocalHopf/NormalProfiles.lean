import LocalHopf.Profiles
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Rational normal corrections of §2
The rows are coefficients in ascending powers of `t`, as in
`verification/normal_corrections.py`. Each row is a polynomial in `u`.
-/
namespace LocalHopf.Profiles
open scoped ContDiff
noncomputable section

def MnumeratorExpr {R : Type*} [Ring R] (t u : R) : R :=
  (-134 + 32*u + 124*u^2 - 48*u^3) +
    t*(-36 + 116*u + 192*u^2 - 24*u^3 - 64*u^4) +
    t^2*(-74 + 159*u + 617*u^2 - 19*u^3 - 175*u^4 - 36*u^5) +
    t^3*(-212 - 322*u + 306*u^2 + 394*u^3 - 94*u^4 - 72*u^5)

def NnumeratorExpr {R : Type*} [Ring R] (t u : R) : R :=
  (-242 - 16*u + 268*u^2 + 336*u^3) +
    t*(-812 - 1566*u + 1146*u^2 + 1660*u^3 + 456*u^4) +
    t^2*(-1056 - 3013*u - 543*u^2 + 2449*u^3 + 1423*u^4 + 124*u^5) +
    t^3*(-618 - 1957*u - 1158*u^2 + 792*u^3 + 812*u^4 + 165*u^5 - 36*u^6) +
    t^4*(-212 - 534*u - 16*u^2 + 700*u^3 + 300*u^4 - 166*u^5 - 72*u^6)

def Mnumerator (t u : ℝ) : ℝ := MnumeratorExpr t u
def Nnumerator (t u : ℝ) : ℝ := NnumeratorExpr t u

def normalM (t u : ℝ) : ℝ := Mnumerator t u / (80 * hh t ^ 2 * (1 + t * (1 + u)))
def normalN (t u : ℝ) : ℝ := Nnumerator t u / (80 * hh t ^ 2 * (1 + t * (1 + u))^2)

theorem normalM_zero (t : ℝ) : normalM t 0 = Mt0 t := by
  unfold normalM Mnumerator MnumeratorExpr Mt0 hh
  by_cases ha : 1+t = 0
  · simp [ha]
  by_cases hb : 1+2*t = 0
  · simp [hb]
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_pow (by decide : 5 ≠ 0), add_zero, sub_zero, mul_one]
  field_simp
  ring

theorem smooth_normal_profiles {t u : ℝ} (ht : 0 ≤ t) (hu : |u| ≤ 1) :
    ContDiffAt ℝ ∞ (normalM t) u ∧ ContDiffAt ℝ ∞ (normalN t) u ∧
    ContDiffAt ℝ ∞ (varphi t) u ∧ ContDiffAt ℝ ∞ (psi t) u := by
  have ha : 0 < 1 + t * (1 + u) := by
    have := (abs_le.mp hu).1
    nlinarith [mul_nonneg ht (show 0 ≤ 1+u by linarith)]
  have hh' : 0 < hh t := by unfold hh; linarith
  have hu' : u^2 ≤ 1 := by
    calc
      u^2 = |u|^2 := (sq_abs u).symm
      _ ≤ (1:ℝ)^2 := by gcongr
      _ = 1 := one_pow _
  have hd : 0 < D t u := lt_of_lt_of_le hh' (D_ge_h t u hu')
  have hD : ContDiff ℝ ∞ (D t) := by unfold D; fun_prop
  unfold normalM normalN Mnumerator Nnumerator MnumeratorExpr NnumeratorExpr varphi psi
  refine ⟨?_, ?_, ?_, ?_⟩ <;> fun_prop (disch := positivity)

end
end LocalHopf.Profiles
