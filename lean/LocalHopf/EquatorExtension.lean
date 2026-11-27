import LocalHopf.PerturbationTensors
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Smooth extension from the equatorial torus to the sphere product -/

namespace LocalHopf.SphereProduct
open Set Function Filter Real Matrix
open scoped Topology ContDiff Manifold
noncomputable section

/-- Equatorial longitude on the actual unit sphere. -/
def equatorPoint (a : ℝ) : Sphere :=
  unitSphere ⟨![cos a,sin a,0], by
    change (![cos a,sin a,0] : R3) ⬝ᵥ ![cos a,sin a,0] = 1
    simp [dotProduct,Fin.sum_univ_three,← sq,Real.cos_sq_add_sin_sq]⟩

/-- The two horizontal Cartesian coordinates as a complex number. -/
def longitude (v : R3) : ℂ := ⟨v 0,v 1⟩

/-- These angles parameterize every point at height zero, including the angle seam. -/
theorem mem_equator_iff (p : Sphere) : (∃ a, equatorPoint a = p) ↔ p.val.ofLp 2 = 0 := by
  constructor
  · rintro ⟨a,rfl⟩; rfl
  · intro hz
    let v := (unitSphere.symm p).val
    let z := longitude v
    have hv : v ⬝ᵥ v = 1 := (unitSphere.symm p).property
    have h₀ : v 2 = 0 := hz
    have norm : ‖z‖ = 1 := by
      have e := Complex.sq_norm z
      change ‖z‖ ^ 2 = v 0*v 0 + v 1*v 1 at e
      simp only [dotProduct,Fin.sum_univ_three,h₀,mul_zero,add_zero] at hv
      nlinarith [norm_nonneg z]
    have cx := Complex.norm_mul_cos_arg z
    have sx := Complex.norm_mul_sin_arg z
    rw [norm,one_mul] at cx sx
    refine ⟨z.arg,unitSphere.symm.injective ?_⟩
    apply Subtype.ext
    change ![cos z.arg,sin z.arg,0] = v
    funext i; fin_cases i
    · exact cx
    · exact sx
    · exact h₀.symm

private theorem smooth_longitude : ContDiff ℝ ∞ longitude := by
  have e : longitude = fun v : R3 => (v 0 : ℂ) + (v 1 : ℂ)*Complex.I := by
    funext v; exact (Complex.mk_eq_add_mul_I ..)
  rw [e]
  have h (i : Fin 3) := Complex.ofRealCLM.contDiff (n := ∞) |>.comp (ContinuousLinearMap.proj i : R3 →L[ℝ] ℝ).contDiff
  exact (h 0).add ((h 1).mul contDiff_const)

private def cutoff (z : ℂ) := smoothTransition (4*Complex.normSq z-1)

private theorem smooth_cutoff : ContDiff ℝ ∞ cutoff := by
  apply smoothTransition.contDiff.comp
  simp only [Complex.normSq_apply]
  exact (contDiff_const.mul ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))).sub contDiff_const

private theorem cutoff_zero : cutoff =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
  have e : ∀ᶠ z : ℂ in 𝓝 0, Complex.normSq z < 1/4 :=
    Complex.continuous_normSq.continuousAt.eventually_lt continuousAt_const (by norm_num)
  filter_upwards [e] with z hz
  exact smoothTransition.zero_of_nonpos (by linarith)

private theorem period_congr {f : ℝ → ℝ} (hf : Periodic f (2*π)) {a b : ℝ}
    (eq : (a : Angle) = (b : Angle)) : f a = f b := by
  obtain ⟨n,hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp eq
  have e : a = b+n • (2*π) := by rw [zsmul_eq_mul,mul_comm (n:ℝ)]; linarith
  rw [e]; exact hf.zsmul n b

private def polarExtension (f : ℝ × ℝ → ℝ) (p : ℂ × ℂ) :=
  cutoff p.1 * cutoff p.2 * f (p.1.arg,p.2.arg)

private theorem smooth_polar {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (h₁ : ∀ b, Periodic (fun a => f (a,b)) (2*π))
    (h₂ : ∀ a, Periodic (fun b => f (a,b)) (2*π)) : ContDiff ℝ ∞ (polarExtension f) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨u,v⟩
  by_cases hu : u = 0
  · subst u
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually cutoff_zero] with q h
    simp [polarExtension,h]
  by_cases hv : v = 0
  · subst v
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually cutoff_zero] with q h
    simp [polarExtension,h]
  let angle (w z : ℂ) := (z/w).log.im + w.arg
  have reg (w : ℂ) (hw : w ≠ 0) : ContDiffAt ℝ ∞ (angle w) w := by
    have hlog := (Complex.contDiffAt_log (n := ∞) (x := w/w) (by simp [hw])).restrict_scalars ℝ
    have quot : ContDiffAt ℝ ∞ (fun z : ℂ => z/w) w := (contDiff_id.div_const w).contDiffAt
    have logq : ContDiffAt ℝ ∞ (fun z : ℂ => (z/w).log) w := hlog.comp (f := fun z : ℂ => z/w) w quot
    exact (Complex.imCLM.contDiff.contDiffAt.comp w logq).add contDiffAt_const
  have same {w z : ℂ} (hw : w ≠ 0) (hz : z ≠ 0) : (z.arg : Angle) = (angle w z : Angle) := by
    simp only [angle,Complex.log_im]
    rw [Real.Angle.coe_add,Complex.arg_div_coe_angle hz hw,sub_add_cancel]
  have hh := (hf.contDiffAt (x := (angle u u,angle v v))).comp (u,v)
    (((reg u hu).comp (u,v) contDiffAt_fst).prodMk ((reg v hv).comp (u,v) contDiffAt_snd))
  apply (((smooth_cutoff.comp contDiff_fst).contDiffAt.mul
    (smooth_cutoff.comp contDiff_snd).contDiffAt).mul hh).congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually_ne hu, continuous_snd.continuousAt.eventually_ne hv] with q hq hq'
  exact congrArg (cutoff q.1 * cutoff q.2 * ·)
    ((period_congr (h₁ _) (same hu hq)).trans (period_congr (h₂ _) (same hv hq')))

/-- A doubly periodic smooth function of the two longitudes extends across both poles.
On the equatorial band it equals its pullback by angular projection. -/
theorem extend_equator {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (h₁ : ∀ b, Periodic (fun a => f (a,b)) (2*π))
    (h₂ : ∀ a, Periodic (fun b => f (a,b)) (2*π)) :
    ∃ χ : Scalar, (∀ a b, χ (equatorPoint a,equatorPoint b) = f (a,b)) ∧
      ∀ p : Base, let u := longitude (point₁ p); let v := longitude (point₂ p)
        1/2 ≤ Complex.normSq u → 1/2 ≤ Complex.normSq v → χ p = f (u.arg,v.arg) := by
  let z (p : Base) := (longitude (point₁ p),longitude (point₂ p))
  let χ : Scalar := ⟨fun p => polarExtension f (z p),
    (smooth_polar hf h₁ h₂).contMDiff.comp ((smooth_longitude.contMDiff.comp point₁.contMDiff).prodMk_space
      (smooth_longitude.contMDiff.comp point₂.contMDiff))⟩
  have band (p : Base) (hu : 1/2 ≤ Complex.normSq (z p).1) (hv : 1/2 ≤ Complex.normSq (z p).2) :
      χ p = f ((z p).1.arg,(z p).2.arg) := by
    change cutoff (z p).1 * cutoff (z p).2 * _ = _
    simp only [cutoff,smoothTransition.one_of_one_le (show 1 ≤ 4*Complex.normSq (z p).1-1 by linarith),
      smoothTransition.one_of_one_le (show 1 ≤ 4*Complex.normSq (z p).2-1 by linarith),one_mul]
  refine ⟨χ,?_,band⟩
  intro a b
  let w (x : ℝ) : ℂ := ⟨cos x,sin x⟩
  have hw (x : ℝ) : Complex.normSq (w x) = 1 := by
    change cos x*cos x+sin x*sin x = 1
    nlinarith [Real.cos_sq_add_sin_sq x]
  have ang (x : ℝ) : ((w x).arg : Angle) = (x : Angle) := by
    simpa [w,Complex.mk_eq_add_mul_I] using Complex.arg_cos_add_sin_mul_I_coe_angle (x : Angle)
  have pair := band (equatorPoint a,equatorPoint b) (by change 1/2 ≤ Complex.normSq (w a); rw [hw]; norm_num)
    (by change 1/2 ≤ Complex.normSq (w b); rw [hw]; norm_num)
  exact pair.trans ((period_congr (h₁ _) (ang a)).trans (period_congr (h₂ _) (ang b)))

end
end LocalHopf.SphereProduct
