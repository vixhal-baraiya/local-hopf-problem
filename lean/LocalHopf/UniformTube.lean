import LocalHopf.Minimization
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Uniform minimization in a normal chart

The constants are uniform in a compact set of base parameters and in the whole
closed normal disk. Derivatives in the perturbation parameter are taken along
the moving ray `(s • ζ, s)`, including the tilt of the plane.
-/

namespace LocalHopf.UniformTube

open Set Metric
open scoped ContDiff Topology
noncomputable section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ordinary scalar derivative in the last coordinate of a family. -/
private def partialTime {A : Type*} (f : A × ℝ → ℝ) (n : ℕ) (q : A × ℝ) : ℝ :=
  iteratedDeriv n (fun r => f (q.1,r)) q.2

private theorem smooth_partialTime {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : A × ℝ → ℝ) (n m : ℕ) {q : A × ℝ} (hf : ContDiffAt ℝ (↑(m+n) : ℕ∞ω) f q) :
    ContDiffAt ℝ m (partialTime f n) q := by
  induction n generalizing m with
  | zero =>
    have he : partialTime f 0 = f := by funext w; simp [partialTime]
    simpa [he] using hf
  | succ n ih =>
    have prev : ContDiffAt ℝ ((m : ℕ∞ω)+1) (partialTime f n) q :=
      ih (m+1) (by convert hf using 1; push_cast; ring)
    let g (z : A × ℝ) (r : ℝ) := partialTime f n (z.1,r)
    have hg : ContDiffAt ℝ ((m : ℕ∞ω)+1) (Function.uncurry g) (q,q.2) :=
      prev.comp (q,q.2) (f := fun w : (A × ℝ) × ℝ => (w.1.1,w.2)) (by fun_prop)
    have hd := hg.fderiv_succ (g := fun z : A × ℝ => z.2) contDiffAt_snd
    have hv := hd.clm_apply (contDiffAt_const (c := (1:ℝ)))
    have he : partialTime f (n+1) = fun z => fderiv ℝ (g z) z.2 1 := by
      funext z
      change iteratedDeriv (n+1) _ z.2 = _
      rw [iteratedDeriv_succ]
      rfl
    rw [he]
    exact hv

/-- Normal and parameter variables move simultaneously. -/
def ray (F : P × E × ℝ → ℝ) (q : (P × E) × ℝ) : ℝ :=
  F (q.1.1, q.2 • q.1.2, q.2)

def coeff (F : P × E × ℝ → ℝ) (n : ℕ) (x : P) (ζ : E) : ℝ :=
  partialTime (ray F) n ((x,ζ),0) / n.factorial

def disk (K : Set P) (δ η : ℝ) : Set (P × E × ℝ) :=
  K ×ˢ (closedBall 0 δ ×ˢ Icc 0 η)

private theorem smooth_ray {F : P × E × ℝ → ℝ} {q : (P × E) × ℝ} {n : ℕ∞ω}
    (hf : ContDiffAt ℝ n F (q.1.1,q.2 • q.1.2,q.2)) :
    ContDiffAt ℝ n (ray F) q := by
  apply hf.comp (f := fun w : (P × E) × ℝ => (w.1.1,w.2 • w.1.2,w.2)) q
  fun_prop

private theorem compact_upper {D : Type*} [TopologicalSpace D] {S : Set D} (hS : IsCompact S)
    (f : D → ℝ) (hf : ContinuousOn f S) : ∃ B ≥ 0, ∀ x ∈ S, f x ≤ B := by
  obtain ⟨b,hb⟩ := (hS.image_of_continuousOn hf).bddAbove
  exact ⟨max b 0, le_max_right .., fun x hx => (hb ⟨x,hx,rfl⟩).trans (le_max_left ..)⟩

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ E] in
private theorem mem_disk {K : Set P} {δ η : ℝ} {x : P} {z : E} {s : ℝ} :
    (x,z,s) ∈ disk K δ η ↔ x ∈ K ∧ ‖z‖ ≤ δ ∧ s ∈ Icc 0 η := by
  simp [disk, mem_closedBall, dist_zero_right]

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
private theorem disk_compact [ProperSpace E] {K : Set P} (hK : IsCompact K) (δ η : ℝ) :
    IsCompact (disk (E := E) K δ η) :=
  hK.prod ((isCompact_closedBall ..).prod isCompact_Icc)

private def timeSlope (F : P × E × ℝ → ℝ) (q : P × E × ℝ) :=
  deriv (fun r => F (q.1,q.2.1,r)) q.2.2

private theorem smooth_slope {F : P × E × ℝ → ℝ} {q : P × E × ℝ}
    (hf : ContDiffAt ℝ 4 F q) : ContDiffAt ℝ 3 (timeSlope F) q := by
  let f (z : (P × E) × ℝ) := F (z.1.1,z.1.2,z.2)
  have h : ContDiffAt ℝ 4 f ((q.1,q.2.1),q.2.2) := hf.comp _ (f := fun z : (P × E) × ℝ => (z.1.1,z.1.2,z.2)) (by fun_prop)
  have hd := smooth_partialTime f 1 3 h
  have hc := hd.comp q (f := fun w : P × E × ℝ => ((w.1,w.2.1),w.2.2)) (by fun_prop)
  have he : timeSlope F = partialTime f 1 ∘ (fun w : P × E × ℝ => ((w.1,w.2.1),w.2.2)) := by
    funext w
    simp [timeSlope, partialTime, iteratedDeriv_one, f]
  rw [he]
  exact hc

/-- Coercivity persists to first order away from the core. The same constant
controls every normal slice of the compact chart. -/
theorem coercivity [ProperSpace E] (F : P × E × ℝ → ℝ) {K : Set P} (hK : IsCompact K)
    {δ η lam : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hsmooth : ∀ q ∈ disk (E := E) K δ η, ContDiffAt ℝ 4 F q)
    (h₀ : ∀ x ∈ K, ∀ z : E, ‖z‖ ≤ δ → lam * ‖z‖^2 ≤ F (x,z,0))
    (h₁ : ∀ x ∈ K, deriv (fun r => F (x,0,r)) 0 = 0) :
    ∃ A ≥ 0, ∀ x ∈ K, ∀ z s, ‖z‖ ≤ δ → s ∈ Icc 0 η →
      lam*‖z‖^2 - A*s*‖z‖ - A*s^2 ≤ F (x,z,s) := by
  obtain ⟨A,hA,bound⟩ := compact_upper (disk_compact (E := E) hK δ η)
    (fun q => ‖fderiv ℝ (timeSlope F) q‖)
    (fun q hq => ((smooth_slope (hsmooth q hq)).fderiv_right (m := 0) (by norm_num)).continuousAt.norm.continuousWithinAt)
  refine ⟨A,hA,?_⟩
  intro x hx z s hz hs
  let S := disk (E := E) ({x} : Set P) δ η
  have hsub : S ⊆ disk (E := E) K δ η := fun q hq => ⟨(mem_singleton_iff.mp hq.1) ▸ hx,hq.2⟩
  have cv : Convex ℝ S := (convex_singleton x).prod ((convex_closedBall ..).prod (convex_Icc ..))
  have zeroMem : (x, (0:E), (0:ℝ)) ∈ S := mem_disk.mpr ⟨by simp, by simpa using hδ,le_rfl,hη⟩
  have slope (r : ℝ) (hr : r ∈ Icc 0 s) : ‖timeSlope F (x,z,r)‖ ≤ A*(‖z‖+s) := by
    have hq : (x,z,r) ∈ S := mem_disk.mpr ⟨by simp,hz,hr.1,hr.2.trans hs.2⟩
    have h := cv.norm_image_sub_le_of_norm_fderiv_le
      (fun q hq => (smooth_slope (hsmooth q (hsub hq))).differentiableAt (by norm_num))
      (fun q hq => bound q (hsub hq)) zeroMem hq
    have ht : timeSlope F (x,0,0) = 0 := h₁ x hx
    rw [ht,sub_zero] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hA
    simp [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact ⟨by linarith [hs.1], by linarith [norm_nonneg z,hr.2]⟩
  have dh (r : ℝ) (hr : r ∈ Icc 0 s) : DifferentiableAt ℝ (fun a => F (x,z,a)) r :=
    ((hsmooth _ (mem_disk.mpr ⟨hx,hz,hr.1,hr.2.trans hs.2⟩)).comp r
      (f := fun a : ℝ => (x,z,a)) (by fun_prop)).differentiableAt (by norm_num)
  have hb := (convex_Icc (0:ℝ) s).norm_image_sub_le_of_norm_deriv_le dh slope
    (left_mem_Icc.mpr hs.1) (right_mem_Icc.mpr hs.1)
  simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg hs.1] at hb
  have hn := (abs_le.mp hb).1
  nlinarith [h₀ x hx z hz]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem coeff_zero (F : P × E × ℝ → ℝ) (x : P) (ζ : E) : coeff F 0 x ζ = F (x,0,0) := by
  simp [coeff,partialTime,ray]

private theorem taylor3 {f : ℝ → ℝ} {s B : ℝ} (hs : 0 < s)
    (hf : ∀ r ∈ Icc 0 s, ContDiffAt ℝ 4 f r)
    (hB : ∀ r ∈ Icc 0 s, |iteratedDeriv 4 f r| ≤ B) :
    |f s - (f 0 + s * deriv f 0 + s^2 * (iteratedDeriv 2 f 0 / 2) +
      s^3 * (iteratedDeriv 3 f 0 / 6))| ≤ (B/24)*s^4 := by
  have hseg : uIcc 0 s = Icc 0 s := uIcc_of_le hs.le
  obtain ⟨r,hr,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 3) hs.ne
    (f := f) (hseg ▸ fun a ha => (hf a ha).contDiffWithinAt)
  rw [uIoo_of_lt hs] at hr
  have h0 : (0:ℝ) ∈ Icc 0 s := left_mem_Icc.mpr hs.le
  have d (n : ℕ) (hn : n ≤ 4) : iteratedDerivWithin n f (Icc 0 s) 0 = iteratedDeriv n f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hs) ((hf 0 h0).of_le (by exact_mod_cast hn)) h0
  rw [hseg, taylorWithinEval_succ _ 2, taylorWithinEval_succ _ 1,
    taylorWithinEval_succ _ 0, taylor_within_zero_eval, d 1 (by decide), d 2 (by decide), d 3 (by decide)] at he
  have e : f s - (f 0 + s * deriv f 0 + s^2 * (iteratedDeriv 2 f 0 / 2) +
      s^3 * (iteratedDeriv 3 f 0 / 6)) = iteratedDeriv 4 f r * s^4 / 24 := by
    norm_num [iteratedDeriv_one] at he
    linarith only [he]
  rw [e, abs_div, abs_mul, abs_of_nonneg (pow_nonneg hs.le 4)]
  have h := mul_le_mul_of_nonneg_right (hB r ⟨hr.1.le,hr.2.le⟩) (pow_nonneg hs.le 4)
  norm_num
  linarith

/-- A single fourth-order remainder bound for every moving ray of bounded speed,
including when only its endpoint is known to lie in the normal disk. -/
theorem rescaled_expansion [ProperSpace E] (F : P × E × ℝ → ℝ) {K : Set P}
    (hK : IsCompact K) {δ η : ℝ} (R : ℝ)
    (hsmooth : ∀ q ∈ disk (E := E) K δ η, ContDiffAt ℝ 4 F q) :
    ∃ C ≥ 0, ∀ x ∈ K, ∀ (ζ : E) (s : ℝ), ‖ζ‖ ≤ R → ‖s • ζ‖ ≤ δ → 0 < s → s ≤ η →
      |F (x,s • ζ,s) - (coeff F 0 x ζ + s*coeff F 1 x ζ +
        s^2*coeff F 2 x ζ + s^3*coeff F 3 x ζ)| ≤ C*s^4 := by
  let S : Set ((P × E) × ℝ) := ((K ×ˢ closedBall 0 R) ×ˢ Icc 0 η) ∩
    (fun q : (P × E) × ℝ => q.2 • q.1.2) ⁻¹' closedBall 0 δ
  have hc : IsCompact S := ((hK.prod (isCompact_closedBall ..)).prod isCompact_Icc).inter_right
    (isClosed_closedBall.preimage (by fun_prop))
  have hreg (q : (P × E) × ℝ) (hq : q ∈ S) : ContDiffAt ℝ 4 (ray F) q :=
    smooth_ray (hsmooth _ ⟨hq.1.1.1,hq.2,hq.1.2⟩)
  obtain ⟨B,hB,bd⟩ := compact_upper hc (fun q => |partialTime (ray F) 4 q|)
    (fun q hq => (smooth_partialTime _ 4 0 (hreg q hq)).continuousAt.abs.continuousWithinAt)
  refine ⟨B/24, by positivity, ?_⟩
  intro x hx ζ s hζ hz hs hη
  have mem (r : ℝ) (hr : r ∈ Icc 0 s) : ((x,ζ),r) ∈ S := by
    refine ⟨⟨⟨hx,by simpa using hζ⟩,hr.1,hr.2.trans hη⟩,?_⟩
    change r • ζ ∈ closedBall 0 δ
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.1]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs] at hz
    exact (mul_le_mul_of_nonneg_right hr.2 (norm_nonneg ζ)).trans hz
  let f (r : ℝ) := ray F ((x,ζ),r)
  have hf (r : ℝ) (hr : r ∈ Icc 0 s) : ContDiffAt ℝ 4 f r :=
    (hreg ((x,ζ),r) (mem r hr)).comp r (f := fun a : ℝ => ((x,ζ),a)) (by fun_prop)
  have hb (r : ℝ) (hr : r ∈ Icc 0 s) : |iteratedDeriv 4 f r| ≤ B :=
    bd ((x,ζ),r) (mem r hr)
  have h := taylor3 (f := f) (B := B) hs hf hb
  have e0 : coeff F 0 x ζ = ray F ((x,ζ),0) := by simp [coeff,partialTime]
  have e1 : coeff F 1 x ζ = deriv (fun r => ray F ((x,ζ),r)) 0 := by simp [coeff,partialTime,iteratedDeriv_one]
  have e2 : coeff F 2 x ζ = iteratedDeriv 2 (fun r => ray F ((x,ζ),r)) 0 / 2 := by
    norm_num [coeff,partialTime,Nat.factorial]
  have e3 : coeff F 3 x ζ = iteratedDeriv 3 (fun r => ray F ((x,ζ),r)) 0 / 6 := by
    norm_num [coeff,partialTime,Nat.factorial]
  rw [e0,e1,e2,e3]
  exact h

/-- Regularity of a rescaled Taylor coefficient in both core point and tilt. -/
theorem smooth_coeff {F : P × E × ℝ → ℝ} {x : P} (ζ : E) (n m : ℕ) (hn : m+n ≤ 4)
    (hf : ContDiffAt ℝ 4 F (x,0,0)) :
    ContDiffAt ℝ m (fun w : P × E => coeff F n w.1 w.2) (x,ζ) := by
  have h : ContDiffAt ℝ (↑(m+n) : ℕ∞ω) (ray F) ((x,ζ),0) :=
    smooth_ray (by simpa using hf.of_le (by exact_mod_cast hn))
  have hc := (smooth_partialTime _ n m h).comp (x,ζ) (f := fun w : P × E => (w,(0:ℝ))) (by fun_prop)
  exact hc.div_const _

/-- The moving ray has zero first derivative by (H0) and (H1). -/
theorem first_coeff_zero (F : P × E × ℝ → ℝ) {x : P} {δ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam) (hsmooth : ContDiffAt ℝ 4 F (x,0,0))
    (hflat : F (x,0,0) = 0) (h₀ : ∀ z : E, ‖z‖ ≤ δ → lam*‖z‖^2 ≤ F (x,z,0))
    (h₁ : deriv (fun r => F (x,0,r)) 0 = 0) (ζ : E) : coeff F 1 x ζ = 0 := by
  let L := fderiv ℝ F (x,0,0)
  have hd := (hsmooth.differentiableAt (by norm_num)).hasFDerivAt
  have line : HasDerivAt (fun r : ℝ => r • ζ) ζ 0 := by
    simpa using (hasDerivAt_id' (0:ℝ)).smul_const ζ
  have normal : HasDerivAt (fun r : ℝ => (x,r • ζ,(0:ℝ))) (0,ζ,0) 0 := (hasDerivAt_const (0:ℝ) x).prodMk (line.prodMk (hasDerivAt_const (0:ℝ) (0:ℝ)))
  have time : HasDerivAt (fun r : ℝ => (x,(0:E),r)) (0,0,1) 0 := (hasDerivAt_const (0:ℝ) x).prodMk ((hasDerivAt_const (0:ℝ) (0:E)).prodMk (hasDerivAt_id' (0:ℝ)))
  have moving : HasDerivAt (fun r : ℝ => (x,r • ζ,r)) (0,ζ,1) 0 := (hasDerivAt_const (0:ℝ) x).prodMk (line.prodMk (hasDerivAt_id' (0:ℝ)))
  have normMin : IsLocalMin (fun r : ℝ => F (x,r • ζ,0)) 0 := by
    have ev : ∀ᶠ r : ℝ in 𝓝 0, ‖r • ζ‖ < δ :=
      ((continuous_id.smul continuous_const).norm.continuousAt.eventually_lt continuousAt_const (by simpa using hδ))
    filter_upwards [ev] with r hr
    simpa [hflat] using (mul_nonneg hlam (sq_nonneg ‖r • ζ‖)).trans (h₀ _ hr.le)
  have hn : L (0,ζ,0) = 0 := normMin.hasDerivAt_eq_zero
    ((show HasFDerivAt F L (x,(0:ℝ) • ζ,0) by simpa [L] using hd).comp_hasDerivAt 0 normal)
  have ht : L (0,0,1) = 0 := (hd.comp_hasDerivAt 0 time).deriv.symm.trans h₁
  have hm : deriv (fun r => ray F ((x,ζ),r)) 0 = L (0,ζ,1) :=
    ((show HasFDerivAt F L (x,(0:ℝ) • ζ,0) by simpa [L] using hd).comp_hasDerivAt 0 moving).deriv
  have he : (0,ζ,1) = ((0,ζ,0) : P × E × ℝ) + (0,0,1) := by simp
  have ec : coeff F 1 x ζ = deriv (fun r => ray F ((x,ζ),r)) 0 := by
    simp [coeff,partialTime,iteratedDeriv_one]
  rw [ec,hm,he,L.map_add,hn,ht,add_zero]

private theorem cubic_lipschitz [ProperSpace E] (F : P × E × ℝ → ℝ) {K : Set P}
    (hK : IsCompact K) (R : ℝ) (hf : ∀ x ∈ K, ContDiffAt ℝ 4 F (x,0,0)) :
    ∃ L ≥ 0, ∀ x ∈ K, ∀ a b : E, ‖a‖ ≤ R → ‖b‖ ≤ R →
      coeff F 3 x a - L*‖b-a‖ ≤ coeff F 3 x b := by
  let f := fun w : P × E => coeff F 3 w.1 w.2
  have hd (x : P) (hx : x ∈ K) (z : E) : ContDiffAt ℝ 1 f (x,z) :=
    smooth_coeff z 3 1 (by decide) (hf x hx)
  obtain ⟨L,hL,bound⟩ := compact_upper (hK.prod (isCompact_closedBall (0:E) R))
    (fun q => ‖fderiv ℝ f q‖) (fun w hw =>
      ((hd _ hw.1 _).fderiv_right (m := 0) (by norm_num)).continuousAt.norm.continuousWithinAt)
  refine ⟨L,hL,?_⟩
  intro x hx a b ha hb
  let S : Set (P × E) := {x} ×ˢ closedBall 0 R
  have sub : S ⊆ K ×ˢ closedBall 0 R := fun q hq => ⟨(mem_singleton_iff.mp hq.1) ▸ hx,hq.2⟩
  have cv : Convex ℝ S := (convex_singleton x).prod (convex_closedBall ..)
  have h := cv.norm_image_sub_le_of_norm_fderiv_le
    (fun q hq => (hd _ (sub hq).1 _).differentiableAt one_ne_zero) (fun q hq => bound q (sub hq))
    (x := (x,a)) (y := (x,b)) ⟨by simp,by simpa using ha⟩ ⟨by simp,by simpa using hb⟩
  have hlow := (abs_le.mp
    (show |f (x,b)-f (x,a)| ≤ L*‖b-a‖ by simpa [Prod.norm_def, Real.norm_eq_abs] using h)).1
  change f (x,a) - L*‖b-a‖ ≤ f (x,b)
  linarith

/-- Uniform lower estimate in a normal chart. The functions being minimized are
the actual Taylor coefficients along the tilted ray. The background lower bound,
the first variation on the core, and the centered quadratic jet determine one
remainder constant for every normal displacement. -/
theorem lower_bound [ProperSpace E] (F : P × E × ℝ → ℝ) {K : Set P} (hK : IsCompact K)
    {δ η lam μ : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hlam : 0 < lam) (hμ : 0 < μ)
    (hsmooth : ∀ q ∈ disk (E := E) K δ η, ContDiffAt ℝ 4 F q)
    (hflat : ∀ x ∈ K, F (x,0,0) = 0)
    (h₀ : ∀ x ∈ K, ∀ z : E, ‖z‖ ≤ δ → lam*‖z‖^2 ≤ F (x,z,0))
    (h₁ : ∀ x ∈ K, deriv (fun r => F (x,0,r)) 0 = 0)
    (center : P → E) (hcenter : ContinuousOn center K)
    (hQ : ∀ x ∈ K, ∀ ζ, coeff F 2 x (center x) + μ*‖ζ-center x‖^2 ≤ coeff F 2 x ζ) :
    ∃ C ≥ 0, ∀ x ∈ K, ∀ z s, ‖z‖ ≤ δ → s ∈ Icc 0 (min η 1) →
      s^2*coeff F 2 x (center x) + s^3*coeff F 3 x (center x) - C*s^4 ≤ F (x,z,s) := by
  obtain ⟨A,hA,coer⟩ := coercivity F hK hδ.le hη.le hsmooth h₀ h₁
  have reg (x : P) (hx : x ∈ K) := hsmooth (x,0,0) (mem_disk.mpr ⟨hx,by simpa using hδ.le,le_rfl,hη.le⟩)
  have cont (n : ℕ) (hn : n ≤ 4) : ContinuousOn (fun x => coeff F n x (center x)) K := by
    intro x hx
    exact (smooth_coeff (center x) n 0 (by simpa using hn) (reg x hx)).continuousAt.comp_continuousWithinAt (f := fun a => (a,center a))
      (continuousWithinAt_id.prodMk (hcenter x hx))
  obtain ⟨B,_,hB⟩ := compact_upper hK _ ((cont 2 (by decide)).abs.add (cont 3 (by decide)).abs)
  obtain ⟨D,_,hD⟩ := compact_upper hK _ hcenter.norm
  let R := 1+(2*A+B)/lam
  obtain ⟨C,hC,expan⟩ := rescaled_expansion F hK R hsmooth
  obtain ⟨L,_,lip⟩ := cubic_lipschitz F hK (max D R) reg
  refine ⟨C+L^2/(4*μ), by positivity, ?_⟩
  intro x hx z s hz hs
  let Q := coeff F 2 x
  let T := coeff F 3 x
  have rad : 1+(2*A+(|Q (center x)|+|T (center x)|))/lam ≤ R := by
    dsimp [R,Q,T]
    gcongr
    exact hB x hx
  apply minimization_lower_bound (fun w r => F (x,w,r)) δ η lam μ A C L (Q (center x))
    (center x) Q T hlam hμ hA hC (fun w r hw hr he => coer x hx w r hw ⟨hr,he⟩) _ (hQ x hx) _
    z s hz hs.1 (hs.2.trans (min_le_left ..)) (hs.2.trans (min_le_right ..))
  · intro ζ r hζ hw hr he
    have H := (abs_le.mp (expan x hx ζ r (hζ.trans rad) hw hr he)).1
    have hzero : coeff F 0 x ζ = 0 := by simp [coeff,partialTime,ray,hflat x hx]
    rw [hzero,first_coeff_zero F hδ hlam.le (reg x hx) (hflat x hx) (h₀ x hx) (h₁ x hx) ζ] at H
    dsimp [Q,T]
    linarith
  · intro ζ hζ
    exact lip x hx _ _ ((hD x hx).trans (le_max_left ..)) ((hζ.trans rad).trans (le_max_right ..))

open Filter in
/-- The third-order remainder on rescaled rays, with both base and tilt velocity
allowed to vary continuously at zero. The limit is two-sided. -/
theorem moving_cubic_remainder (F : P × E × ℝ → ℝ) {x : P} {a : E}
    (hf : ContDiffAt ℝ 4 F (x,0,0)) (w : ℝ → P × E)
    (hw : Tendsto w (𝓝[≠] (0:ℝ)) (𝓝 (x,a))) :
    Tendsto (fun s => (F ((w s).1,s • (w s).2,s) -
      (coeff F 0 (w s).1 (w s).2 + s*coeff F 1 (w s).1 (w s).2 +
        s^2*coeff F 2 (w s).1 (w s).2))/s^3) (𝓝[≠] 0) (𝓝 (coeff F 3 x a)) := by
  let f := ray F
  let o := ((x,a),(0:ℝ))
  have sm : ContDiffAt ℝ 4 f o := smooth_ray (by simpa [o] using hf)
  have cont : ContinuousAt (partialTime f 3) o :=
    (smooth_partialTime f 3 0 (q := o) (sm.of_le (by norm_num))).continuousAt
  let L := 𝓝[≠] (0:ℝ)
  have sid : Tendsto id L (𝓝 0) := nhdsWithin_le_nhds
  have good := sm.eventually (by simp)
  obtain ⟨U,hU,V,hV,sub⟩ := mem_nhds_prod_iff.mp good
  obtain ⟨δ,hδ,inc⟩ := Metric.mem_nhds_iff.mp hV
  let R (s : ℝ) := (F ((w s).1,s • (w s).2,s) -
    (coeff F 0 (w s).1 (w s).2+s*coeff F 1 (w s).1 (w s).2+s^2*coeff F 2 (w s).1 (w s).2))/s^3
  let witness (s r : ℝ) := |r|≤|s| ∧ R s = partialTime f 3 (w s,r)/6
  have existsR : ∀ᶠ s in L, ∃ r, witness s r := by
    filter_upwards [hw hU,sid (Metric.ball_mem_nhds (0:ℝ) hδ),self_mem_nhdsWithin] with s hws hs hsne
    have nz : s≠0 := hsne
    have bound (r : ℝ) (hr : r ∈ uIcc 0 s) : |r|≤|s| := by
      rcases mem_uIcc.mp hr with hr | hr
      · simpa only [abs_of_nonneg hr.1,abs_of_nonneg (hr.1.trans hr.2)] using hr.2
      · simpa only [abs_of_nonpos hr.2,abs_of_nonpos (hr.1.trans hr.2),neg_le_neg_iff] using hr.1
    let g (r : ℝ) := f (w s,r)
    have smooth (r : ℝ) (hr : r ∈ uIcc 0 s) : ContDiffAt ℝ 4 g r := by
      have hsδ : |s|<δ := by simpa [Metric.mem_ball,Real.dist_eq] using hs
      have hrδ := (bound r hr).trans_lt hsδ
      have m : r ∈ V := inc (by simpa [Metric.mem_ball,Real.dist_eq] using hrδ)
      have hp : ContDiffAt ℝ 4 f (w s,r) := sub ⟨hws,m⟩
      exact hp.comp r (f := fun y : ℝ => (w s,y)) (contDiffAt_const.prodMk contDiffAt_id)
    obtain ⟨r,hr,er⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := g) (n := 2) nz.symm
      (fun y hy => ((smooth y hy).of_le (by norm_num)).contDiffWithinAt)
    have m0 : (0:ℝ) ∈ uIcc 0 s := left_mem_uIcc
    have d (i : ℕ) (hi : i≤4) : iteratedDerivWithin i g (uIcc 0 s) 0=iteratedDeriv i g 0 :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc nz.symm) ((smooth _ m0).of_le (by exact_mod_cast hi)) m0
    rw [taylorWithinEval_succ _ 1,taylorWithinEval_succ _ 0,taylor_within_zero_eval,d 1 (by decide),d 2 (by decide)] at er
    refine ⟨r,bound r ⟨hr.1.le,hr.2.le⟩,?_⟩
    change (g s-(iteratedDeriv 0 g 0 / _+s*(iteratedDeriv 1 g 0 / _)+s^2*(iteratedDeriv 2 g 0 / _)))/s^3 = iteratedDeriv 3 g r/6
    norm_num [Nat.factorial,iteratedDeriv_one] at er ⊢
    apply (div_eq_iff (pow_ne_zero _ nz)).mpr
    linarith only [er]
  classical
  let r (s : ℝ) := if h : ∃ y, witness s y then h.choose else 0
  have chosen : ∀ᶠ s in L, witness s (r s) := existsR.mono (fun s h => by simpa only [r,dite_eq_left h] using h.choose_spec)
  have small : Tendsto r L (𝓝 0) := squeeze_zero_norm' (chosen.mono (fun s h => h.1)) (by simpa using sid.abs)
  have eql : R =ᶠ[L] (fun s => partialTime f 3 (w s,r s)/6) := chosen.mono (fun s h => h.2)
  have lim := (cont.tendsto.comp (hw.prodMk_nhds small)).div_const (6:ℝ)
  have target : coeff F 3 x a = partialTime f 3 o / 6 := by
    change iteratedDeriv 3 _ 0 / (Nat.factorial 3 : ℝ) = _
    norm_num [Nat.factorial,partialTime,f,o]
  rw [target]
  exact lim.congr' eql.symm


end
end LocalHopf.UniformTube
