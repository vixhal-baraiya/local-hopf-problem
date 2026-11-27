import LocalHopf.TorusMean
import LocalHopf.Profiles
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # The Poisson correction on the equatorial torus

In angles `(m+d,m-d)` the simultaneous and opposite rotations differentiate
in `m` and `d`. Each nonconstant rotation mode solves a periodic second-order ODE.
-/

namespace LocalHopf.TorusPoisson
open Real Function intervalIntegral
open scoped ContDiff Topology
noncomputable section

private abbrev T : ℝ := 2 * π

/-- Periodic inverse of `D-a` on smooth functions of separation. -/
private def inverseFirst (a : ℝ) (f : ℝ → ℝ) (x : ℝ) :=
  (∫ r in (0:ℝ)..T, exp (-a*r)*f (x+r)) / (exp (-a*T)-1)

private theorem inverse_shift (a : ℝ) (f : ℝ → ℝ) {l e : ℝ} (hf : ∀ x, f (x+l) = e*f x) (x : ℝ) :
    inverseFirst a f (x+l) = e*inverseFirst a f x := by
  have eq (r : ℝ) : exp (-a*r)*f (x+l+r) = e*(exp (-a*r)*f (x+r)) := by
    rw [show x+l+r = x+r+l by ring,hf]; ring
  simp only [inverseFirst,eq,integral_const_mul]
  ring

private theorem inverse_spec {a : ℝ} (ha : a ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f T) :
    ContDiff ℝ ∞ (inverseFirst a f) ∧ ∀ x, HasDerivAt (inverseFirst a f) (a*inverseFirst a f x+f x) x := by
  let g (x : ℝ) := exp (-a*x)*f x
  have hg : ContDiff ℝ ∞ g := (show ContDiff ℝ ∞ (fun x : ℝ => exp (-a*x)) by fun_prop).mul hf
  let G (x : ℝ) := ∫ y in (0:ℝ)..x, g y
  have dG (x : ℝ) : HasDerivAt G (g x) x := (hg.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have sG : ContDiff ℝ ∞ G := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x => (dG x).differentiableAt,?_⟩
    rw [show deriv G = g from funext fun x => (dG x).deriv]
    exact hg
  let b := exp (-a*T)-1
  have hb : b ≠ 0 := by
    apply sub_ne_zero.mpr
    rw [← Real.exp_zero]
    exact Real.exp_injective.ne (mul_ne_zero (neg_ne_zero.mpr ha) (by positivity))
  have eq : inverseFirst a f = fun x => exp (a*x)*(G (x+T)-G x)/b := by
    funext x
    have e (r : ℝ) : exp (-a*r)*f (x+r) = exp (a*x)*g (r+x) := by
      rw [add_comm x r]; dsimp [g]; rw [← mul_assoc,← Real.exp_add]; ring_nf
    simp only [inverseFirst,e,integral_const_mul,integral_comp_add_right,zero_add]
    rw [show T+x = x+T by ring]
    rw [show G (x+T)-G x = ∫ r in x..x+T, g r from
      integral_interval_sub_left (hg.continuous.intervalIntegrable _ _) (hg.continuous.intervalIntegrable _ _)]
  constructor
  · rw [eq]
    exact ((show ContDiff ℝ ∞ (fun x : ℝ => exp (a*x)) by fun_prop).mul
      ((sG.comp (contDiff_id.add contDiff_const)).sub sG)).div_const b
  · intro x
    have hExp := ((hasDerivAt_id' x).const_mul a).exp
    have ds := (dG (x+T)).comp x ((hasDerivAt_id' x).add_const T)
    rw [eq]
    have result : HasDerivAt (fun y => exp (a*y)*(G (y+T)-G y)/b)
        ((exp (a*x)*(a*1)*(G (x+T)-G x) + exp (a*x)*(g (x+T)*1-g x))/b) x :=
      ((hExp.mul (ds.sub (dG x))).div_const b)
    convert result using 1
    have e : exp (a*x)*exp (-a*x) = 1 := by
      rw [← Real.exp_add,show a*x + -a*x = 0 by ring,Real.exp_zero]
    have boundary : exp (a*x)*(g (x+T)*1-g x) = f x*b := by
      dsimp only [g,b]
      rw [hp x,show -a*(x+T) = -a*x + -a*T by ring,Real.exp_add]
      linear_combination f x*(exp (-a*T)-1)*e
    rw [boundary,mul_one]
    field_simp [hb]

private def inverseMode (a : ℝ) (f : ℝ → ℝ) := inverseFirst a (inverseFirst (-a) f)

private theorem mode_spec {a : ℝ} (ha : a ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f T) :
    ContDiff ℝ ∞ (inverseMode a f) ∧ ∀ x, iteratedDeriv 2 (inverseMode a f) x =
      a^2*inverseMode a f x+f x := by
  obtain ⟨sg,dg⟩ := inverse_spec (neg_ne_zero.mpr ha) hf hp
  have pg : Periodic (inverseFirst (-a) f) T := fun x => by
    simpa using inverse_shift (-a) f (e := 1) (fun w => by simpa using hp w) x
  obtain ⟨su,du⟩ := inverse_spec ha sg pg
  refine ⟨su, fun x => ?_⟩
  have eq : deriv (inverseMode a f) = fun y => a*inverseMode a f y+inverseFirst (-a) f y :=
    funext fun y => (du y).deriv
  have dd := (((du x).const_mul a).add (dg x)).deriv
  rw [show 2 = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,eq]
  change deriv _ x = _
  rw [show deriv (fun y => a*inverseMode a f y+inverseFirst (-a) f y) x = _ from dd]
  dsimp [inverseMode]; ring

private abbrev freq (i : Fin 3) : ℕ := i.val+1

private def waves (A B : Fin 3 → ℝ) (m : ℝ) :=
  ∑ i, (A i*cos ((freq i : ℝ)*m) + B i*sin ((freq i : ℝ)*m))

private theorem trig3_waves (A B : Fin 3 → ℝ) (m c : ℝ) :
    trig3 c (A 0) (B 0) (A 1) (B 1) (A 2) (B 2) m = c + waves A B m := by
  norm_num [trig3,waves,Fin.sum_univ_three,freq]; ring

private theorem waves_mean (A B : Fin 3 → ℝ) : (∫ m in (0:ℝ)..T, waves A B m) = 0 := by
  have eq : waves A B = trig3 0 (A 0) (B 0) (A 1) (B 1) (A 2) (B 2) := by
    funext m; simp [trig3_waves]
  rw [eq]
  have h := trig3_integral_mean 0 (A 0) (B 0) (A 1) (B 1) (A 2) (B 2)
  exact (div_eq_zero_iff.mp h).resolve_right (by positivity)

private def frequencySign (i : Fin 3) : ℝ := (-1)^freq i

private theorem waves_shift (A B : Fin 3 → ℝ) (m : ℝ) :
    waves A B (m+π) = waves (fun i => frequencySign i*A i) (fun i => frequencySign i*B i) m := by
  unfold waves frequencySign
  apply Finset.sum_congr rfl; intro i _
  rw [mul_add,cos_add,sin_add,cos_nat_mul_pi,sin_nat_mul_pi]; ring

private theorem cos_diff (k m : ℝ) : iteratedDeriv 2 (fun r => cos (k*r)) m = -k^2*cos (k*m) := by
  have h (r : ℝ) := (hasDerivAt_id' r).const_mul k
  have eq : deriv (fun r => cos (k*r)) = fun r => -sin (k*r)*(k*1) := funext fun r => (h r).cos.deriv
  rw [show 2 = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,eq,show deriv (fun r => -sin (k*r)*(k*1)) m = _ from ((((h m).sin).neg).mul_const _).deriv]
  ring

private theorem sin_diff (k m : ℝ) : iteratedDeriv 2 (fun r => sin (k*r)) m = -k^2*sin (k*m) := by
  have h (r : ℝ) := (hasDerivAt_id' r).const_mul k
  have eq : deriv (fun r => sin (k*r)) = fun r => cos (k*r)*(k*1) := funext fun r => (h r).sin.deriv
  rw [show 2 = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,eq,((h m).cos.mul_const _).deriv]
  ring

private theorem d2sum (f : Fin 3 → ℝ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (x : ℝ) :
    iteratedDeriv 2 (fun r => ∑ i, f i r) x = ∑ i, iteratedDeriv 2 (f i) x := by
  have h (i : Fin 3) : ContDiffAt ℝ 2 (f i) x := (hf i).contDiffAt.of_le (by simp)
  simp only [Fin.sum_univ_three,iteratedDeriv_fun_add ((h 0).add (h 1)) (h 2),
    iteratedDeriv_fun_add (h 0) (h 1)]

private def corrected (h : ℝ) (A : Fin 3 → ℝ → ℝ) (i : Fin 3) :=
  inverseMode (sqrt h * freq i) (A i)

private theorem corrected_spec {h : ℝ} (hh : 0 < h) {A : Fin 3 → ℝ → ℝ}
    (sm : ∀ i, ContDiff ℝ ∞ (A i)) (per : ∀ i, Periodic (A i) T) (i : Fin 3) :
    ContDiff ℝ ∞ (corrected h A i) ∧ ∀ d, iteratedDeriv 2 (corrected h A i) d =
      h*(freq i : ℝ)^2*corrected h A i d + A i d := by
  have hω : sqrt h * (freq i : ℝ) ≠ 0 := (mul_pos (sqrt_pos.mpr hh) (by positivity)).ne'
  simpa only [corrected,mul_pow,Real.sq_sqrt hh.le] using mode_spec hω (sm i) (per i)

private def flatLap (h : ℝ) (u : ℝ × ℝ → ℝ) (m d : ℝ) :=
  h*iteratedDeriv 2 (fun x => u (x,d)) m + iteratedDeriv 2 (fun x => u (m,x)) d

private def field (A B : Fin 3 → ℝ → ℝ) (p : ℝ × ℝ) := waves (fun i => A i p.2) (fun i => B i p.2) p.1

private theorem smooth_field {A B : Fin 3 → ℝ → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (A i))
    (hb : ∀ i, ContDiff ℝ ∞ (B i)) : ContDiff ℝ ∞ (field A B) := by
  unfold field waves; apply ContDiff.sum; intro i _
  exact ((ha i).comp contDiff_snd |>.mul (by fun_prop)).add
    ((hb i).comp contDiff_snd |>.mul (by fun_prop))

private theorem lap_corrected {h : ℝ} (hh : 0 < h) (A B : Fin 3 → ℝ → ℝ)
    (sa : ∀ i, ContDiff ℝ ∞ (A i)) (sb : ∀ i, ContDiff ℝ ∞ (B i))
    (pa : ∀ i, Periodic (A i) T) (pb : ∀ i, Periodic (B i) T) (m d : ℝ) :
    flatLap h (field (corrected h A) (corrected h B)) m d = field A B (m,d) := by
  let a := corrected h A
  let b := corrected h B
  have hA := corrected_spec hh sa pa
  have hB := corrected_spec hh sb pb
  let c (i : Fin 3) (r : ℝ) := cos ((freq i : ℝ)*r)
  let s (i : Fin 3) (r : ℝ) := sin ((freq i : ℝ)*r)
  have regular₁ (i : Fin 3) : ContDiff ℝ ∞ (fun r => a i d*c i r+b i d*s i r) := by dsimp [c,s]; fun_prop
  have regular₂ (i : Fin 3) : ContDiff ℝ ∞ (fun r => a i r*c i m+b i r*s i m) :=
    ((hA i).1.mul contDiff_const).add ((hB i).1.mul contDiff_const)
  change h*iteratedDeriv 2 (fun r => ∑ i, (a i d*c i r+b i d*s i r)) m +
    iteratedDeriv 2 (fun r => ∑ i, (a i r*c i m+b i r*s i m)) d = _
  rw [d2sum _ regular₁,d2sum _ regular₂,Finset.mul_sum,← Finset.sum_add_distrib]
  unfold field waves
  apply Finset.sum_congr rfl; intro i _
  have da := (hA i).2 d
  have db := (hB i).2 d
  change iteratedDeriv 2 (a i) d = _ at da
  change iteratedDeriv 2 (b i) d = _ at db
  rw [iteratedDeriv_fun_add (f := fun r => a i d*c i r) (g := fun r => b i d*s i r)
    (by dsimp [c]; fun_prop) (by dsimp [s]; fun_prop),
    iteratedDeriv_fun_add (f := fun r => a i r*c i m) (g := fun r => b i r*s i m)
      (((hA i).1.contDiffAt.mul contDiffAt_const).of_le (by simp))
      (((hB i).1.contDiffAt.mul contDiffAt_const).of_le (by simp))]
  simp only [iteratedDeriv_const_mul_field,iteratedDeriv_mul_const_field,da,db,c,s,cos_diff,sin_diff,a,b]
  ring

private def evenPart (f : ℝ → ℝ) (x : ℝ) := (f x+f (-x))/2
private def oddPart (f : ℝ → ℝ) (x : ℝ) := (f x-f (-x))/2

private def cosineSamples (f : ℝ → ℝ) : Fin 3 → ℝ :=
  let b := -evenPart f (π/2)
  let dif := sqrt 2 * evenPart f (π/4)
  ![(f 0-b+dif)/2,b,(f 0-b-dif)/2]

private def sineSamples (f : ℝ → ℝ) : Fin 3 → ℝ :=
  let u := oddPart f (π/4)
  let v := oddPart f (π-π/4)
  let sum := sqrt 2 * (u+v)/2
  let dif := oddPart f (π/2)
  ![(sum+dif)/2,(u-v)/2,(sum-dif)/2]

private theorem recover (A B : Fin 3 → ℝ) :
    cosineSamples (waves A B) = A ∧ sineSamples (waves A B) = B := by
  have shape (x : ℝ) : waves A B x = A 0*cos x + B 0*sin x +
      (A 1*(2*cos x^2-1) + B 1*(2*sin x*cos x)) +
      (A 2*(4*cos x^3-3*cos x) + B 2*(3*sin x-4*sin x^3)) := by
    norm_num [waves,Fin.sum_univ_three,freq,cos_two_mul,sin_two_mul,cos_three_mul,sin_three_mul]
  have s₃ : sqrt 2 ^ 3 = 2*sqrt 2 := by rw [pow_succ,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have s₄ : sqrt 2 ^ 4 = 4 := by rw [show (4:ℕ) = 2*2 by decide,pow_mul,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  constructor <;> ext i <;> fin_cases i <;>
    simp [cosineSamples,sineSamples,evenPart,oddPart,shape,Real.sin_sub,Real.cos_sub,
      Real.cos_pi_div_four,Real.sin_pi_div_four] <;>
    ring_nf <;> norm_num [Real.sq_sqrt,s₃,s₄] <;> ring

private theorem smooth_samples {f : ℝ → ℝ → ℝ} (hf : ∀ x, ContDiff ℝ ∞ (f x)) (i : Fin 3) :
    ContDiff ℝ ∞ (fun d => cosineSamples (fun x => f x d) i) ∧
      ContDiff ℝ ∞ (fun d => sineSamples (fun x => f x d) i) := by
  fin_cases i <;> constructor <;>
    simp [cosineSamples,sineSamples,evenPart,oddPart] <;> fun_prop (disch := exact hf _)

private theorem corrected_shift {h : ℝ} {A : Fin 3 → ℝ → ℝ} {l e : ℝ} {i : Fin 3}
    (hs : ∀ d, A i (d+l) = e*A i d) (d : ℝ) :
    corrected h A i (d+l) = e*corrected h A i d :=
  inverse_shift _ _ (inverse_shift _ _ hs) d

/-- The zero-mean Poisson solution for any smooth torus forcing with rotation
degree at most three and constant rotation mean. The two angle periods are
independent, so this solves the equation on the original torus. -/
theorem exists_potential (h μ : ℝ) (hh : 0 < h) (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ y, Periodic (fun x => f (x,y)) (2*π)) (hq : ∀ x, Periodic (fun y => f (x,y)) (2*π))
    (degree : ∀ d, ∃ a b c e j k : ℝ, ∀ m,
      f (m+d,m-d) = trig3 μ a b c e j k m) :
    ∃ u : ℝ × ℝ → ℝ, ContDiff ℝ ∞ u ∧
      (∀ y, Periodic (fun x => u (x,y)) (2*π)) ∧ (∀ x, Periodic (fun y => u (x,y)) (2*π)) ∧
      (∀ d, (∫ m in (0:ℝ)..2*π, u (m+d,m-d)) = 0) ∧ ∀ m d,
        h*iteratedDeriv 2 (fun x => u (x+d,x-d)) m +
          iteratedDeriv 2 (fun x => u (m+x,m-x)) d = f (m+d,m-d)-μ := by
  let g (m d : ℝ) := f (m+d,m-d)-μ
  let A (i : Fin 3) (d : ℝ) := cosineSamples (fun x => g x d) i
  let B (i : Fin 3) (d : ℝ) := sineSamples (fun x => g x d) i
  have sm (m : ℝ) : ContDiff ℝ ∞ (g m) :=
    (hf.comp ((contDiff_const.add contDiff_id).prodMk (contDiff_const.sub contDiff_id))).sub contDiff_const
  have repr (d : ℝ) : (fun m => g m d) = waves (fun i => A i d) (fun i => B i d) := by
    obtain ⟨a,b,c,e,j,k,eq⟩ := degree d
    let aa : Fin 3 → ℝ := ![a,c,j]
    let bb : Fin 3 → ℝ := ![b,e,k]
    have hg : (fun x => g x d) = waves aa bb := by
      funext m
      change f (m+d,m-d)-μ = _
      rw [eq]
      change trig3 μ (aa 0) (bb 0) (aa 1) (bb 1) (aa 2) (bb 2) m - μ = waves aa bb m
      rw [trig3_waves]; ring
    change _ = waves (cosineSamples _) (sineSamples _)
    rw [hg,(recover aa bb).1,(recover aa bb).2]
  have translate (m d : ℝ) : g m (d+π) = g (m+π) d := by
    have e := hq (m+(d+π)) (m-(d+π))
    change f (m+(d+π),m-(d+π)+T) = f (m+(d+π),m-(d+π)) at e
    dsimp [g]
    rw [show m+π+d=m+(d+π) by ring,show m+π-d=m-(d+π)+T by dsimp [T];ring,e]
  have twist (d : ℝ) :
      (∀ i, A i (d+π) = frequencySign i*A i d) ∧ (∀ i, B i (d+π) = frequencySign i*B i d) := by
    have eq : (fun m => g m (d+π)) = waves (fun i => frequencySign i*A i d) (fun i => frequencySign i*B i d) :=
      funext fun m => (translate m d).trans ((congrFun (repr d) (m+π)).trans (waves_shift _ _ m))
    exact ⟨fun i => congrFun ((congrArg cosineSamples eq).trans (recover _ _).1) i,
      fun i => congrFun ((congrArg sineSamples eq).trans (recover _ _).2) i⟩
  have per (m d : ℝ) : g m (d+T) = g m d := by
    dsimp [g]
    rw [show m+(d+T) = (m+d)+T by ring,show m-(d+T) = (m-d)-T by ring]
    exact congrArg (· - μ) (((hp ((m-d)-T)) (m+d)).trans ((hq (m+d)).sub_eq (m-d)))
  have pA (i : Fin 3) : Periodic (A i) T := fun d => congrFun (congrArg cosineSamples (funext fun m => per m d)) i
  have pB (i : Fin 3) : Periodic (B i) T := fun d => congrFun (congrArg sineSamples (funext fun m => per m d)) i
  let a := corrected h A
  let b := corrected h B
  let v := field a b
  let u (q : ℝ × ℝ) := v ((q.1+q.2)/2,(q.1-q.2)/2)
  have pull (m d : ℝ) : u (m+d,m-d) = v (m,d) := by
    dsimp only [u]; congr 1; congr 1 <;> ring
  have sv : ContDiff ℝ ∞ v := smooth_field (fun i => (corrected_spec hh (fun i => (smooth_samples sm i).1) pA i).1)
    (fun i => (corrected_spec hh (fun i => (smooth_samples sm i).2) pB i).1)
  have deck (m d : ℝ) : v (m+π,d+π) = v (m,d) := by
    unfold v field
    rw [waves_shift]
    have ea (i : Fin 3) : a i (d+π) = frequencySign i*a i d := corrected_shift (fun r => (twist r).1 i) d
    have eb (i : Fin 3) : b i (d+π) = frequencySign i*b i d := corrected_shift (fun r => (twist r).2 i) d
    simp only [ea,eb,← mul_assoc,frequencySign,← mul_pow,neg_one_mul,neg_neg,one_pow,one_mul]
  have pd (m d : ℝ) : v (m,d+T) = v (m,d) := by
    have p {C : Fin 3 → ℝ → ℝ} (hc : ∀ i, Periodic (C i) T) (i : Fin 3) :
        corrected h C i (d+T) = corrected h C i d := by
      simpa using corrected_shift (h := h) (i := i) (e := 1) (fun r => by simpa using hc i r) d
    simp only [v,field,a,b,p pA,p pB]
  refine ⟨u,sv.comp (show ContDiff ℝ ∞ (fun q : ℝ × ℝ => ((q.1+q.2)/2,(q.1-q.2)/2)) by fun_prop),?_,?_,?_,?_⟩
  · intro y x
    dsimp only [u]
    rw [show (x+T+y)/2 = (x+y)/2+π by dsimp [T];ring,show (x+T-y)/2 = (x-y)/2+π by dsimp [T];ring,deck]
  · intro x y
    dsimp only [u]
    rw [show (x+(y+T))/2 = (x+y)/2+π by dsimp [T];ring,show (x-(y+T))/2 = (x-y)/2-π by dsimp [T];ring,
      ← pd ((x+y)/2+π) ((x-y)/2-π),show (x-y)/2-π+T = (x-y)/2+π by dsimp [T];ring,deck]
  · intro d
    simp only [pull]
    exact waves_mean (fun i => a i d) (fun i => b i d)
  · intro m d
    simp only [pull]
    exact (lap_corrected hh A B (fun i => (smooth_samples sm i).1) (fun i => (smooth_samples sm i).2) pA pB m d).trans
      (congrFun (repr d) m).symm

end
end LocalHopf.TorusPoisson
