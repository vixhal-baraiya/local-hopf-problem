import LocalHopf.UniformTube
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Maps.Proper.Basic

/-! # The normal quadratic minimum

The normal Hessian estimate follows from the background growth on the
normal disk. Compactness gives a continuous family of minimizing tilts.
-/
namespace LocalHopf.UniformTube
open Set Filter Metric
open scoped Topology ContDiff
noncomputable section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private def path (x : P) (v : E) (k s : ℝ) : P × E × ℝ := (x,s • v,s*k)

private theorem path_deriv (x : P) (v : E) (k s : ℝ) :
    HasDerivAt (path x v k) (0,v,k) s := by
  have hv : HasDerivAt (fun r : ℝ => r • v) v s := by simpa using (hasDerivAt_id' s).smul_const v
  have hk : HasDerivAt (fun r : ℝ => r*k) k s := by simpa using (hasDerivAt_id' s).mul_const k
  exact HasDerivAt.prodMk (hasDerivAt_const s x) (HasDerivAt.prodMk hv hk)

private def H (F : P × E × ℝ → ℝ) (x : P) := fderiv ℝ (fderiv ℝ F) (x,(0:E),(0:ℝ))

private theorem second_path (F : P × E × ℝ → ℝ) {x : P} (v : E) (k : ℝ)
    (hf : ContDiffAt ℝ 2 F (x,0,0)) :
    iteratedDeriv 2 (F ∘ path x v k) 0 = H F x (0,v,k) (0,v,k) := by
  let γ := path x v k
  let d := ((0,v,k) : P × E × ℝ)
  have h0 : γ 0 = (x,0,0) := by simp [γ,path]
  have hs : ContDiffAt ℝ 2 F (γ 0) := h0 ▸ hf
  have hγ := path_deriv x v k 0
  have ev : deriv (F ∘ γ) =ᶠ[𝓝 0] fun r => fderiv ℝ F (γ r) d := by
    filter_upwards [hγ.continuousAt.tendsto.eventually (hs.eventually (by simp))] with r hr
    exact ((hr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r (path_deriv x v k r)).deriv
  have h2 := ((hs.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hg := (h2.comp_hasDerivAt 0 hγ).clm_apply (hasDerivAt_const (0:ℝ) d)
  rw [show (2:ℕ) = 1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, ev.deriv_eq]
  simpa [H, h0, Function.comp_def, d, γ, path] using hg.deriv

theorem coeff_two_eq_hessian (F : P × E × ℝ → ℝ) {x : P} (v : E)
    (hf : ContDiffAt ℝ 2 F (x,0,0)) :
    coeff F 2 x v = fderiv ℝ (fderiv ℝ F) (x,0,0) (0,v,1) (0,v,1) / 2 := by
  have he : (fun r => ray F ((x,v),r)) = F ∘ path x v 1 := by ext r; simp [ray,path]
  change iteratedDeriv 2 _ 0 / _ = _
  rw [he,second_path F v 1 hf]
  norm_num [H,Nat.factorial]

/-- Second derivative test in the direction needed for a quadratic lower bound. -/
private theorem second_nonneg (f : ℝ → ℝ) (reg : ContDiffAt ℝ 2 f 0) (hmin : IsLocalMin f 0) :
    0 ≤ iteratedDeriv 2 f 0 := by
  by_contra! h
  have hF := (reg.iteratedFDeriv_right (m := 0) (i := 2) (by norm_num)).continuousAt
  have hc : ContinuousAt (iteratedDeriv 2 f) 0 := by
    change ContinuousAt (fun r => (iteratedFDeriv ℝ 2 f r) (fun _ => 1)) 0
    exact (continuous_eval_const (fun _ : Fin 2 => (1:ℝ))).continuousAt.comp hF
  have ev : ∀ᶠ r in 𝓝 (0:ℝ), (f 0 ≤ f r ∧ iteratedDeriv 2 f r < 0) ∧ ContDiffAt ℝ 2 f r :=
    (hmin.and (hc.eventually_lt continuousAt_const h)).and (reg.eventually (by norm_num))
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp ev
  let s := ε/2
  have hs : 0 < s := by dsimp [s]; positivity
  have seg (r : ℝ) (hr : r ∈ Icc 0 s) : r ∈ ball 0 ε := by
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hr.1]
    dsimp [s] at hr; linarith [hr.2]
  have regOn : ContDiffOn ℝ 2 f (uIcc 0 s) := by
    rw [uIcc_of_le hs.le]
    exact fun r hr => (he (seg r hr)).2.contDiffWithinAt
  obtain ⟨r,hr,Hr⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hs.ne regOn
  rw [uIoo_of_lt hs] at hr
  have hneg := (he (seg r ⟨hr.1.le,hr.2.le⟩)).1.2
  have hle := (he (seg s ⟨hs.le,le_rfl⟩)).1.1
  rw [uIcc_of_le hs.le, taylorWithinEval_succ _ 0, taylor_within_zero_eval,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hs) (reg.of_le (by norm_num))
      (left_mem_Icc.mpr hs.le), iteratedDeriv_one, hmin.deriv_eq_zero] at Hr
  norm_num at Hr
  nlinarith [mul_neg_of_neg_of_pos hneg (sq_pos_of_pos hs)]

/-- The normal Hessian inherits the quantitative growth constant of the background. -/
theorem normal_second_lower (F : P × E × ℝ → ℝ) {x : P} {δ lam : ℝ}
    (hδ : 0 < δ) (hf : ContDiffAt ℝ 2 F (x,0,0)) (hf0 : F (x,0,0) = 0)
    (h₀ : ∀ z : E, ‖z‖ ≤ δ → lam*‖z‖^2 ≤ F (x,z,0)) (v : E) :
    2*lam*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ F) (x,0,0) (0,v,0) (0,v,0) := by
  change _ ≤ H F x (0,v,0) (0,v,0)
  let f := F ∘ path x v 0
  let c := lam*‖v‖^2
  let q (r : ℝ) := c*r^2
  have reg : ContDiffAt ℝ 2 f 0 := (show ContDiffAt ℝ 2 F (path x v 0 0) by simpa [path] using hf).comp 0
    (f := path x v 0) (by unfold path; fun_prop)
  have rq : ContDiff ℝ 2 q := by dsimp [q]; fun_prop
  have hm : IsLocalMin (f-q) 0 := by
    have ev : ∀ᶠ r : ℝ in 𝓝 0, ‖r • v‖ < δ :=
      (continuous_id.smul continuous_const).norm.continuousAt.eventually_lt continuousAt_const (by simpa using hδ)
    filter_upwards [ev] with r hr
    have h := h₀ (r • v) hr.le
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at h
    simp [f,q,c,path,hf0]
    linarith
  have hs := second_nonneg _ (reg.sub rq.contDiffAt) hm
  have dd : iteratedDeriv 2 q 0 = 2*c := by
    norm_num [q,iteratedDeriv_const_mul_field,iteratedDeriv_pow]
    ring
  change 0 ≤ iteratedDeriv 2 (f-q) 0 at hs
  rw [iteratedDeriv_sub reg rq.contDiffAt, dd, second_path F v 0 hf] at hs
  dsimp [c] at hs
  linarith

private theorem quadratic_growth (F : P × E × ℝ → ℝ) {x : P} {lam : ℝ}
    (hf : ContDiffAt ℝ 2 F (x,0,0))
    (hn : ∀ z : E, 2*lam*‖z‖^2 ≤ H F x (0,z,0) (0,z,0)) (z : E) :
    coeff F 2 x 0 + lam*‖z‖^2 - ‖H F x‖*‖z‖ ≤ coeff F 2 x z := by
  let L := H F x
  let a := ((0,z,0) : P × E × ℝ)
  let e := ((0,0,1) : P × E × ℝ)
  have cross (u v : P × E × ℝ) : ‖L u v‖ ≤ ‖L‖*‖u‖*‖v‖ :=
    ((L u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (L.le_opNorm u) (norm_nonneg _))
  have h1 : - (‖L‖*‖z‖) ≤ L a e := by
    have h := (abs_le.mp (cross a e)).1
    simpa [a,e,Prod.norm_def] using h
  have h2 : - (‖L‖*‖z‖) ≤ L e a := by
    have h := (abs_le.mp (cross e a)).1
    simpa [a,e,Prod.norm_def] using h
  have ha : a+e = (0,z,1) := by simp [a,e]
  rw [coeff_two_eq_hessian F z hf,coeff_two_eq_hessian F 0 hf]
  change L e e / 2 + _ - _ ≤ L (0,z,1) (0,z,1) / 2
  rw [← ha,L.map_add,add_apply,map_add,map_add]
  have h := hn z
  change 2*lam*‖z‖^2 ≤ L a a at h
  change _ + _ - ‖L‖*‖z‖ ≤ _
  linarith

private theorem quadratic_gap (F : P × E × ℝ → ℝ) {x : P} {lam : ℝ}
    (hf : ContDiffAt ℝ 2 F (x,0,0))
    (hn : ∀ z : E, 2*lam*‖z‖^2 ≤ H F x (0,z,0) (0,z,0))
    {a : E} (ha : ∀ z, coeff F 2 x a ≤ coeff F 2 x z) (b : E) :
    coeff F 2 x a + (lam/2)*‖b-a‖^2 ≤ coeff F 2 x b := by
  let L := H F x
  let A := ((0,a,1) : P × E × ℝ)
  let B := ((0,b,1) : P × E × ℝ)
  have hm := ha ((1/2:ℝ) • (a+b))
  have hd := hn (b-a)
  have d : B-A = (0,b-a,0) := by simp [A,B]
  have m : (1/2:ℝ) • (A+B) = (0,(1/2:ℝ) • (a+b),1) := by
    ext <;> simp [A,B]
    norm_num
  rw [coeff_two_eq_hessian F a hf,coeff_two_eq_hessian F _ hf] at hm ⊢
  change L A A / 2 ≤ L (0,_,1) (0,_,1) / 2 at hm
  rw [← m, L.map_smul,smul_apply,map_smul,
    L.map_add,add_apply,map_add,map_add] at hm
  change 2*lam*‖b-a‖^2 ≤ L (0,b-a,0) (0,b-a,0) at hd
  rw [← d,L.map_sub,sub_apply,map_sub,map_sub] at hd
  change L A A / 2 + _ ≤ L B B / 2
  simp only [smul_eq_mul] at hm
  linarith

/-- Quadratic growth of the background supplies a continuous minimizing tilt on
the entire compact chart, including its boundary. -/
theorem exists_center [ProperSpace E] (F : P × E × ℝ → ℝ) {K : Set P}
    (hK : IsCompact K) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 < lam)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 2 F (x,0,0))
    (hflat : ∀ x ∈ K, F (x,0,0) = 0)
    (h₀ : ∀ x ∈ K, ∀ z : E, ‖z‖ ≤ δ → lam*‖z‖^2 ≤ F (x,z,0)) :
    ∃ center : P → E, ContinuousOn center K ∧ ∀ x ∈ K, ∀ z,
      coeff F 2 x (center x) + (lam/2)*‖z-center x‖^2 ≤ coeff F 2 x z := by
  classical
  have hH : ContinuousOn (H F) K := by
    intro x hx
    exact (((hf x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt.comp_continuousWithinAt (f := fun y : P => (y,(0:E),(0:ℝ))) (by fun_prop)
  have hn (x : P) (hx : x ∈ K) := normal_second_lower F hδ (hf x hx) (hflat x hx) (h₀ x hx)
  have hN : ContinuousOn (fun x => ‖H F x‖) K := by
    intro x hx
    exact ContinuousWithinAt.norm (f := H F) (hH x hx)
  obtain ⟨b,bd⟩ := (hK.image_of_continuousOn hN).bddAbove
  let R := 1+max b 0 / lam
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let S := closedBall (0:E) R
  let Q (x : K) (z : E) := coeff F 2 x.val z
  have cont : Continuous (Function.uncurry Q) := by
    let L := fun w : K × E => H F w.1.val
    let v := fun w : K × E => ((0,w.2,1) : P × E × ℝ)
    have cl : Continuous L := (continuousOn_iff_continuous_domRestrict.mp hH).comp continuous_fst
    have cv : Continuous v := by dsimp [v]; fun_prop
    have eq : Function.uncurry Q = fun w => L w (v w) (v w) / 2 :=
      funext fun w => coeff_two_eq_hessian F _ (hf _ w.1.property)
    rw [eq]
    exact ((cl.clm_apply cv).clm_apply cv).div_const _
  have small (x : K) : ∃ a ∈ S, ∀ z : E, Q x a ≤ Q x z := by
    obtain ⟨a,ha,hm⟩ := (isCompact_closedBall (0:E) R).exists_isMinOn
      ⟨0,by simpa [S] using hR⟩ ((cont.comp (f := fun z : E => (x,z)) (by fun_prop)).continuousOn)
    refine ⟨a,ha,fun z => ?_⟩
    by_cases hz : z ∈ S
    · exact hm hz
    have hr : R < ‖z‖ := by simpa [S] using hz
    have hh : ‖H F x.val‖ ≤ max b 0 := (bd ⟨x.val,x.property,rfl⟩).trans (le_max_left ..)
    have hb : ‖H F x.val‖ ≤ lam*‖z‖ := by
      have hdiv : max b 0 / lam ≤ ‖z‖ := by dsimp [R] at hr; linarith
      have := (div_le_iff₀ hlam).mp hdiv
      linarith
    have hg := quadratic_growth F (hf _ x.property) (hn _ x.property) z
    exact (hm (show (0:E) ∈ S by simpa [S] using hR)).trans (by
      dsimp [Q]; nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg z)])
  choose a ha hm using small
  let c (x : K) : S := ⟨a x,ha x⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall ..)
  have gap (x : K) (z : E) := quadratic_gap F (hf _ x.property) (hn _ x.property) (hm x) z
  have cc : Continuous c := by
    apply continuous_of_isClosed_graph
    have he : c.graph = ⋂ v : S, {w : K × S | Q w.1 w.2.val ≤ Q w.1 v.val} := by
      ext w
      simp only [mem_iInter,mem_ofPred_eq]
      constructor
      · intro h v
        rcases w with ⟨x,z⟩
        change c x = z at h
        subst z
        exact hm x v.val
      · intro h
        have hi := h (c w.1)
        have hg := gap w.1 w.2.val
        change coeff F 2 w.1.val w.2.val ≤ coeff F 2 w.1.val (a w.1) at hi
        have hz : ‖w.2.val-a w.1‖ = 0 := by
          by_contra! hn'
          nlinarith [mul_pos (half_pos hlam) (sq_pos_of_ne_zero hn')]
        exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
    rw [he]
    apply isClosed_iInter
    intro v
    exact isClosed_le (cont.comp (f := fun w : K × S => (w.1,w.2.val)) (by fun_prop))
      (cont.comp (f := fun w : K × S => (w.1,v.val)) (by fun_prop))
  let center (x : P) := if hx : x ∈ K then a ⟨x,hx⟩ else 0
  refine ⟨center,?_,?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    simpa [Set.domRestrict,center,c,Function.comp_def] using continuous_subtype_val.comp cc
  · intro x hx z
    simpa [center,hx] using gap ⟨x,hx⟩ z

/-- Lemma 3.1 for a compact parameter set. Every displacement satisfies the
lower bound, and evaluation at `s • center x` attains the expansion up to a
uniform fourth-order error. In particular a true fiber minimum has this expansion. -/
theorem minimum_expansion [ProperSpace E] (F : P × E × ℝ → ℝ) {K : Set P}
    (hK : IsCompact K) {δ η lam : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hlam : 0 < lam)
    (hsmooth : ∀ q ∈ disk (E := E) K δ η, ContDiffAt ℝ 4 F q)
    (hflat : ∀ x ∈ K, F (x,0,0) = 0)
    (h₀ : ∀ x ∈ K, ∀ z : E, ‖z‖ ≤ δ → lam*‖z‖^2 ≤ F (x,z,0))
    (h₁ : ∀ x ∈ K, deriv (fun r => F (x,0,r)) 0 = 0) :
    ∃ center : P → E, ContinuousOn center K ∧
      (∀ x ∈ K, ∀ ζ, coeff F 2 x (center x) + (lam/2)*‖ζ-center x‖^2 ≤ coeff F 2 x ζ) ∧
      ∃ C ≥ 0, ∃ ε > 0, ∀ x ∈ K, ∀ s ∈ Ioo 0 ε,
        let target := s^2*coeff F 2 x (center x) + s^3*coeff F 3 x (center x)
        (∀ z : E, ‖z‖ ≤ δ → target - C*s^4 ≤ F (x,z,s)) ∧
        ∃ m ∈ closedBall (0:E) δ, IsMinOn (fun z => F (x,z,s)) (closedBall 0 δ) m ∧
          |F (x,m,s)-target| ≤ C*s^4 := by
  have reg (x : P) (hx : x ∈ K) : ContDiffAt ℝ 4 F (x,0,0) :=
    hsmooth _ ⟨hx,by simpa using hδ.le,le_rfl,hη.le⟩
  obtain ⟨center,hc,hq⟩ := exists_center F hK hδ hlam (fun x hx => (reg x hx).of_le (by norm_num)) hflat h₀
  refine ⟨center,hc,hq,?_⟩
  obtain ⟨A,hA,low⟩ := lower_bound F hK hδ hη hlam (half_pos hlam) hsmooth hflat h₀ h₁ center hc hq
  obtain ⟨b,hb⟩ := (hK.image_of_continuousOn hc.norm).bddAbove
  let R := max b 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨B,_,expan⟩ := rescaled_expansion F hK R hsmooth
  refine ⟨max A B,hA.trans (le_max_left ..),min (min η 1) (δ/R),
    lt_min (lt_min hη one_pos) (div_pos hδ hR),?_⟩
  intro x hx s hs target
  have hηs : s ≤ min η 1 := hs.2.le.trans (min_le_left ..)
  have hlo (z : E) (hz : ‖z‖ ≤ δ) : target-max A B*s^4 ≤ F (x,z,s) := by
    have := low x hx z s hz ⟨hs.1.le,hηs⟩
    dsimp [target]
    linarith [mul_le_mul_of_nonneg_right (le_max_left A B) (pow_nonneg hs.1.le 4)]
  refine ⟨hlo,?_⟩
  have hcR : ‖center x‖ ≤ R := by
    have hh := (hb ⟨x,hx,rfl⟩).trans (le_max_left b 0)
    dsimp [R]; linarith
  have hδs : ‖s • center x‖ ≤ δ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs.1]
    exact (mul_le_mul_of_nonneg_left hcR hs.1.le).trans
      ((le_div_iff₀ hR).mp (hs.2.le.trans (min_le_right ..)))
  have hev := expan x hx (center x) s hcR hδs hs.1 (hηs.trans (min_le_left ..))
  rw [coeff_zero,hflat x hx,first_coeff_zero F hδ hlam.le (reg x hx) (hflat x hx) (h₀ x hx) (h₁ x hx)] at hev
  have H : ContinuousOn (fun z : E => F (x,z,s)) (closedBall 0 δ) := by
    intro z hz
    exact (hsmooth _ ⟨hx,hz,hs.1.le,hηs.trans (min_le_left ..)⟩).continuousAt.comp_continuousWithinAt
      (f := fun z : E => (x,z,s)) (by fun_prop)
  obtain ⟨m,hm,hmin⟩ := (isCompact_closedBall (0:E) δ).exists_isMinOn
    ⟨0,by simpa using hδ.le⟩ H
  refine ⟨m,hm,hmin,abs_le.mpr ⟨?_,?_⟩⟩
  · linarith [hlo m (by simpa using hm)]
  · have hu := hmin (show s • center x ∈ closedBall 0 δ by simpa using hδs)
    have h := (abs_le.mp hev).2
    dsimp [target]
    dsimp at hu
    linarith [mul_le_mul_of_nonneg_right (le_max_right A B) (pow_nonneg hs.1.le 4)]

end
end LocalHopf.UniformTube
