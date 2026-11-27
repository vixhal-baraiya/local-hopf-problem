import LocalHopf.RegularTransition

/-! Regularity of the fixed-base graph as the transverse chart displaces its base point. -/
namespace LocalHopf.BackgroundGrowth.Transverse
open Real Matrix Filter Set SphereProduct JetChart
open scoped ContDiff Topology
noncomputable section

private def scriptPair (u : FlatLocus.Representative) (z : Tilts) : TangentPair :=
  let r := align _ _ u.property.1
  let s := align _ _ u.property.2
  let p := (chart r s).symm 0
  ⟨p,field r s ((1,0),z 0,z 1) p,field r s ((0,1),z 2,z 3) p⟩

private theorem script_data (u : FlatLocus.Representative) (z : Tilts) :
    let n := u.val.1.val
    let p := u.val.2.1.val
    let q := u.val.2.2.val
    frameData (scriptPair u z) =
      ((p,q),((n ⨯₃ p)+z 0 • n,(n ⨯₃ q)+z 1 • n),(-(n ⨯₃ p)+z 2 • n,(n ⨯₃ q)+z 3 • n)) := by
  intro n p q
  let r := align _ _ u.property.1
  let s := align _ _ u.property.2
  let base := (chart r s).symm 0
  have vel (d : Params) : ambientVelocityL base (field r s d base) =
      ((d.1.1-d.1.2) • (n ⨯₃ p)+d.2.1 • n,(d.1.1+d.1.2) • (n ⨯₃ q)+d.2.2 • n) := by
    have h0 := (JetChart.center u).1
    have D := ambient_field r s ((chart r s).map_target h0) d
    rw [(chart r s).right_inv h0] at D
    exact D.trans (center_velocity u d)
  have b : ambientPoint base = (p,q) := by rw [show base = _ from (JetChart.center u).2]; rfl
  change (ambientPoint base,ambientVelocityL base (field r s _ base),ambientVelocityL base (field r s _ base)) = _
  rw [b,vel,vel]
  norm_num

theorem regularBase_zero (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) :
    regularBase v reg 0=v := by rw [regularBase,dite_eq_left (by norm_num : |(0:ℝ)|<1),movingRepresentative_zero]

/-- Curvature in graph coordinates at a displaced regular base point, with height and metric parameters independent. -/
def regularFamily (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (A : Fin 4 → AmbientTensor) (q : ℝ × Tilts × ℝ) := (scriptPair (regularBase v reg q.1) q.2.1).numerator A q.2.2

theorem regularFamily_smooth (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) {h : ℝ} (hh : |h|<1) (z : Tilts) :
    ContDiffAt ℝ ∞ (regularFamily v reg (paperCoefficients t ht χ)) (h,z,0) := by
  let W (q : ℝ × Tilts × ℝ) := scriptPair (regularBase v reg q.1) q.2.1
  apply moving_numerator_smooth (w := W) (h := fun q : ℝ × Tilts × ℝ => q.2.2) (paper_metrics_realize t ht χ) _ (by fun_prop)
  let p := v.val.2.1.val
  let n (u : ℝ × Tilts × ℝ) := movingNormal v u.1
  let q (u : ℝ × Tilts × ℝ) := point v.val.1.val v.val.2.2.val u.1
  have hn : ContDiffAt ℝ ∞ n (h,z,0) := (movingNormal_smooth v hh).comp (h,z,0) (f := fun u : ℝ × Tilts × ℝ => u.1) (by fun_prop)
  have rad : 0<1-h^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one ..).mpr hh)
  have hq : ContDiffAt ℝ ∞ q (h,z,0) := by
    change ContDiffAt ℝ ∞ (fun w : ℝ × Tilts × ℝ => sqrt (1-w.1^2) • v.val.2.2.val+w.1 • v.val.1.val) _
    fun_prop (disch := exact rad.ne')
  have l := Cheeger.smooth_cross.contDiffAt.comp (h,z,0) (hn.prodMk (contDiffAt_const (c := p)))
  have m := Cheeger.smooth_cross.contDiffAt.comp (h,z,0) (hn.prodMk hq)
  have tz (i : Fin 4) : ContDiffAt ℝ ∞ (fun w : ℝ × Tilts × ℝ => w.2.1 i) (h,z,0) := by fun_prop
  let G (u : ℝ × Tilts × ℝ) : AmbientPairData :=
    ((p,q u),((n u ⨯₃ p)+u.2.1 0 • n u,(n u ⨯₃ q u)+u.2.1 1 • n u),(-(n u ⨯₃ p)+u.2.1 2 • n u,(n u ⨯₃ q u)+u.2.1 3 • n u))
  have sm : ContDiffAt ℝ ∞ G (h,z,0) := (contDiffAt_const.prodMk hq).prodMk
    (((l.add ((tz 0).smul hn)).prodMk (m.add ((tz 1).smul hn))).prodMk
      ((l.neg.add ((tz 2).smul hn)).prodMk (m.add ((tz 3).smul hn))))
  apply sm.congr_of_eventuallyEq
  have near : ∀ᶠ u : ℝ × Tilts × ℝ in 𝓝 (h,z,0), |u.1|<1 := continuous_fst.abs.continuousAt.eventually_lt_const hh
  filter_upwards [near] with u hu
  change frameData (scriptPair (regularBase v reg u.1) u.2.1) = _
  rw [script_data]
  simp only [regularBase,dite_eq_left hu]
  rfl

theorem regularFamily_coeff (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) (h : ℝ) (a : Tilts) (n : ℕ) :
    let u := regularBase v reg h
    let r := align _ _ u.property.1
    let s := align _ _ u.property.2
    let p := (chart r s).symm 0
    let e (i : Fin 4) := field r s (parameterBasis i) p
    let A := paperCoefficients t ht χ
    UniformTube.coeff (regularFamily v reg A) n h a = graphCoefficient A (e 0) (e 1) (e 2) (e 3) n a := by
  intro u r s p e A
  let F := graphNumerator A (e 0) (e 1) (e 2) (e 3)
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target (JetChart.center u).1)
  have eq (z : Tilts) : scriptPair u z = tiltedPair (e 0) (e 1) (e 2) (e 3) z := by
    have two (i : Fin 4) (q : Params) (x y : ℝ) (eq : parameterBasis i+x • parameterBasis 2+y • parameterBasis 3=q) :
        field r s q p=e i+x • e 2+y • e 3 := by
      have H := congrArg L eq
      simp only [map_add,map_smul] at H
      simpa only [hL] using H.symm
    have l := two 0 ((1,0),z 0,z 1) (z 0) (z 1) (by ext <;> simp [parameterBasis_apply])
    have m := two 1 ((0,1),z 2,z 3) (z 2) (z 3) (by ext <;> simp [parameterBasis_apply])
    change TangentPair.mk p _ _ = ⟨p,_,_⟩
    rw [l,m]
  have ray : (fun s : ℝ => regularFamily v reg A (h,s • a,s)) = fun s => F (0,s • a,s) := by
    funext s
    change (scriptPair u _).numerator A s = _
    rw [eq]
    rfl
  calc
    _ = UniformTube.coeff F n 0 a := congrArg (fun f : ℝ → ℝ => iteratedDeriv n f 0 / (n.factorial : ℝ)) ray
    _ = _ := graph_coeff_eq_quotient t ht χ p (e 0) (e 1) (e 2) (e 3) a n

private theorem background_nonneg (t : ℝ) (ht : 0≤t) (w : TangentPair) :
    0 ≤ curvatureNumerator (backgroundMetric t ht) w.point w.first w.second := by
  let d := frameData w
  let X := Cheeger.operator d.1.1 d.1.2 t ht d.2.1
  let Y := Cheeger.operator d.1.1 d.1.2 t ht d.2.2
  have back : d = ((d.1.1,d.1.2),Cheeger.inverseOperator d.1.1 d.1.2 t X,Cheeger.inverseOperator d.1.1 d.1.2 t Y) := by
    simp [X,Y,Cheeger.inverse_operator]
  have b := intrinsic_background_comparison t ht w _ _ X Y back
  have pos : 0 ≤ zillerLower d.1.1 d.1.2 t X Y := add_nonneg (add_nonneg (sqLength_nonneg _) (sqLength_nonneg _))
    (mul_nonneg (by positivity) (sqLength_nonneg _))
  linarith only [pos,b]

theorem regularFamily_flat (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) (h : ℝ) :
    regularFamily v reg (paperCoefficients t ht χ) (h,0,0) = 0 := by
  let u := regularBase v reg h
  change (scriptPair u 0).numerator _ 0 = 0
  rw [TangentPair.numerator_eq _ (background_zero t ht χ)]
  exact flat_torus_curvature u (JetChart.center u).1 rfl t ht (1,0) (0,1)

/-- The entire first derivative vanishes on the family of core planes, including in the base direction. -/
theorem regularFamily_critical (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) {h : ℝ} (hh : |h|<1) :
    fderiv ℝ (regularFamily v reg (paperCoefficients t ht χ)) (h,0,0) = 0 := by
  let A := paperCoefficients t ht χ
  let F := regularFamily v reg A
  let L := fderiv ℝ F (h,0,0)
  have diff := ((regularFamily_smooth v reg t ht χ hh 0).differentiableAt (by simp)).hasFDerivAt
  have line (b k : ℝ) (a : Tilts) : HasDerivAt (fun s : ℝ => (h+s*b,s • a,s*k)) (b,a,k) 0 := by
    have d : HasDerivAt (fun s : ℝ => h+s*b) b 0 := by simpa using ((hasDerivAt_id' (0:ℝ)).mul_const b).const_add h
    exact d.prodMk
      ((show HasDerivAt (fun s : ℝ => s • a) a 0 by simpa using (hasDerivAt_id' (0:ℝ)).smul_const a).prodMk
        (show HasDerivAt (fun s : ℝ => s*k) k 0 by simpa using (hasDerivAt_id' (0:ℝ)).mul_const k))
  have comp (b k : ℝ) (a : Tilts) : HasDerivAt (fun s : ℝ => F (h+s*b,s • a,s*k)) (L (b,a,k)) 0 := by
    have hd : HasFDerivAt F L ((fun s : ℝ => (h+s*b,s • a,s*k)) 0) := by simpa [F,A,L] using diff
    exact hd.comp_hasDerivAt 0 (line b k a)
  have bg (b : ℝ) (a : Tilts) : L (b,a,0)=0 := by
    apply IsLocalMin.hasDerivAt_eq_zero _ (comp b 0 a)
    apply Filter.Eventually.of_forall
    intro s
    simp only [zero_mul,add_zero,zero_smul,mul_zero]
    rw [show F (h,0,0)=0 from regularFamily_flat v reg t ht χ h]
    change 0≤(scriptPair _ _).numerator _ 0
    rw [TangentPair.numerator_eq _ (background_zero t ht χ)]
    exact background_nonneg ..
  let u := regularBase v reg h
  have time : HasDerivAt (fun s : ℝ => F (h,0,s)) 0 0 :=
    flat_torus_first u (JetChart.center u).1 rfl t ht χ (1,0) (0,1)
  have last : L (0,0,1)=0 := (show HasDerivAt (fun s : ℝ => F (h,0,s)) (L (0,0,1)) 0 by simpa using comp 0 1 0).unique time
  apply ContinuousLinearMap.ext
  rintro ⟨b,a,k⟩
  change L (b,a,k)=0
  have split : (b,a,k) = ((b,a,0) : ℝ × Tilts × ℝ) + k • (0,0,1) := by simp
  rw [split,L.map_add,L.map_smul,bg,last,smul_zero,add_zero]

private abbrev Dom := ℝ × Tilts × ℝ

/-- On a critical curve the acceleration term disappears from the second derivative. -/
private theorem second_path_critical (F : Dom → ℝ) (γ : ℝ → Dom) (d : Dom)
    (hγ : ContDiffAt ℝ 2 γ 0) (vel : HasDerivAt γ d 0)
    (hf : ContDiffAt ℝ 2 F (γ 0)) (crit : fderiv ℝ F (γ 0)=0) :
    iteratedDeriv 2 (F ∘ γ) 0 = fderiv ℝ (fderiv ℝ F) (γ 0) d d := by
  rw [iteratedDeriv_vcomp_two hf hγ,crit,zero_apply,add_zero,vel.deriv,iteratedFDeriv_two_apply]

private theorem regular_hessian_normal (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) (b : ℝ) (a : Tilts) :
    let F := regularFamily v reg (paperCoefficients t ht χ)
    let H := fderiv ℝ (fderiv ℝ F) (0,0,0)
    H (b,a,1) (b,a,1)=H (0,a,1) (0,a,1) := by
  intro F H
  have hf : ContDiffAt ℝ 2 F (0,0,0) := (regularFamily_smooth v reg t ht χ (h := 0) (by norm_num) 0).of_le (by simp)
  let γ (s : ℝ) : Dom := (s*b,0,0)
  have vel : HasDerivAt γ (b,0,0) 0 := (show HasDerivAt (fun s : ℝ => s*b) b 0 by simpa using (hasDerivAt_id' (0:ℝ)).mul_const b).prodMk
    (hasDerivAt_const (0:ℝ) ((0,0):Tilts × ℝ))
  have h0 : γ 0=(0,0,0) := by simp [γ]
  have near : (fderiv ℝ F ∘ γ) =ᶠ[𝓝 0] 0 := by
    have step : ∀ᶠ s : ℝ in 𝓝 0, |s*b|<1 := (continuous_id.mul continuous_const).abs.continuousAt.eventually_lt_const (by simp)
    filter_upwards [step] with s hs
    exact regularFamily_critical v reg t ht χ hs
  have dg := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have d0 := (h0 ▸ dg : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (γ 0)) (γ 0))
  have d := (d0.comp_hasDerivAt 0 vel).deriv
  have vanish : H (b,0,0) = 0 := by simpa only [h0,near.deriv_eq,deriv_zero,Pi.zero_apply] using d.symm
  have symm : H (0,a,1) (b,0,0)=H (b,0,0) (0,a,1) := hf.isSymmSndFDerivAt (by simp) _ _
  have split : (b,a,1) = ((b,0,0):Dom)+(0,a,1) := by simp
  rw [split,H.map_add,vanish,zero_add,map_add,symm,vanish,zero_apply,zero_add]

/-- The quadratic coefficient in the compact chart is the regular-fiber quadratic evaluated
at the linearized graph velocity. Moving the base and multiplying by the changing area
have no second-order contribution on the critical flat family. -/
theorem transverse_quadratic_eq_regular (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) (a : Tilts) :
    let A := paperCoefficients t ht χ
    let F := (compactNormalChart t).curvature A
    UniformTube.coeff F 2 (rawCore v) a = (Profiles.hh t)^2/4 *
      UniformTube.coeff (regularFamily v reg A) 2 0 (fderiv ℝ (transverseGraph v t) 0 a) := by
  intro A F
  let G := regularFamily v reg A
  let z (s : ℝ) := s • a
  let b := fderiv ℝ (transverseGraph v t) 0 a
  let γ (s : ℝ) : Dom := (s*(a 2),transverseGraph v t (z s),s)
  let k (s : ℝ) := (transverseDet v t (z s))^2
  let f (s : ℝ) := (longitudePair t ((compactNormalChart t).frame (rawCore v,z s))).numerator A s
  have dz : HasDerivAt z a 0 := by simpa [z] using (hasDerivAt_id' (0:ℝ)).smul_const a
  have z0 : z 0=0 := zero_smul ..
  obtain ⟨det0,g0⟩ := transverseGraph_at_core v t ht
  obtain ⟨ds,gs⟩ := transverseGraph_smooth v t ht
  have eq : f =ᶠ[𝓝 0] (k * (G ∘ γ)) := by
    filter_upwards [dz.continuousAt.tendsto.eventually (z0 ▸ regular_transition v t ht reg),paper_metrics_realize t ht χ] with h step ⟨g,hg⟩
    obtain ⟨hz,_,_,K⟩ := step
    change (longitudePair t ((compactNormalChart t).frame (rawCore v,z h))).numerator A h =
      k h*(scriptPair (regularBase v reg (z h 2)) (transverseGraph v t (z h))).numerator A h
    rw [TangentPair.numerator_eq _ hg,TangentPair.numerator_eq _ hg,K g]
    rw [regularBase,dite_eq_left hz]
    rfl
  have hz : ContDiffAt ℝ ∞ z 0 := by unfold z; fun_prop
  have dgs := (show ContDiffAt ℝ ∞ (transverseGraph v t) (z 0) by rwa [z0]).comp 0 hz
  have dds := (show ContDiffAt ℝ ∞ (transverseDet v t) (z 0) by rwa [z0]).comp 0 hz
  have dgraph := ((show ContDiffAt ℝ ∞ (transverseGraph v t) (z 0) by rwa [z0]).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 dz
  have vel : HasDerivAt γ (a 2,b,1) 0 := (show HasDerivAt (fun s : ℝ => s*(a 2)) (a 2) 0 by simpa using (hasDerivAt_id' (0:ℝ)).mul_const (a 2)).prodMk
    ((show HasDerivAt (transverseGraph v t ∘ z) b 0 by simpa only [z0] using dgraph).prodMk (hasDerivAt_id' (0:ℝ)))
  have path : ContDiffAt ℝ 2 γ 0 := (show ContDiffAt ℝ ∞ (fun s : ℝ => s*(a 2)) 0 by fun_prop).prodMk (dgs.prodMk contDiffAt_id) |>.of_le (by simp)
  have start : γ 0=(0,0,0) := by simp [γ,z0,g0]
  have smooth : ContDiffAt ℝ 2 G (γ 0) := by rw [start]; exact (regularFamily_smooth v reg t ht χ (h := 0) (by norm_num) 0).of_le (by simp)
  have critical : fderiv ℝ G (γ 0)=0 := by rw [start]; exact regularFamily_critical v reg t ht χ (by norm_num)
  have val : (G ∘ γ) 0=0 := by simpa only [Function.comp_apply,start] using regularFamily_flat v reg t ht χ 0
  have slope : deriv (G ∘ γ) 0=0 := by rw [((smooth.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 vel).deriv,critical,zero_apply]
  have one : k 0=1 := by simp [k,z0,det0]
  have weighted : iteratedDeriv 2 f 0 = iteratedDeriv 2 (G ∘ γ) 0 := by
    rw [eq.iteratedDeriv_eq,iteratedDeriv_mul (show ContDiffAt ℝ 2 k 0 from (dds.pow 2).of_le (by simp)) (smooth.comp 0 path)]
    have val' : G (γ 0)=0 := val
    norm_num [Finset.sum_range_succ,iteratedDeriv_one,slope,val',one]
  have normal := regular_hessian_normal v reg t ht χ (a 2) b
  have second := second_path_critical G γ (a 2,b,1) path vel smooth critical
  rw [start] at second
  have Gsmooth : ContDiffAt ℝ 2 G (0,0,0) := start ▸ smooth
  have fixed := UniformTube.coeff_two_eq_hessian G b Gsmooth
  have scale := longitudePair_coeff t ht χ (rawCore v) a 2
  change _ = (Profiles.hh t)^2/4 * (iteratedDeriv 2 f 0/(Nat.factorial 2 : ℝ)) at scale
  rw [scale,weighted,second,normal,fixed,show (Nat.factorial 2 : ℝ) = 2 by norm_num [Nat.factorial]]

/-- Coercivity in the compact transverse chart forces the differential of the
regular change of tilt coordinates to be an isomorphism. -/
theorem transverseGraph_bijective (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0<t) : Function.Bijective (fderiv ℝ (transverseGraph v t) 0) := by
  let L := fderiv ℝ (transverseGraph v t) 0
  let c := compactNormalChart t
  let F := c.curvature (paperCoefficients t ht.le 0)
  let x := rawCore v
  have hx : x∈c.core := ⟨v,rfl⟩
  obtain ⟨center,_,gap,_⟩ := compact_minimum_expansion t ht 0 (intrinsic_background_comparison t ht.le)
  have inj : Function.Injective L.toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    have same : L (center x+a)=L (center x) := by rw [L.map_add,show L a=0 from ha,add_zero]
    have eql : UniformTube.coeff F 2 x (center x+a)=UniformTube.coeff F 2 x (center x) := by
      rw [transverse_quadratic_eq_regular v reg t ht.le,transverse_quadratic_eq_regular v reg t ht.le]
      rw [show fderiv ℝ (transverseGraph v t) 0 (center x+a) = _ from same]
    have lower := gap x hx (center x+a)
    change UniformTube.coeff F 2 x (center x) + _*‖center x+a-center x‖^2 ≤ UniformTube.coeff F 2 x (center x+a) at lower
    rw [eql,add_sub_cancel_left] at lower
    by_contra ne
    have pos : 0<((2*(66+32/t^3))⁻¹/2)*‖a‖^2 := by
      apply mul_pos (by positivity) (sq_pos_of_pos (norm_pos_iff.mpr ne))
    linarith only [lower,pos]
  exact ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩

/-- Every minimizing compact-chart velocity maps to a minimizing fixed-base
graph velocity. Both minima use the full four-dimensional space of normal tilts. -/
theorem transverse_minimum_regular (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0<t) (χ : Scalar) (a : Tilts) :
    let A := paperCoefficients t ht.le χ
    let F := (compactNormalChart t).curvature A
    let G := regularFamily v reg A
    (∀ z, UniformTube.coeff F 2 (rawCore v) a ≤ UniformTube.coeff F 2 (rawCore v) z) ↔
      ∀ z, UniformTube.coeff G 2 0 (fderiv ℝ (transverseGraph v t) 0 a) ≤ UniformTube.coeff G 2 0 z := by
  intro A F G
  have pos : 0<(Profiles.hh t)^2/4 := by have := Profiles.hh_pos ht.le; positivity
  constructor
  · intro hm z
    obtain ⟨b,rfl⟩ := (transverseGraph_bijective v reg t ht).surjective z
    have bound := hm b
    rw [transverse_quadratic_eq_regular v reg t ht.le,transverse_quadratic_eq_regular v reg t ht.le] at bound
    exact (mul_le_mul_iff_right₀ pos).mp bound
  · intro hm z
    rw [transverse_quadratic_eq_regular v reg t ht.le,transverse_quadratic_eq_regular v reg t ht.le]
    exact mul_le_mul_of_nonneg_left (hm _) pos.le

/-- Order two of the intrinsic compact-disk minimum at a regular pair, evaluated
by polynomial division at the solution of the four-by-four graph normal equation. -/
theorem transverse_minimum_chartPolynomial (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0<t) (χ : Scalar) (a : Tilts) :
    let A := paperCoefficients t ht.le χ
    let F := (compactNormalChart t).curvature A
    let P := gramPolys v t ht.le
    let D := (P 0 0).det
    let Q (z : Tilts) := quotientCoeff (residual (movingChartPolynomial P z) D 2) D
    (∀ z, UniformTube.coeff F 2 (rawCore v) a ≤ UniformTube.coeff F 2 (rawCore v) z) →
      fderiv ℝ (transverseGraph v t) 0 a = stationaryTilt Q ∧
      UniformTube.coeff F 2 (rawCore v) a = (Profiles.hh t)^2/4*Q (stationaryTilt Q) := by
  intro A F P D Q hm
  let G := regularFamily v reg A
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (chart r s).symm 0
  let e (i : Fin 4) := field r s (parameterBasis i) p
  let C (φ : Scalar) := graphCoefficient (paperCoefficients t ht.le φ) (e 0) (e 1) (e 2) (e 3) 2
  have base := regularBase_zero v reg
  have eq : UniformTube.coeff G 2 0 = C χ := by
    funext z
    have h := regularFamily_coeff v reg t ht.le χ 0 z 2
    dsimp only at h
    rw [base] at h
    exact h
  have raw : C 0=Q := funext fun z => graphCoefficient_eq_chartPolynomial v t ht.le z 2
  have table : UniformTube.coeff G 2 0 = Q := eq.trans ((graph_cubic_correction t ht.le 0 χ (e 0) (e 1) (e 2) (e 3)).1.trans raw)
  have inv := (regular_graph_minimum v reg t ht χ (δ := 1) (by norm_num)).1
  have det : IsUnit (tiltHessian (UniformTube.coeff G 2 0)).det := by rw [eq]; exact inv
  let b := fderiv ℝ (transverseGraph v t) 0 a
  have smooth : ContDiffAt ℝ 2 G (0,0,0) := (regularFamily_smooth v reg t ht.le χ (h := 0) (by norm_num) 0).of_le (by simp)
  have min := (transverse_minimum_regular v reg t ht χ a).mp hm
  have st := stationaryTilt_of_minimum G smooth b min det
  rw [table] at st
  refine ⟨st.symm,?_⟩
  rw [transverse_quadratic_eq_regular v reg t ht.le]
  change _ * UniformTube.coeff G 2 0 b=_
  rw [table,st]

/-- Along the compact-chart ray, the squared-area factor converts the regular-base numerator back to the original frame. -/
private theorem compact_regular_value (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) (a : Tilts) :
    let A := paperCoefficients t ht χ
    let F := (compactNormalChart t).curvature A
    let G := regularFamily v reg A
    ∀ᶠ s : ℝ in 𝓝 0, F (rawCore v,s • a,s) =
      ((Profiles.hh t)^2/4 * (transverseDet v t (s • a))^2) * G (s*a 2,transverseGraph v t (s • a),s) := by
  intro A F G
  let z (s : ℝ) := s • a
  have dz : HasDerivAt z a 0 := by simpa [z] using (hasDerivAt_id' (0:ℝ)).smul_const a
  have z0 : z 0=0 := zero_smul ..
  filter_upwards [dz.continuousAt.tendsto.eventually (z0 ▸ regular_transition v t ht reg),paper_metrics_realize t ht χ] with h step ⟨g,hg⟩
  obtain ⟨hz,_,_,K⟩ := step
  let w := (compactNormalChart t).frame (rawCore v,z h)
  let H := Profiles.hh t
  let det := transverseDet v t (z h)
  let right := (scriptPair (regularBase v reg (z h 2)) (transverseGraph v t (z h))).numerator A h
  have e : (longitudePair t w).numerator A h = det^2*right := by
    dsimp only [right]
    rw [TangentPair.numerator_eq _ hg,TangentPair.numerator_eq _ hg,K g,regularBase,dite_eq_left hz]
    rfl
  have l : (longitudePair t w).numerator A h = (2/H)^2*w.numerator A h := by
    rw [TangentPair.numerator_eq _ hg,TangentPair.numerator_eq _ hg]
    have cur := curvatureNumerator_basis_change g w.point w.first w.second H⁻¹ H⁻¹ (-1) 1
    simpa only [H,longitudePair,one_smul,mul_one,mul_neg_one,sub_neg_eq_add,div_eq_mul_inv,two_mul] using cur
  change w.numerator A h = (H^2/4*det^2)*right
  rw [l] at e
  field_simp [show H≠0 from (Profiles.hh_pos ht).ne'] at e
  linarith only [e]

private theorem signed_quotient_limit {f : ℝ → ℝ} {c : ℝ} (lim : Tendsto f (𝓝[≠] 0) (𝓝 c))
    (sgn : ∀ᶠ s in 𝓝[≠] (0:ℝ), 0≤s*f s) : c=0 := by
  have right : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun _ h => ne_of_gt h)
  have left : 𝓝[<] (0:ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun _ h => ne_of_lt h)
  have hr : 0≤c := ge_of_tendsto (lim.mono_left right) (by
    filter_upwards [right sgn,self_mem_nhdsWithin] with s pos hs
    exact nonneg_of_mul_nonneg_right pos (show 0<s from hs))
  have hl : c≤0 := le_of_tendsto (lim.mono_left left) (by
    filter_upwards [left sgn,self_mem_nhdsWithin] with s pos hs
    exact nonpos_of_mul_nonneg_right pos (show s<0 from hs))
  exact le_antisymm hl hr

/-- On the zero set of a nonnegative regular-fiber quadratic, the moving base
and the changing area factor preserve the cubic coefficient, up to the core area.
Both signs of the metric parameter are used in the proof. -/
theorem transverse_cubic_eq_regular (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0<t) (χ : Scalar) (a : Tilts) :
    let A := paperCoefficients t ht.le χ
    let F := (compactNormalChart t).curvature A
    let G := regularFamily v reg A
    UniformTube.coeff F 2 (rawCore v) a=0 →
    (∀ᶠ h : ℝ in 𝓝 0, ∀ z, 0≤UniformTube.coeff G 2 h z) →
    UniformTube.coeff F 3 (rawCore v) a = (Profiles.hh t)^2/4 *
      UniformTube.coeff G 3 0 (fderiv ℝ (transverseGraph v t) 0 a) := by
  intro A F G F2 positive
  let x := rawCore v
  let c := compactNormalChart t
  let L := 𝓝[≠] (0:ℝ)
  let b := fderiv ℝ (transverseGraph v t) 0 a
  let Z (s : ℝ) := transverseGraph v t (s • a)
  let w (s : ℝ) := (s*a 2,s⁻¹ • Z s)
  let area := (Profiles.hh t)^2/4
  let k (s : ℝ) := area*(transverseDet v t (s • a))^2
  have sid : Tendsto id L (𝓝 0) := nhdsWithin_le_nhds
  have dz : HasDerivAt (fun s : ℝ => s • a) a 0 := by simpa using (hasDerivAt_id' (0:ℝ)).smul_const a
  have base := transverseGraph_at_core v t ht.le
  have sm := transverseGraph_smooth v t ht.le
  have vel : HasDerivAt Z b 0 := by
    have dG : HasFDerivAt (transverseGraph v t) (fderiv ℝ (transverseGraph v t) 0) ((0:ℝ) • a) := by
      simpa only [zero_smul] using (sm.2.differentiableAt (by simp)).hasFDerivAt
    exact dG.comp_hasDerivAt 0 dz
  have Z0 : Z 0 = 0 := by simp only [Z,zero_smul,base.2]
  have ws : Tendsto (fun s : ℝ => s⁻¹ • Z s) L (𝓝 b) := by
    have eq : slope Z 0 = fun s => s⁻¹ • Z s := by funext s; simp [slope_def_module,Z0]
    rw [←eq]
    exact vel.tendsto_slope
  have height : Tendsto (fun s : ℝ => s*a 2) L (𝓝 0) := by simpa using sid.mul_const (a 2)
  have hw : Tendsto w L (𝓝 (0,b)) := height.prodMk_nhds ws
  have hk : Tendsto k L (𝓝 area) := by
    have dt : Tendsto (fun s : ℝ => transverseDet v t (s • a)) L (𝓝 1) := by
      have ds := sm.1.continuousAt.tendsto
      rw [base.1] at ds
      exact ds.comp ((show Tendsto (fun s : ℝ => s • a) (𝓝 0) (𝓝 0) by simpa using dz.continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
    simpa [k] using (dt.pow 2).const_mul area
  have hx : x ∈ c.core := ⟨v,rfl⟩
  obtain ⟨η,hη,regular⟩ := compact_curvature_regular t ht.le χ
  have hf : ContDiffAt ℝ 4 F (x,0,0) := (regular _ ⟨hx,by simpa using c.radius_pos.le,le_rfl,hη.le⟩).of_le (by simp)
  have ft := compact_chart_core_jet t ht.le χ hx
  have f0 : UniformTube.coeff F 0 x a=0 := (UniformTube.coeff_zero F x a).trans ft.1
  have f1 := UniformTube.first_coeff_zero F c.radius_pos (show 0≤(2*(66+32/t^3))⁻¹ by positivity) hf ft.1
    ((comparison_bounds t ht χ (intrinsic_background_comparison t ht.le)).1 x hx) ft.2.deriv a
  let u (s : ℝ) := F (x,s • a,s)/s^3
  have left : Tendsto u L (𝓝 (UniformTube.coeff F 3 x a)) := by
    have h := UniformTube.moving_cubic_remainder F hf (fun _ => (x,a)) tendsto_const_nhds
    have F2x : UniformTube.coeff F 2 x a=0 := F2
    simpa only [f0,f1,F2x,mul_zero,add_zero,zero_add,sub_zero] using h
  have hG : ContDiffAt ℝ 4 G (0,0,0) := (regularFamily_smooth v reg t ht.le χ (h := 0) (by norm_num) 0).of_le (by simp)
  let y (s : ℝ) := (G ((w s).1,s • (w s).2,s)-s^2*UniformTube.coeff G 2 (w s).1 (w s).2)/s^3
  have right : Tendsto y L (𝓝 (UniformTube.coeff G 3 0 b)) := by
    apply (UniformTube.moving_cubic_remainder G hG w hw).congr'
    have close : ∀ᶠ s : ℝ in L, |(w s).1|<1 := height.abs.eventually_lt_const (by simp)
    filter_upwards [close] with s hs
    have zero := regularFamily_flat v reg t ht.le χ (w s).1
    have cap : ContDiffAt ℝ 4 G ((w s).1,0,0) := (regularFamily_smooth v reg t ht.le χ hs 0).of_le (by simp)
    have flat : G ((w s).1,0,0)=0 := zero
    have time : deriv (fun r => G ((w s).1,0,r)) 0=0 :=
      (flat_torus_first (regularBase v reg (w s).1) (JetChart.center _).1 rfl t ht.le χ (1,0) (0,1)).deriv
    have low (z : Tilts) (_ : ‖z‖≤ 1) : (0:ℝ)*‖z‖^2 ≤ G ((w s).1,z,0) := by
      rw [zero_mul]
      change 0≤(scriptPair _ _).numerator _ 0
      rw [TangentPair.numerator_eq _ (background_zero t ht.le χ)]
      exact background_nonneg ..
    have one := UniformTube.first_coeff_zero G (by norm_num : 0<(1:ℝ)) le_rfl cap flat low time (w s).2
    simp only [UniformTube.coeff_zero,flat,one,mul_zero,add_zero,zero_add,y]
  have lim := left.sub (hk.mul right)
  apply sub_eq_zero.mp
  apply signed_quotient_limit lim
  filter_upwards [nhdsWithin_le_nhds (compact_regular_value v reg t ht.le χ a),height.eventually positive,self_mem_nhdsWithin] with s he hp hn
  have nz : s≠0 := hn
  have back : s • (w s).2=Z s := by simp [w,smul_smul,nz]
  change F (x,s • a,s) = k s*G ((w s).1,Z s,s) at he
  change 0≤s*(F (x,s • a,s)/s^3 - k s*((G ((w s).1,s • (w s).2,s)-s^2*UniformTube.coeff G 2 (w s).1 (w s).2)/s^3))
  rw [back,he,show s*(k s*G ((w s).1,Z s,s)/s^3-k s*((G ((w s).1,Z s,s)-s^2*UniformTube.coeff G 2 (w s).1 (w s).2)/s^3)) =
    k s*UniformTube.coeff G 2 (w s).1 (w s).2 by field_simp; ring]
  exact mul_nonneg (by dsimp [k,area]; positivity) (hp _)

/-- The intrinsic graph Taylor coefficient in the adapted frame at a representative. -/
def fiberCoefficient (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (χ : Scalar) (n : ℕ) (z : Tilts) :=
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (chart r s).symm 0
  let e (i : Fin 4) := field r s (parameterBasis i) p
  graphCoefficient (paperCoefficients t ht χ) (e 0) (e 1) (e 2) (e 3) n z

private theorem fiberCoefficient_ray (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) (n : ℕ) (z : Tilts) :
    fiberCoefficient v t ht χ n z =
      iteratedDeriv n (fun s : ℝ => (scriptPair v (s • z)).numerator (paperCoefficients t ht χ) s) 0 / n.factorial := by
  have eq := regularFamily_coeff v reg t ht χ 0 z n
  change iteratedDeriv n (fun s : ℝ => (scriptPair (regularBase v reg 0) (s • z)).numerator _ s) 0 / _ =
    fiberCoefficient (regularBase v reg 0) t ht χ n z at eq
  rw [regularBase_zero] at eq
  exact eq.symm

/-- Reversing the common normal reverses both spanning vectors and leaves every
graph coefficient invariant, including at nonzero graph tilt. -/
theorem fiberCoefficient_orientation (v u : FlatLocus.Representative)
    (rv : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (ru : rangeFactorization FlatLocus.forgetOrientation u ∈ FlatLocus.regular)
    (base : v.val.2=u.val.2) (normal : v.val.1.val = u.val.1.val ∨ v.val.1.val = -u.val.1.val)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) (n : ℕ) (z : Tilts) :
    fiberCoefficient v t ht χ n z=fiberCoefficient u t ht χ n z := by
  rcases normal with same | opp
  · have eq : v=u := Subtype.ext (Prod.ext (Subtype.ext same) base)
    rw [eq]
  let A := paperCoefficients t ht χ
  let flip (p : TangentPair) : TangentPair := ⟨p.point,-p.first,-p.second⟩
  have fd (p : TangentPair) : frameData (flip p) = ((frameData p).1,-(frameData p).2.1,-(frameData p).2.2) := by
    simp only [flip,frameData,map_neg]
  have repl (a : Tilts) : scriptPair v a = flip (scriptPair u a) := by
    apply frameData_injective
    rw [fd,script_data,script_data,base,opp]
    simp [add_comm]
  have eq : (fun s : ℝ => (scriptPair v (s • z)).numerator A s) =ᶠ[𝓝 0]
      (fun s : ℝ => (scriptPair u (s • z)).numerator A s) := by
    filter_upwards [paper_metrics_realize t ht χ] with s ⟨g,hg⟩
    rw [repl,TangentPair.numerator_eq _ hg,TangentPair.numerator_eq _ hg]
    let w := scriptPair u (s • z)
    have cur := curvatureNumerator_basis_change g w.point w.first w.second (-1) 0 0 (-1)
    simpa only [flip,neg_one_smul,zero_smul,add_zero,zero_add,neg_mul_neg,one_mul,mul_one,zero_mul,sub_zero,one_pow] using cur
  rw [fiberCoefficient_ray v rv,fiberCoefficient_ray u ru,eq.iteratedDeriv_eq]

private theorem unit_circle_angle (x y : ℝ) (eq : x^2+y^2=1) : ∃ θ : ℝ, cos θ=x ∧ sin θ=y := by
  have bound : |x|≤1 := (sq_le_one_iff_abs_le_one x).mp (by nlinarith only [eq,sq_nonneg y])
  have cosx := cos_arccos (abs_le.mp bound).1 (abs_le.mp bound).2
  have sinx := sin_arccos x
  rw [show 1-x^2=y^2 by linarith only [eq],sqrt_sq_eq_abs] at sinx
  by_cases hy : 0≤y
  · exact ⟨arccos x,cosx,sinx.trans (abs_of_nonneg hy)⟩
  · exact ⟨-arccos x,by rwa [cos_neg],by rw [sin_neg,sinx,abs_of_neg (lt_of_not_ge hy),neg_neg]⟩

/-- Every equatorial incidence representative has a longitude pair, with either choice of common normal. -/
theorem equatorial_representative (v : FlatLocus.Representative) (zero : v.val.1.val 0^2+v.val.1.val 1^2=0) :
    ∃ m d : ℝ, v.val.2=(equatorCore m d).val.2 ∧
      (v.val.1.val=(equatorCore m d).val.1.val ∨ v.val.1.val= -(equatorCore m d).val.1.val) := by
  let n := v.val.1.val
  have h0 : n 0=0 := by change v.val.1.val 0=0; nlinarith only [zero,sq_nonneg (v.val.1.val 1)]
  have h1 : n 1=0 := by change v.val.1.val 1=0; nlinarith only [zero,sq_nonneg (v.val.1.val 0)]
  have un : n ⬝ᵥ n=1 := v.val.1.property
  simp only [dotProduct,Fin.sum_univ_three,h0,h1,zero_mul,zero_add] at un
  have pm : n 2 = 1 ∨ n 2 = -1 := by
    have split : (n 2-1)*(n 2+1)=0 := by linarith only [un]
    rcases mul_eq_zero.mp split with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have get (p : FlatLocus.UnitVector) (perp : n ⬝ᵥ p.val=0) : ∃ θ : ℝ, p.val= ![cos θ,sin θ,0] := by
    simp only [dotProduct,Fin.sum_univ_three,h0,h1,zero_mul,zero_add] at perp
    have pz := (mul_eq_zero.mp perp).resolve_left (by rcases pm with hp | hp <;> rw [hp] <;> norm_num)
    have unit := p.property
    change p.val ⬝ᵥ p.val=1 at unit
    simp only [dotProduct,Fin.sum_univ_three,pz,mul_zero,add_zero] at unit
    obtain ⟨θ,hco,hsi⟩ := unit_circle_angle (p.val 0) (p.val 1) (by nlinarith only [unit])
    refine ⟨θ,?_⟩
    ext i; fin_cases i
    · exact hco.symm
    · exact hsi.symm
    · exact pz
  obtain ⟨α,hα⟩ := get _ v.property.1
  obtain ⟨β,hβ⟩ := get _ v.property.2
  let m := (α+β)/2
  let d := (α-β)/2
  refine ⟨m,d,Prod.ext (Subtype.ext ?_) (Subtype.ext ?_),?_⟩
  · change v.val.2.1.val= ![cos (m+d),sin (m+d),0]
    rwa [show m+d=α by dsimp [m,d]; ring]
  · change v.val.2.2.val= ![cos (m-d),sin (m-d),0]
    rwa [show m-d=β by dsimp [m,d]; ring]
  · change n=Pi.single 2 (1:ℝ) ∨ n= -(Pi.single 2 (1:ℝ))
    rcases pm with hp | hp
    · left; ext i; fin_cases i <;> simp [h0,h1,hp]
    · right; ext i; fin_cases i <;> simp [h0,h1,hp]

end
end LocalHopf.BackgroundGrowth.Transverse
