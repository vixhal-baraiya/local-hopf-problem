import LocalHopf.RegularFamily
import LocalHopf.GeometricReduction

/-! The two explicit coefficient identities from the verifier which suffice for
the concrete theorem. Both sides of the identities are fixed by the paper data. -/
namespace LocalHopf.BackgroundGrowth.Transverse
open Set Filter Real Matrix Metric SphereProduct JetChart UniformTube Profiles
open scoped Topology ContDiff
noncomputable section

/-- A Taylor coefficient from finite division of the intrinsic chart polynomials. -/
def chartEntry (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (n : ℕ) (z : Tilts) :=
  let P := gramPolys v t ht
  let D := (P 0 0).det
  quotientCoeff (residual (movingChartPolynomial P z) D n) D

/-- Evaluate the chart coefficient at the solution of the quadratic normal equation. -/
def minimumEntry (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (n : ℕ) :=
  chartEntry v t ht n (stationaryTilt (chartEntry v t ht 2))

private theorem fiber_zero (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (n : ℕ) :
    fiberCoefficient v t ht 0 n = chartEntry v t ht n :=
  funext fun z => graphCoefficient_eq_chartPolynomial v t ht z n

private theorem fiber_two (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (χ : Scalar) :
    fiberCoefficient v t ht χ 2 = chartEntry v t ht 2 := by
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (chart r s).symm 0
  let e (i : Fin 4) := field r s (parameterBasis i) p
  exact (graph_cubic_correction t ht 0 χ (e 0) (e 1) (e 2) (e 3)).1.trans (fiber_zero v t ht 2)

private theorem family_core (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) (n : ℕ) :
    coeff (regularFamily v reg (paperCoefficients t ht χ)) n 0 = fiberCoefficient v t ht χ n := by
  funext z
  have eq := regularFamily_coeff v reg t ht χ 0 z n
  change _ = fiberCoefficient (regularBase v reg 0) t ht χ n z at eq
  rwa [regularBase_zero] at eq

private theorem chart_minimizes (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0<t) (z : Tilts) : minimumEntry v t ht.le 2 ≤ chartEntry v t ht.le 2 z := by
  let c := compactNormalChart t
  let F := c.curvature (paperCoefficients t ht.le 0)
  let x := rawCore v
  have hx : x∈c.core := ⟨v,rfl⟩
  obtain ⟨center,_,gap,_⟩ := intrinsic_minimum_expansion t ht 0
  have min (b : Tilts) : coeff F 2 x (center x) ≤ coeff F 2 x b :=
    (le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))).trans (gap x hx b)
  obtain ⟨st,_⟩ := transverse_minimum_chartPolynomial v reg t ht 0 (center x) min
  have b := (transverse_minimum_regular v reg t ht 0 (center x)).mp min z
  rw [family_core,fiber_zero,st] at b
  exact b

theorem regularFamily_normal_second (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (χ : Scalar) (z : Tilts) :
    let G := regularFamily v reg (paperCoefficients t ht χ)
    iteratedDeriv 2 (fun h : ℝ => G (0,h • z,0)) 0 = normalSecond t (v.val.2.1.val ⬝ᵥ v.val.2.2.val) z := by
  intro G
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (chart r s).symm 0
  let a (h : ℝ) : Params := ((1,0),(h • z) 0,(h • z) 1)
  let b (h : ℝ) : Params := ((0,1),(h • z) 2,(h • z) 3)
  have eq : (fun h : ℝ => G (0,h • z,0)) = fun h => curvatureNumerator (backgroundMetric t ht) p
      (field r s (a h) p) (field r s (b h) p) := by
    funext h
    dsimp only [G,regularFamily]
    rw [regularBase_zero,TangentPair.numerator_eq _ (background_zero t ht χ)]
    rfl
  rw [eq]
  exact graph_background_derivative v t ht z

/-- The intrinsic quadratic in the four tilt variables has the explicit
rational Hessian at every regular pair. -/
theorem chartEntry_hessian (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) (t : ℝ) (ht : 0≤t) :
    tiltHessian (chartEntry v t ht 2) = normalMatrix t (v.val.2.1.val ⬝ᵥ v.val.2.2.val) := by
  let c := v.val.2.1.val ⬝ᵥ v.val.2.2.val
  let M := normalMatrix t c
  have hc : c^2≤1 := by have circ := separation_circle v; dsimp only at circ; dsimp [c]; nlinarith only [circ,sq_nonneg ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val)]
  let G := regularFamily v reg (paperCoefficients t ht 0)
  have eq : coeff G 2 0=chartEntry v t ht 2 := (family_core v reg t ht 0 2).trans (fiber_zero v t ht 2)
  have sm : ContDiffAt ℝ 2 G (0,0,0) := (regularFamily_smooth v reg t ht 0 (h := 0) (by norm_num) 0).of_le (by simp)
  ext i j
  rw [←eq,tiltHessian_background G sm i j]
  dsimp only
  have ray (z : Tilts) : iteratedDeriv 2 (fun s : ℝ => G (0,s • z,0)) 0 = z ⬝ᵥ M *ᵥ z :=
    (regularFamily_normal_second v reg t ht 0 z).trans (normalSecond_matrix t c ht hc z)
  rw [ray,ray,ray,Matrix.mulVec_add,add_dotProduct,dotProduct_add,dotProduct_add]
  simp only [single_dotProduct,one_mul,Matrix.mulVec_single_one,Matrix.col_apply]
  have sym : M j i=M i j := (normalMatrix_symmetric t c).apply i j
  linarith only [sym]

theorem chartEntry_hessian_det (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) (t : ℝ) (ht : 0≤t) :
    let c := v.val.2.1.val ⬝ᵥ v.val.2.2.val
    (tiltHessian (chartEntry v t ht 2)).det = 4*t^6*(1-c^2)*(4*(1+t)^2-(t*c)^2)/((hh t)^4*(Profiles.D t c)^5) := by
  intro c
  rw [chartEntry_hessian v reg t ht]
  apply normalMatrix_det _ _ ht
  have circ := separation_circle v
  dsimp only at circ
  nlinarith only [circ,sq_nonneg ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val)]


/-- The constant tilt term used in the Schur complement, with the explicit inverse
background Gram matrix and no differentiated inverse. -/
theorem chartEntry_fixed_second (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let a : Params := ((1,0),0)
    let b : Params := ((0,1),0)
    let c := v.val.2.1.val ⬝ᵥ v.val.2.2.val
    let I : Matrix (Fin 4) (Fin 4) ℝ := !![1+2*t,0,0,0;0,1,0,0;0,0,2*(1+t),2*t*c;0,0,2*t*c,2*(1+t)]
    let J (u w : Params) (i : Fin 4) := symbol (tensor r s (firstOrderTensor t ht)) u w (parameterBasis i) 0
    chartEntry v t ht 2 0 = second (tensor r s (secondOrderTensor t ht)) a b 0 +
      J a b ⬝ᵥ I *ᵥ J a b - J a a ⬝ᵥ I *ᵥ J b b := by
  intro r s a b c I J
  let A := paperCoefficients t ht 0
  let G : Matrix (Fin 4) (Fin 4) ℝ := fun i j => tensor r s (A 0) (parameterBasis i) (parameterBasis j) 0
  have inv : G⁻¹=I := inverse_at_center v t ht
  have unit : IsUnit G.det := by
    by_contra hn
    have h := congrFun (congrFun (inv.symm.trans (nonsing_inv_apply_not_isUnit G hn)) 1) 1
    norm_num [I] at h
  have h0 : (0:Params) ∈ (coreChart v).target := (center v).1
  have gamma (d : Params) : symbol (tensor r s (A 0)) a a d 0=0 ∧ symbol (tensor r s (A 0)) a b d 0=0 ∧
      symbol (tensor r s (A 0)) b b d 0=0 := ⟨core_gamma v h0 rfl t ht (1,0) (1,0) d,
        core_gamma v h0 rfl t ht (1,0) (0,1) d,core_gamma v h0 rfl t ht (0,1) (0,1) d⟩
  have calc₂ := tensorNumerator_second r s A parameterBasis 0 a b unit.ne_zero gamma
  change iteratedDeriv 2 _ 0/2=second (tensor r s (secondOrderTensor t ht)) a b 0+
    J a b ⬝ᵥ G⁻¹ *ᵥ J a b-J a a ⬝ᵥ G⁻¹ *ᵥ J b b at calc₂
  rw [inv] at calc₂
  rw [←calc₂]
  let f (z : ℝ) := uncorrectedNumerator v t ht z a b
  have eq : f =ᶠ[𝓝 0] tensorNumerator r s A parameterBasis 0 a b := by
    filter_upwards [paper_metrics_realize t ht (0:Scalar)] with z ⟨g,hg⟩
    exact (curvature_eq_uncorrectedNumerator v t ht hg a b).symm.trans
      (tensorNumerator_realizes r s hg h0 parameterBasis a b)
  rw [←eq.iteratedDeriv_eq]
  have e := (graphCoefficient_eq_chartPolynomial v t ht 0 2).symm.trans (graphCoefficient_eq_uncorrected v t ht 0 2)
  have hz : (0 : ℝ × ℝ) = (0,0) := rfl
  simpa [chartEntry,f,a,b,hz,Nat.factorial] using e

/-- The verifier's gradient and inverse-Hessian formula computes the same
quadratic minimum as the intrinsic graph. -/
theorem minimumEntry_schur (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0<t) :
    let Q := chartEntry v t ht.le 2
    let g := fixedGradient (linearGramPolys v t ht.le)
    minimumEntry v t ht.le 2 = Q 0 - (g ⬝ᵥ ((normalMatrix t (v.val.2.1.val ⬝ᵥ v.val.2.2.val))⁻¹ *ᵥ g))/2 := by
  intro Q g
  let G := regularFamily v reg (paperCoefficients t ht.le 0)
  let a := stationaryTilt Q
  have eq : coeff G 2 0=Q := (family_core v reg t ht.le 0 2).trans (fiber_zero v t ht.le 2)
  have min (z : Tilts) : coeff G 2 0 a ≤ coeff G 2 0 z := by rw [eq]; exact chart_minimizes v reg t ht z
  have sm : ContDiffAt ℝ 2 G (0,0,0) := (regularFamily_smooth v reg t ht.le 0 (h := 0) (by norm_num) 0).of_le (by simp)
  have val := quadratic_minimum_schur G sm a min
  rw [eq] at val
  have gradient : g = tiltGradient Q 0 := (fixedGradient_linear v t ht.le).symm.trans
    (funext fun i => (moving_gradient_entry (gramPolys v t ht.le) i).symm)
  change Q a=Q 0+(tiltGradient Q 0 ⬝ᵥ a)/2 at val
  change Q a= _
  rw [val,gradient,←chartEntry_hessian v reg t ht.le]
  simp [a,stationaryTilt,Q,sub_eq_add_neg,Matrix.mulVec_neg,dotProduct_neg,neg_div]


private theorem entry_low (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (z : Tilts) : chartEntry v t ht 0 z=0 ∧ chartEntry v t ht 1 z=0 := by
  let F := regularFamily v reg (paperCoefficients t ht 0)
  have e (n : ℕ) : coeff F n 0 z=chartEntry v t ht n z :=
    congrFun ((family_core v reg t ht 0 n).trans (fiber_zero v t ht n)) z
  rw [←e 0,←e 1,coeff_zero]
  refine ⟨regularFamily_flat v reg t ht 0 0,?_⟩
  let γ (s : ℝ) : ℝ × Tilts × ℝ := (0,s • z,s)
  have vel : HasDerivAt γ (0,z,1) 0 := by
    simpa [γ] using (hasDerivAt_const (0:ℝ) (0:ℝ)).prodMk (((hasDerivAt_id' (0:ℝ)).smul_const z).prodMk (hasDerivAt_id' (0:ℝ)))
  have smooth : ContDiffAt ℝ ∞ F (γ 0) := by simpa [γ,F] using regularFamily_smooth v reg t ht (0:Scalar) (h := 0) (by norm_num) 0
  have crit : fderiv ℝ F (γ 0)=0 := by simpa [γ,F] using regularFamily_critical v reg t ht (0:Scalar) (h := 0) (by norm_num)
  have der := ((smooth.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 vel).deriv
  rw [crit,zero_apply] at der
  change iteratedDeriv 1 (F ∘ γ) 0 / (1:ℕ).factorial=0
  simp [iteratedDeriv_one,der]

/-- Both moving coefficients in terms of ordinary numerator coefficients and the
two scalar block solves. The cubic uses the first-order change of the volume determinant. -/
theorem minimumEntry_coefficients (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) (t : ℝ) (ht : 0<t) :
    let u := v.val.2.1.val ⬝ᵥ v.val.2.2.val
    let T := gramPolys v t ht.le
    let g := fixedGradient (linearGramPolys v t ht.le)
    let z := normalSolve t u (-g)
    let N := movingChartPolynomial T z
    let D := (T 0 0).det
    let scale := 4*hh t*Profiles.D t u
    N.coeff 0=0 ∧ N.coeff 1=0 ∧ minimumEntry v t ht.le 2 = scale * N.coeff 2 ∧
      minimumEntry v t ht.le 3 = scale * (N.coeff 3 - (scale*N.coeff 2)*D.coeff 1) := by
  intro u T g z N D scale
  have grad : tiltGradient (chartEntry v t ht.le 2) 0 = g :=
    (funext (moving_gradient_entry T)).trans (fixedGradient_linear v t ht.le)
  have tilt : stationaryTilt (chartEntry v t ht.le 2)=z := by
    rw [stationaryTilt,chartEntry_hessian v reg t ht.le,grad]
    exact (normalSolve_eq t u ht (sep_regular v reg) (-g)).symm
  have nd : D.coeff 0 = 1/scale := gramPolys_det_zero v t ht.le
  have hu := (sep_regular v reg).le
  have hd := Profiles.D_pos ht.le ((sq_le_one_iff_abs_le_one u).mpr hu)
  have hh₀ := hh_pos ht.le
  have scale_pos : 0<scale := by dsimp [scale]; positivity
  have d0 : D.coeff 0≠0 := nd.trans_ne (one_div_ne_zero scale_pos.ne')
  have lo := entry_low v reg t ht.le z
  change quotientCoeff N D=0 ∧ quotientCoeff (residual N D 1) D=0 at lo
  have r1 : residual N D 1=N.divX := by simp [SphereProduct.residual,quotientNext,lo.1]
  have r2 : residual N D 2=N.divX.divX := by
    change (residual N D 1-Polynomial.C (quotientCoeff (residual N D 1) D)*D).divX=_
    rw [lo.2,Polynomial.C_0,zero_mul,sub_zero,r1]
  have n0 : N.coeff 0=0 := (div_eq_zero_iff.mp lo.1).resolve_right d0
  have n1 := lo.2
  rw [r1,quotientCoeff,Polynomial.coeff_divX] at n1
  refine ⟨n0,(div_eq_zero_iff.mp n1).resolve_right d0,?_,?_⟩
  · rw [minimumEntry,tilt]
    change quotientCoeff (residual N D 2) D=_
    rw [r2,quotientCoeff,Polynomial.coeff_divX,Polynomial.coeff_divX,nd]
    simp only [div_div_eq_mul_div,div_one]
    ring
  · rw [minimumEntry,tilt]
    change quotientCoeff (quotientNext (residual N D 2) D) D=_
    rw [r2]
    simp only [quotientNext,quotientCoeff,Polynomial.coeff_divX,Polynomial.coeff_sub,Polynomial.coeff_C_mul,nd,div_div_eq_mul_div,div_one]
    ring


/-- The uncorrected equatorial cubic, after its quadratic vanishes, agrees with
the exported forcing exactly when the cleared third numerator coefficient agrees
with the integer table in half-angle coordinates. This also covers rotations by pi. -/
theorem equator_cubic_iff_numerator (t m d : ℝ) (ht : 0<t)
    (reg : rangeFactorization FlatLocus.forgetOrientation (equatorCore m d) ∈ FlatLocus.regular)
    (h₂ : minimumEntry (equatorCore m d) t ht.le 2=0) :
    let v := equatorCore m d
    let α := m+d
    let β := m-d
    let u := v.val.2.1.val ⬝ᵥ v.val.2.2.val
    let z := normalSolve t u (-fixedGradient (linearGramPolys v t ht.le))
    let N := movingChartPolynomial (gramPolys v t ht.le) z
    let r := tan ((β-α)/2)
    let a : ℝ × ℝ := if cos (-α/2)=0 then (0,1) else (1,tan (-α/2))
    minimumEntry v t ht.le 3=EquatorJet.forcing t (α,β) ↔
      4*hh t*Profiles.D t u*N.coeff 3=EquatorJet.rationalForcing t r a.1 a.2 := by
  intro v α β u z N r a
  have hu : |u|<1 := sep_regular v reg
  have dot : u=cos (β-α) := by
    change (![cos α,sin α,0] : R3) ⬝ᵥ ![cos β,sin β,0]=cos (β-α)
    simp [dotProduct,Fin.sum_univ_three,cos_sub]; ring
  have hd : cos ((β-α)/2)≠0 := by
    intro hn
    have dd := cos_two_mul ((β-α)/2)
    rw [show 2*((β-α)/2)=β-α by ring,hn] at dd
    rw [dot,dd] at hu
    norm_num at hu
  have f : EquatorJet.forcing t (α,β)=EquatorJet.rationalForcing t r a.1 a.2 := by
    by_cases h : cos (-α/2)=0
    · simpa [a,h,r] using EquatorJet.forcing_at_rotation_pole t α β hd h
    · simpa [a,h,r] using EquatorJet.forcing_rational t α β hd h
  have raw := minimumEntry_coefficients v reg t ht
  rcases raw with ⟨_,_,q,c⟩
  change minimumEntry v t ht.le 2=4*hh t*Profiles.D t u*N.coeff 2 at q
  change minimumEntry v t ht.le 3=4*hh t*Profiles.D t u*(N.coeff 3-(4*hh t*Profiles.D t u*N.coeff 2)*_) at c
  rw [←q,h₂,zero_mul,sub_zero] at c
  rw [f,c]

/-- The two arithmetic checks on the uncorrected family. The equatorial table
is required only with north-pointing normal and regular sphere pair. -/
def chartTablesMatch (t : ℝ) (ht : 0≤t) : Prop :=
  (∀ x : FlatLocus.Plane, x ∈ FlatLocus.regular →
    minimumEntry (FlatLocus.oriented x) t ht 2=exportedQuadratic t (FlatLocus.oriented x)) ∧
  (∀ m d : ℝ, rangeFactorization FlatLocus.forgetOrientation (equatorCore m d) ∈ FlatLocus.regular →
    minimumEntry (equatorCore m d) t ht 3=EquatorJet.forcing t (m+d,m-d))

/-- Subtracting the two proven profile responses leaves exactly the rational
calculation of Proposition 5.1 on each positively oriented regular frame. -/
theorem quadratic_table_iff_rational (x : FlatLocus.Plane) (reg : x ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0<t) :
    let v := FlatLocus.oriented x
    let f := FlatLocus.data
    let u := f.sep x
    let a : Params := ((1,0),0)
    let b : Params := ((0,1),0)
    let I : Matrix (Fin 4) (Fin 4) ℝ := !![1+2*t,0,0,0;0,1,0,0;0,0,2*(1+t),2*t*u;0,0,2*t*u,2*(1+t)]
    let J := firstSymbol v t ht.le
    let q := rationalTensorSecond v t ht.le
    let g := fixedGradient (linearGramPolys v t ht.le)
    minimumEntry v t ht.le 2 = exportedQuadratic t v ↔
      (q (a+b) 1 0-q a 1 0-q b 1 0-q a 1 1-q b 0 0) +
        J 0 1 ⬝ᵥ I *ᵥ J 0 1 - J 0 0 ⬝ᵥ I *ᵥ J 1 1 - (g ⬝ᵥ normalSolve t u g)/2 =
      V2form lamC lamD (Certificate.baseY.value t (-u)) (Certificate.baseY.value t u)
        (f.nx x) (f.ny x) (f.nz x) (Certificate.vectorA t u) (Certificate.vectorB t u)
        (f.xp x) (f.zp x) (Certificate.matrix₁ t u) (Certificate.matrix₂ t u) := by
  intro v f u a b I J q g
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let Γ (l k : Params) (i : Fin 4) := symbol (tensor r s (firstOrderTensor t ht.le)) l k (parameterBasis i) 0
  have ea : parameterBasis 0=a := by ext <;> simp [a,parameterBasis_apply]
  have eb : parameterBasis 1=b := by ext <;> simp [b,parameterBasis_apply]
  have symbols (i j : Fin 4) : Γ (parameterBasis i) (parameterBasis j)=J i j := funext (firstSymbol_eq v t ht.le i j)
  have ab := symbols 0 1
  have aa' := symbols 0 0
  have bb' := symbols 1 1
  rw [ea,eb] at ab
  rw [ea] at aa'
  rw [eb] at bb'
  have mapped : rangeFactorization FlatLocus.forgetOrientation v = x := Subtype.ext (FlatLocus.oriented_spec x).1
  have sep : v.val.2.1.val ⬝ᵥ v.val.2.2.val=u := congrArg (fun y : FlatLocus.Ambient => y.1.1 ⬝ᵥ y.1.2) (FlatLocus.oriented_spec x).1
  have hx : v.val.1.val 0=f.nx x := rfl
  have hy : v.val.1.val 1=f.ny x := rfl
  have h0 : (0:Params) ∈ (coreChart v).target := (center v).1
  have aa (φ : ℝ → ℝ) (hφ : ∀ u, |u|≤1 → ContDiffAt ℝ ∞ φ u) (i : Fin 3) :=
    profileChannel_second v t ht.le i φ hφ
  have spatial : second (tensor r s (secondOrderTensor t ht.le)) a b 0 =
      second (tensor r s (rationalSecondOrderTensor t ht.le)) a b 0 +
      (f.nx x)^2*(Certificate.Fx t u-Certificate.baseY.value t (-u))+
      (f.ny x)^2*(Certificate.Fy t u-Certificate.baseY.value t u) := by
    unfold secondOrderTensor
    rw [tensor_second_add r s _ _ a b h0,tensor_second_add r s _ _ a b h0]
    rw [aa,aa,sep,hx,hy]
    unfold Certificate.Fx Certificate.Fy
    ring
  have rv : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular := mapped ▸ reg
  have min := minimumEntry_schur v rv t ht
  dsimp only at min
  rw [chartEntry_fixed_second,sep] at min
  change minimumEntry v t ht.le 2 = second (tensor r s (secondOrderTensor t ht.le)) a b 0 +
    Γ a b ⬝ᵥ I *ᵥ Γ a b-Γ a a ⬝ᵥ I *ᵥ Γ b b-(g ⬝ᵥ (normalMatrix t u)⁻¹ *ᵥ g)/2 at min
  have spatialRat := rationalTensorSecond_curvature v t ht.le
  dsimp only at spatialRat
  rw [ea,eb] at spatialRat
  rw [min,spatial,spatialRat,ab,aa',bb',normalSolve_eq t u ht (sep ▸ sep_regular v rv),exportedQuadratic,mapped]
  change _ = V2form _ _ _ _ _ _ _ _ _ _ _ _ _ ↔ _
  unfold V2form
  constructor <;> intro h <;> linarith only [h]

private theorem quadratic_at_representative {t : ℝ} {ht : 0≤t} (tables : chartTablesMatch t ht)
    (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) :
    minimumEntry v t ht 2 = exportedQuadratic t v := by
  let x := rangeFactorization FlatLocus.forgetOrientation v
  let u := FlatLocus.oriented x
  have mapped : FlatLocus.forgetOrientation u = FlatLocus.forgetOrientation v := (FlatLocus.oriented_spec x).1
  have same : rangeFactorization FlatLocus.forgetOrientation u = x := Subtype.ext mapped
  have base : v.val.2=u.val.2 := Prod.ext
    (Subtype.ext (congrArg (fun y : FlatLocus.Ambient => y.1.1) mapped.symm))
    (Subtype.ext (congrArg (fun y : FlatLocus.Ambient => y.1.2) mapped.symm))
  have normals := (FlatLocus.normal_line_eq v.val.1.property u.val.1.property).mp (congrArg Prod.snd mapped.symm)
  have ru : rangeFactorization FlatLocus.forgetOrientation u ∈ FlatLocus.regular := same ▸ reg
  have entries : chartEntry v t ht 2 = chartEntry u t ht 2 := (fiber_zero v t ht 2).symm.trans
    ((funext fun z => fiberCoefficient_orientation v u reg ru base normals t ht 0 2 z).trans (fiber_zero u t ht 2))
  have table := tables.1 x reg
  change minimumEntry u t ht 2 = exportedQuadratic t u at table
  have goal : exportedQuadratic t u = exportedQuadratic t v := by unfold exportedQuadratic; rw [same]
  rw [←goal,←table]
  simp only [minimumEntry,entries]

private theorem exported_zero (t : ℝ) (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (e : v.val.1.val 0^2+v.val.1.val 1^2=0) : exportedQuadratic t v=0 := by
  let x := rangeFactorization FlatLocus.forgetOrientation v
  let f := FlatLocus.data
  have weight : f.ρ x=0 := (FlatLocus.frame v).1.symm.trans e
  have hz := (f.frame x reg).1.trans weight
  have nx : f.nx x=0 := by nlinarith only [hz,sq_nonneg (f.ny x)]
  have ny : f.ny x=0 := by nlinarith only [hz,sq_nonneg (f.nx x)]
  change V2form _ _ _ _ (f.nx x) (f.ny x) _ _ _ _ _ _ _ = 0
  simp only [V2form,nx,ny,zero_pow (by decide : 2≠0),zero_mul,mul_zero,add_zero]

set_option maxHeartbeats 1500000 in
theorem regular_identities_of_chart_tables (t : ℝ) (ht : 0<t) (hmax : t≤1/100) (tables : chartTablesMatch t ht.le) :
    ∃ χ : Scalar, matches_export t ht.le χ := by
  obtain ⟨χ,corr⟩ := corrected_equator_increment t ht.le
  refine ⟨χ,?_⟩
  intro v reg a hm
  let A := paperCoefficients t ht.le χ
  let F := (compactNormalChart t).curvature A
  let G := regularFamily v reg A
  let Q := chartEntry v t ht.le 2
  let b := stationaryTilt Q
  have ⟨station,quad⟩ := transverse_minimum_chartPolynomial v reg t ht χ a hm
  change fderiv ℝ (transverseGraph v t) 0 a = b at station
  change coeff F 2 (rawCore v) a=(hh t)^2/4*minimumEntry v t ht.le 2 at quad
  rw [quadratic_at_representative tables v reg] at quad
  refine ⟨quad,?_⟩
  intro equator
  change v.val.1.val 0^2+v.val.1.val 1^2=0 at equator
  have F2 : coeff F 2 (rawCore v) a=0 := by rw [quad,exported_zero t v reg equator,mul_zero]
  have pos : ∀ᶠ h : ℝ in 𝓝 0, ∀ z, 0≤coeff G 2 h z := by
    have near : ∀ᶠ h : ℝ in 𝓝 0, |h|<1 := continuous_id.abs.continuousAt.eventually_lt_const (by norm_num)
    filter_upwards [near] with h hh
    intro z
    let u := regularBase v reg h
    have ru : rangeFactorization FlatLocus.forgetOrientation u ∈ FlatLocus.regular := by
      dsimp [u,regularBase]; rw [dite_eq_left hh]; exact movingRepresentative_regular v reg hh
    have eq : coeff G 2 h z = fiberCoefficient u t ht.le χ 2 z := regularFamily_coeff v reg t ht.le χ h z 2
    rw [eq,fiber_two]
    have cert : 3/10*FlatLocus.weight (rangeFactorization FlatLocus.forgetOrientation u) ≤ exportedQuadratic t u :=
      Certificate.fitted_V2_on_locus ⟨ht.le,hmax⟩ _
    have lower := chart_minimizes u ru t ht z
    rw [quadratic_at_representative tables u ru] at lower
    exact (mul_nonneg (by norm_num : (0:ℝ)≤3/10) (FlatLocus.weight_nonneg _)).trans (cert.trans lower)
  have cubic := transverse_cubic_eq_regular v reg t ht χ a F2 pos
  rw [station,family_core] at cubic
  rw [cubic]
  congr 1
  obtain ⟨m,d,points,normal⟩ := equatorial_representative v equator
  let u := equatorCore m d
  have ru : rangeFactorization FlatLocus.forgetOrientation u ∈ FlatLocus.regular := by
    change u.val.2.2.val≠u.val.2.1.val ∧ u.val.2.2.val≠ -u.val.2.1.val
    rw [←points]
    exact reg
  have same (φ : Scalar) (n : ℕ) : fiberCoefficient v t ht.le φ n = fiberCoefficient u t ht.le φ n :=
    funext fun z => fiberCoefficient_orientation v u reg ru points normal t ht.le φ n z
  have Qsame : chartEntry v t ht.le 2 = chartEntry u t ht.le 2 := (fiber_zero v t ht.le 2).symm.trans ((same 0 2).trans (fiber_zero u t ht.le 2))
  have raw : fiberCoefficient u t ht.le 0 3 b = EquatorJet.forcing t (m+d,m-d) := by
    change fiberCoefficient u t ht.le 0 3 (stationaryTilt (chartEntry v t ht.le 2))=_
    rw [Qsame,fiber_zero]
    exact tables.2 m d ru
  let r := align _ _ u.property.1
  let s := align _ _ u.property.2
  let p := (chart r s).symm 0
  let e (i : Fin 4) := field r s (parameterBasis i) p
  have e0 : parameterBasis 0=((1,0),0) := by ext <;> simp [parameterBasis_apply]
  have e1 : parameterBasis 1=((0,1),0) := by ext <;> simp [parameterBasis_apply]
  have inc : EquatorJet.forcing t (m+d,m-d)+(fiberCoefficient u t ht.le χ 3 b-fiberCoefficient u t ht.le 0 3 b)=mu t := by
    simp only [fiberCoefficient,e0,e1]
    exact corr m d (e 2) (e 3) b
  rw [same χ 3]
  rw [raw] at inc
  linarith only [inc]

/-- With both finite chart identities for the paper data, the concrete sequence
uses t = 1/(100(n+1)) and the proved torus correction at each parameter. -/
theorem localHopfProblem_of_chart_tables
    (tables : ∀ t : ℝ, (ht : 0<t) → t≤1/100 → chartTablesMatch t ht.le) : LocalHopfProblem := by
  let t (n : ℕ) := (1/100:ℝ)/((n:ℝ)+1)
  have pos (n : ℕ) : 0<t n := by dsimp [t]; positivity
  have small (n : ℕ) : t n≤1/100 := by
    change (1/100:ℝ)/_≤_
    apply div_le_self (by norm_num) (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have lim : Tendsto t atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1/100:ℝ)
    rw [mul_zero] at h
    exact h.congr (fun n => by dsimp [t]; ring)
  choose χ jets using fun n => regular_identities_of_chart_tables (t n) (pos n) (small n) (tables _ (pos n) (small n))
  exact localHopfProblem_of_regular_identities t pos small lim χ jets

end
end LocalHopf.BackgroundGrowth.Transverse
