import LocalHopf.PerturbedCurvature
import LocalHopf.CurvatureBasis

/-! Exact division of the chart curvature by the Gram determinant along moving planes. -/
namespace LocalHopf.SphereProduct.JetChart
open Real Matrix Filter Set LongitudeHeight Polynomial
open scoped Topology ContDiff
noncomputable section

private abbrev Mat (R : Type) := Matrix (Fin 4) (Fin 4) R

/-- Background and first perturbation, with the amplitude terms needed by the normal gradient. -/
def linearGramPolys (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (m : Fin 3) : Mat ℝ[X] :=
  let G := metricTaylor t (v.val.2.1.val ⬝ᵥ v.val.2.2.val) ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val) d
  fun i j => C (G m i j) + X*C (firstTensorTaylor v t ht d i j m)

/-- Metric and its directional spatial derivatives, as polynomials in the perturbation amplitude. -/
def gramPolys (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (m : Fin 3) : Mat ℝ[X] :=
  fun i j => linearGramPolys v t ht d m i j + X^2*C (secondTensorTaylor v t ht d i j m)

private def pairOver {R : Type} [CommRing R] (ofReal : ℝ →+* R) (M : Mat R) (a b : Params) :=
  ∑ i, ∑ j, ofReal (parameterBasis.equivFun a i * parameterBasis.equivFun b j) * M i j

private def spatialSecond {R : Type} [CommRing R] (ofReal : ℝ →+* R) (T : Params → Fin 3 → Mat R) (a b : Params) :=
  let q (d u v : Params) := pairOver ofReal (T d 2) u v
  q (a+b) b a-q a b a-q b b a-q a b b-q b a a

private def spatialSymbols {R : Type} [CommRing R] (ofReal : ℝ →+* R) (T : Params → Fin 3 → Mat R) (a b : Params) (i : Fin 4) :=
  let first (d u v : Params) := pairOver ofReal (T d 1) u v
  (first a b (parameterBasis i)+first b (parameterBasis i) a-first (parameterBasis i) a b)*ofReal (1/2)

/-- The cleared polynomial numerator at a fixed pair of chart vectors. -/
def chartPolynomial (T : Params → Fin 3 → Mat ℝ[X]) (a b : Params) :=
  let G := T 0 0
  let J := spatialSymbols C T
  spatialSecond C T a b * G.det + J a b ⬝ᵥ G.adjugate *ᵥ J a b - J a a ⬝ᵥ G.adjugate *ᵥ J b b

private theorem eval_gramPolys (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (h : ℝ) (d : Params) (m : Fin 3) :
    (gramPolys v t ht d m).map (evalRingHom h) = uncorrectedTaylor v t ht h d m := by
  ext i j
  change ((gramPolys v t ht d m i j).eval h) = _
  simp only [gramPolys,linearGramPolys,uncorrectedTaylor,eval_add,eval_mul,eval_C,eval_X,eval_pow]

private theorem eval_pairOver (h : ℝ) (M : Mat ℝ[X]) (a b : Params) :
    (pairOver C M a b).eval h = pairOver (RingHom.id ℝ) (M.map (evalRingHom h)) a b := by
  simp [pairOver,eval_finsetSum]

private theorem eval_chartPolynomial (T : Params → Fin 3 → Mat ℝ[X]) (h : ℝ) (a b : Params)
    (hd : ((T 0 0).map (evalRingHom h)).det ≠ 0) :
    let M := fun d i => (T d i).map (evalRingHom h)
    (chartPolynomial T a b).eval h / (T 0 0).det.eval h = contractSpatial M (M 0 0)⁻¹ a b := by
  intro M
  let G := T 0 0
  let J := spatialSymbols (RingHom.id ℝ) M
  have e (x y : Params) (i : Fin 4) :
      (spatialSymbols C T x y i).eval h = J x y i := by
    simp [J,spatialSymbols,M,eval_pairOver]
  have sec : (spatialSecond C T a b).eval h = spatialSecond (RingHom.id ℝ) M a b := by
    simp [spatialSecond,M,eval_pairOver]
  have det : G.det.eval h = (M 0 0).det := (evalRingHom h).map_det G
  have adj := (evalRingHom h).map_adjugate G
  have pair (x y w z : Params) :
      ((spatialSymbols C T x y) ⬝ᵥ G.adjugate *ᵥ (spatialSymbols C T w z)).eval h =
        J x y ⬝ᵥ (M 0 0).adjugate *ᵥ J w z := by
    rw [←show G.adjugate.map (evalRingHom h) = (M 0 0).adjugate from adj]
    simp [dotProduct,mulVec,eval_finsetSum,e]
  have sym (x y : Params) (i : Fin 4) : J x y i =
      (pairOver (RingHom.id ℝ) (M x 1) y (parameterBasis i)+pairOver (RingHom.id ℝ) (M y 1) (parameterBasis i) x-
        pairOver (RingHom.id ℝ) (M (parameterBasis i) 1) x y)/2 := by simp [J,spatialSymbols,div_eq_mul_inv]
  let B := M 0 0
  have form : contractSpatial M B⁻¹ a b =
      spatialSecond (RingHom.id ℝ) M a b + J a b ⬝ᵥ B⁻¹ *ᵥ J a b - J a a ⬝ᵥ B⁻¹ *ᵥ J b b := by
    have f (x y : Params) := funext (sym x y)
    simp only [f]; rfl
  rw [form,chartPolynomial,eval_sub,eval_add,eval_mul,sec,det,pair,pair,Matrix.inv_def,Ring.inverse_eq_inv]
  simp only [smul_mulVec,dotProduct_smul,smul_eq_mul]
  change _ / B.det = _ + B.det⁻¹ * _ - B.det⁻¹ * _
  field_simp [show B.det ≠ 0 from hd]
  rfl

private theorem gramPolys_det (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) {h : ℝ}
    {g : SmoothMetric} (hg : Realizes g h (paperCoefficients t ht 0)) :
    ((gramPolys v t ht 0 0).map (evalRingHom h)).det ≠ 0 := by
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (chart r s).symm 0
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target (center v).1)
  let b := parameterBasis.map L.toLinearEquiv
  have hb (i : Fin 4) : b i = field r s (parameterBasis i) p := by simpa [b] using hL (parameterBasis i)
  have eq : (gramPolys v t ht 0 0).map (evalRingHom h) = gramMatrix g b := by
    rw [eval_gramPolys]
    ext i j
    rw [show gramMatrix g b i j = g.inner p (b i) (b j) from rfl,hb,hb]
    change _ = coefficient r s g (parameterBasis i) (parameterBasis j) 0
    exact (by simpa only [zero_smul] using (uncorrected_jet v t ht hg 0 i j).value.symm)
  exact eq ▸ (gram_isUnit g b).ne_zero


/-- The amplitude-zero determinant is positive and independent of the frame rotation. -/
theorem gramPolys_det_zero (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) :
    let u := v.val.2.1.val ⬝ᵥ v.val.2.2.val
    (gramPolys v t ht 0 0).det.coeff 0 = 1/(4*Profiles.hh t*Profiles.D t u) := by
  intro u
  let B := metricTaylor t u ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val) 0 0
  have h : (gramPolys v t ht 0 0).map (evalRingHom 0) = B := by
    rw [eval_gramPolys]
    ext i j
    simp [uncorrectedTaylor,B,u]
  rw [coeff_zero_eq_eval_zero,show (gramPolys v t ht 0 0).det.eval 0 =
    ((gramPolys v t ht 0 0).map (evalRingHom 0)).det from (evalRingHom (0:ℝ)).map_det _,h]
  have circ := separation_circle v
  have hu : u^2≤1 := by dsimp only at circ; dsimp [u]; nlinarith only [circ,sq_nonneg ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val)]
  have dn := (Profiles.D_pos ht hu).ne'
  have hn := (Profiles.hh_pos ht).ne'
  have det₄ (a b c : ℝ) : (!![a,0,0,0;0,1,0,0;0,0,b,c;0,0,c,b] : Matrix (Fin 4) (Fin 4) ℝ).det=a*(b*b-c*c) := by
    rw [Matrix.det_succ_row_zero]
    norm_num [Matrix.det_fin_three,Fin.sum_univ_four,Fin.succAbove]
  rw [show B.det=_ from det₄ (1+2*t)⁻¹ ((1+t)/(2*Profiles.D t u)) (-t*u/(2*Profiles.D t u))]
  unfold Profiles.hh
  have hh : 1+2*t ≠ 0 := hn
  field_simp [hh,dn]
  unfold Profiles.D
  ring

theorem curvature_eq_chartPolynomial (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) {h : ℝ}
    {g : SmoothMetric} (hg : Realizes g h (paperCoefficients t ht 0)) (a b : Params) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    let T := gramPolys v t ht
    curvatureNumerator g p (field r s a p) (field r s b p) = (chartPolynomial T a b).eval h / (T 0 0).det.eval h := by
  dsimp only
  rw [curvature_eq_uncorrectedNumerator v t ht hg a b,eval_chartPolynomial _ _ _ _ (gramPolys_det v t ht hg)]
  simp only [eval_gramPolys]
  rfl

private def samplePolynomial (x p m : ℝ[X]) :=
  x + X*(p-m)*C (1/2) + X^2*((p+m)*C (1/2)-x)

private theorem eval_sample (h : ℝ) (x p m : ℝ[X]) :
    (samplePolynomial x p m).eval h = quadraticSamples h (x.eval h) (p.eval h) (m.eval h) := by
  simp only [samplePolynomial,quadraticSamples,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow]; ring

private theorem samples_div (h a b c d : ℝ) :
    quadraticSamples h (a/d) (b/d) (c/d) = quadraticSamples h a b c / d := by
  unfold quadraticSamples; ring

private def speeds (z : Fin 4 → ℝ) : Params × Params := (((0,0),z 0,z 1),((0,0),z 2,z 3))

/-- Exact numerator polynomial for the evolving graph. The nine fixed-plane
samples recover the two quadratic dependencies on the spanning vectors. -/
def movingChartPolynomial (T : Params → Fin 3 → Mat ℝ[X]) (z : Fin 4 → ℝ) :=
  let a := parameterBasis 0
  let b := parameterBasis 1
  let (u,w) := speeds z
  let row q := samplePolynomial (chartPolynomial T q b) (chartPolynomial T q (b+w)) (chartPolynomial T q (b-w))
  samplePolynomial (row a) (row (a+u)) (row (a-u))

private theorem eval_moving (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) {h : ℝ}
    {g : SmoothMetric} (hg : Realizes g h (paperCoefficients t ht 0)) (z : Fin 4 → ℝ) :
    let T := gramPolys v t ht
    uncorrectedNumerator v t ht h ((1,0),h*z 0,h*z 1) ((0,1),h*z 2,h*z 3) =
      (movingChartPolynomial T z).eval h / (T 0 0).det.eval h := by
  intro T
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (chart r s).symm 0
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target (center v).1)
  let K (a b : Params) := curvatureNumerator g p (L a) (L b)
  have ac (a b : Params) : K a b = uncorrectedNumerator v t ht h a b := by
    dsimp only [K]; rw [hL,hL]; exact curvature_eq_uncorrectedNumerator v t ht hg a b
  have calcK (a b : Params) : K a b = (chartPolynomial T a b).eval h / (T 0 0).det.eval h := by
    dsimp only [K]; rw [hL,hL]; exact curvature_eq_chartPolynomial v t ht hg a b
  let a := parameterBasis 0
  let b := parameterBasis 1
  let u := (speeds z).1
  let w := (speeds z).2
  have aeq : a+h • u=((1,0),h*z 0,h*z 1) := by ext <;> simp [a,u,speeds,parameterBasis_apply]
  have beq : b+h • w=((0,1),h*z 2,h*z 3) := by ext <;> simp [b,w,speeds,parameterBasis_apply]
  have left (x : Params) :
      K (a+h • u) x = quadraticSamples h (K a x) (K (a+u) x) (K (a-u) x) := by
    simpa only [K,L.map_add,L.map_sub,L.map_smul] using
      (curvatureNumerator_interpolate g p (L a) (L u) (L x) h).1
  have right (x : Params) :
      K x (b+h • w) = quadraticSamples h (K x b) (K x (b+w)) (K x (b-w)) := by
    simpa only [K,L.map_add,L.map_sub,L.map_smul] using
      (curvatureNumerator_interpolate g p (L b) (L w) (L x) h).2
  rw [←aeq,←beq,←ac,left]
  simp only [right,calcK,movingChartPolynomial,eval_sample,samples_div]
  rfl

/-- All intrinsic graph coefficients of the uncorrected family, computed by finite
polynomial division from the spatial tensor entries. In particular this calculates
the input to the four-dimensional normal equation and the cubic value at its solution. -/
theorem graphCoefficient_eq_chartPolynomial (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t)
    (z : Fin 4 → ℝ) (n : ℕ) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    let e (i : Fin 4) := field r s (parameterBasis i) p
    let A := paperCoefficients t ht 0
    let T := gramPolys v t ht
    let D := (T 0 0).det
    graphCoefficient A (e 0) (e 1) (e 2) (e 3) n z = quotientCoeff (residual (movingChartPolynomial T z) D n) D := by
  intro r s p e A T D
  let N := movingChartPolynomial T z
  let f (h : ℝ) := uncorrectedNumerator v t ht h ((1,0),h*z 0,h*z 1) ((0,1),h*z 2,h*z 3)
  have eq : f =ᶠ[𝓝 0] fun h => N.eval h / D.eval h := by
    filter_upwards [paper_metrics_realize t ht (0:Scalar)] with h hg
    exact eval_moving v t ht hg.choose_spec z
  have zero := (paper_metrics_realize t ht (0:Scalar)).self_of_nhds
  have det := gramPolys_det v t ht zero.choose_spec
  have hd : D.eval 0 ≠ 0 := ((evalRingHom (0:ℝ)).map_det (T 0 0)).trans_ne det
  calc
    _ = iteratedDeriv n f 0 / n.factorial := graphCoefficient_eq_uncorrected v t ht z n
    _ = _ := (congrArg (· / (n.factorial : ℝ)) (eq.iteratedDeriv_eq (n := n))).trans
      (quotientCoeff_eq_derivative N D hd n)



private theorem twice_half : (2 : ℝ[X])*C (1/2:ℝ)=1 := by
  simpa only [map_mul,map_ofNat,map_one] using congrArg (C : ℝ →+* ℝ[X]) (show (2:ℝ)*(1/2)=1 by norm_num)

private theorem sample_same (x : ℝ[X]) : samplePolynomial x x x=x := by
  unfold samplePolynomial
  linear_combination X^2*x*twice_half

private theorem sample_diff (x a b : ℝ[X]) :
    samplePolynomial x a b-samplePolynomial x b a=X*(a-b) := by
  unfold samplePolynomial
  linear_combination X*(a-b)*twice_half

private theorem moving_axis_diff (T : Params → Fin 3 → Mat ℝ[X]) (i : Fin 4) :
    let z : Fin 4 → ℝ := Pi.single i 1
    let a := parameterBasis 0
    let b := parameterBasis 1
    let u := (speeds z).1
    let w := (speeds z).2
    movingChartPolynomial T z - movingChartPolynomial T (-z) =
      X*(chartPolynomial T (a+u) (b+w)-chartPolynomial T (a-u) (b-w)) := by
  intro z a b u w
  have negU : (speeds (-z)).1 = -u := by ext <;> simp [u,speeds]
  have negW : (speeds (-z)).2 = -w := by ext <;> simp [w,speeds]
  have split : u=0 ∨ w=0 := by fin_cases i <;> simp [u,w,speeds,z]
  dsimp only [u,w] at split negU negW
  dsimp only [u,w,a,b]
  rcases split with L | R
  · simp only [movingChartPolynomial,negU,negW,L,neg_zero,add_zero,sub_zero,sub_neg_eq_add,←sub_eq_add_neg,sample_same,sample_diff]
  · simp only [movingChartPolynomial,negU,negW,R,neg_zero,add_zero,sub_zero,sub_neg_eq_add,←sub_eq_add_neg,sample_same,sample_diff]

private theorem quotientNext_sub (p q d : ℝ[X]) : quotientNext (p-q) d=quotientNext p d-quotientNext q d := by
  unfold quotientNext quotientCoeff
  rw [coeff_sub,sub_div,map_sub,sub_mul]
  ext i; simp; ring

private theorem coefficient_sub (p q d : ℝ[X]) (n : ℕ) : quotientCoeff (residual (p-q) d n) d =
    quotientCoeff (residual p d n) d-quotientCoeff (residual q d n) d := by
  have eq : residual (p-q) d n=residual p d n-residual q d n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [residual,ih,quotientNext_sub]
  rw [eq,quotientCoeff,coeff_sub,sub_div]
  rfl

/-- The four entries of the normal gradient from fixed planes at opposite unit tilts. -/
def fixedGradient (T : Params → Fin 3 → Mat ℝ[X]) (i : Fin 4) : ℝ :=
  let d := (T 0 0).det
  let fixed (u w : Params) := quotientCoeff (residual (chartPolynomial T u w) d 1) d
  let z : Fin 4 → ℝ := Pi.single i 1
  let a := parameterBasis 0
  let b := parameterBasis 1
  let u : Params := ((0,0),z 0,z 1)
  let w : Params := ((0,0),z 2,z 3)
  (fixed (a+u) (b+w)-fixed (a-u) (b-w))/2

/-- The moving quadratic has the fixed-plane first-order gradient used in the Schur complement. -/
theorem moving_gradient_entry (T : Params → Fin 3 → Mat ℝ[X]) (i : Fin 4) :
    let d := (T 0 0).det
    tiltGradient (fun v => quotientCoeff (residual (movingChartPolynomial T v) d 2) d) 0 i = fixedGradient T i := by
  intro d
  let z : Fin 4 → ℝ := Pi.single i 1
  let a := parameterBasis 0
  let b := parameterBasis 1
  let u := (speeds z).1
  let w := (speeds z).2
  unfold tiltGradient
  simp only [zero_add,zero_sub]
  apply congrArg (fun x : ℝ => x/2)
  rw [←coefficient_sub (movingChartPolynomial T z) (movingChartPolynomial T (-z)) d 2,moving_axis_diff T i]
  let P := chartPolynomial T (a+u) (b+w) - chartPolynomial T (a-u) (b-w)
  have shift : quotientNext (X*P) d=P := by ext i; simp [quotientNext,quotientCoeff]
  change quotientCoeff (quotientNext (quotientNext (X*P) d) d) d=_
  rw [shift]
  exact coefficient_sub _ _ _ 1


private abbrev FirstOrder := ℝ[X] ⧸ Ideal.span {(X : ℝ[X])^2}
private def reduceFirst : ℝ[X] →+* FirstOrder := Ideal.Quotient.mk _

private theorem reduced_coeff {p q : ℝ[X]} (h : reduceFirst p=reduceFirst q) (n : ℕ) (hn : n<2) :
    p.coeff n=q.coeff n := by
  have mem : p-q ∈ Ideal.span {(X : ℝ[X])^2} := Ideal.Quotient.eq.mp h
  have dvd := Ideal.mem_span_singleton.mp mem
  exact sub_eq_zero.mp ((coeff_sub p q n).symm.trans (X_pow_dvd_iff.mp dvd n hn))

private theorem firstQuotient_congr {p q d e : ℝ[X]} (num : reduceFirst p=reduceFirst q) (den : reduceFirst d=reduceFirst e) :
    quotientCoeff (residual p d 1) d = quotientCoeff (residual q e 1) e := by
  simp only [residual,quotientNext,quotientCoeff,coeff_divX,zero_add,coeff_sub,coeff_C_mul]
  rw [reduced_coeff num 0 (by decide),reduced_coeff num 1 (by decide),reduced_coeff den 0 (by decide),reduced_coeff den 1 (by decide)]

private theorem reduced_chart {T U : Params → Fin 3 → Mat ℝ[X]}
    (jets : ∀ d m i j, reduceFirst (T d m i j)=reduceFirst (U d m i j)) (a b : Params) :
    reduceFirst (chartPolynomial T a b) = reduceFirst (chartPolynomial U a b) := by
  have mat (d : Params) (m : Fin 3) : (T d m).map reduceFirst = (U d m).map reduceFirst :=
    Matrix.ext (jets d m)
  have adj : (T 0 0).adjugate.map reduceFirst = (U 0 0).adjugate.map reduceFirst := by
    exact (reduceFirst.map_adjugate (T 0 0)).trans ((congrArg Matrix.adjugate (mat 0 0)).trans (reduceFirst.map_adjugate (U 0 0)).symm)
  have det : reduceFirst (T 0 0).det = reduceFirst (U 0 0).det := by
    exact (reduceFirst.map_det (T 0 0)).trans ((congrArg Matrix.det (mat 0 0)).trans (reduceFirst.map_det (U 0 0)).symm)
  have paired (d : Params) (m : Fin 3) (x y : Params) :
      reduceFirst (pairOver C (T d m) x y)=reduceFirst (pairOver C (U d m) x y) := by
    simp only [pairOver,map_sum,map_mul,jets]
  have sym (x y : Params) (i : Fin 4) :
      reduceFirst (spatialSymbols C T x y i)=reduceFirst (spatialSymbols C U x y i) := by
    simp only [spatialSymbols,map_mul,map_sub,map_add,paired]
  have sec : reduceFirst (spatialSecond C T a b)=reduceFirst (spatialSecond C U a b) := by
    simp only [spatialSecond,map_sub,paired]
  have entry (i j : Fin 4) : reduceFirst ((T 0 0).adjugate i j)=reduceFirst ((U 0 0).adjugate i j) := congrFun (congrFun adj i) j
  simp only [chartPolynomial,map_sub,map_add,map_mul,det,sec,dotProduct,mulVec,map_sum,sym,entry]

/-- The normal gradient only depends on the background and first perturbing
tensor. All second-order profile and mixed tensor channels drop out. -/
theorem fixedGradient_linear (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) :
    fixedGradient (gramPolys v t ht) = fixedGradient (linearGramPolys v t ht) := by
  let P := linearGramPolys v t ht
  let T := gramPolys v t ht
  have zero : reduceFirst ((X : ℝ[X])^2)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have jets (d : Params) (m : Fin 3) (i j : Fin 4) : reduceFirst (T d m i j)=reduceFirst (P d m i j) := by
    simp only [T,gramPolys,P,linearGramPolys,map_add,map_mul,zero,zero_mul,add_zero]
  have mat : (T 0 0).map reduceFirst=(P 0 0).map reduceFirst := Matrix.ext (jets 0 0)
  have det : reduceFirst (T 0 0).det=reduceFirst (P 0 0).det := (reduceFirst.map_det (T 0 0)).trans ((congrArg Matrix.det mat).trans (reduceFirst.map_det (P 0 0)).symm)
  have eq (a b : Params) := firstQuotient_congr (reduced_chart jets a b) det
  funext i
  unfold fixedGradient
  dsimp only
  rw [eq,eq]

end
end LocalHopf.SphereProduct.JetChart
