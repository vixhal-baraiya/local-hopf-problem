import LocalHopf.PerturbationGram
import LocalHopf.ChartExpansion
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! Assembly of the spatial tensor entries in the longitude-height curvature calculation. -/
namespace LocalHopf.SphereProduct.JetChart
open Real Matrix LongitudeHeight Filter Profiles
open scoped ContDiff Topology
noncomputable section

private structure RayValue where
  fn : ℝ → ℝ
  terms : Fin 3 → ℝ
  jet : SpatialJet fn (terms 0) (terms 1) (terms 2)

private def constantRay (c : ℝ) : RayValue :=
  ⟨fun _ => c, ![c,0,0], jet_const c⟩

private def addRay (x y : RayValue) : RayValue :=
  ⟨_,x.terms+y.terms,jet_add x.jet y.jet⟩

private def mulRay (x y : RayValue) : RayValue :=
  ⟨_,productJet x.terms y.terms,jet_mul x.jet y.jet⟩

private def scaleRay (c : ℝ) (x : RayValue) : RayValue :=
  ⟨_,c • x.terms,jet_scale c x.jet⟩

private def negRay (x : RayValue) : RayValue :=
  ⟨_,-x.terms,jet_neg x.jet⟩

private def compRay (f : ℝ → ℝ) (x : RayValue) (h : ContDiffAt ℝ ∞ f (x.terms 0)) : RayValue := by
  let a := x.terms 0
  let b := x.terms 1
  let c := x.terms 2
  have reg : ContDiffAt ℝ ∞ f (x.fn 0) := x.jet.value ▸ h
  refine ⟨f ∘ x.fn,![f a,deriv f a*b,deriv f a*c+iteratedDeriv 2 f a*b^2/2],reg.comp 0 x.jet.smooth,?_,?_,?_⟩
  · exact congrArg f x.jet.value
  · rw [deriv_comp 0 (reg.differentiableAt (by simp)) (x.jet.smooth.differentiableAt (by simp)),x.jet.first,x.jet.value]; rfl
  · rw [iteratedDeriv_comp_two (reg.of_le (by simp)) (x.jet.smooth.of_le (by simp)),x.jet.second,x.jet.first,x.jet.value]
    change _ = 2*(deriv f a*c+iteratedDeriv 2 f a*b^2/2)
    dsimp [a,b,c]; ring


open Polynomial in
private def polynomialRay (p : ℝ[X]) (x : RayValue) : RayValue := by
  let a := x.terms 0
  have sm : ContDiff ℝ ∞ (fun z => p.eval z) := by
    rw [show (fun z : ℝ => p.eval z)=(fun z : ℝ => aeval z p) from funext fun z => (congrFun (coe_aeval_eq_eval z) p).symm]
    exact p.contDiff_aeval ∞
  have first (y : ℝ) := (p.hasDerivAt y).deriv
  have second : iteratedDeriv 2 (fun z => p.eval z) a=p.derivative.derivative.eval a := by
    rw [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,funext first]
    exact (p.derivative.hasDerivAt a).deriv
  let j := compRay (fun z => p.eval z) x sm.contDiffAt
  refine ⟨j.fn,![p.eval a,p.derivative.eval a*x.terms 1,p.derivative.eval a*x.terms 2 +
    p.derivative.derivative.eval a*(x.terms 1)^2/2],?_⟩
  have e := j.jet
  change SpatialJet j.fn (p.eval a) (deriv (fun z => p.eval z) a*x.terms 1)
    (deriv (fun z => p.eval z) a*x.terms 2 + iteratedDeriv 2 (fun z => p.eval z) a*(x.terms 1)^2/2) at e
  rwa [first,second] at e

private def divRay (x y : RayValue) (hy : y.terms 0≠0) : RayValue := by
  let f := x.fn/y.fn
  let a := x.terms 0/y.terms 0
  let b := (x.terms 1 - a*y.terms 1)/y.terms 0
  let c := (x.terms 2 - b*y.terms 1 - a*y.terms 2)/y.terms 0
  have ny : y.fn 0≠0 := y.jet.value ▸ hy
  have sm : ContDiffAt ℝ ∞ f 0 := x.jet.smooth.div y.jet.smooth ny
  have F : SpatialJet f (f 0) (deriv f 0) (iteratedDeriv 2 f 0/2) := ⟨sm,rfl,rfl,by ring⟩
  have prod := jet_mul F y.jet
  have eq : x.fn =ᶠ[𝓝 0] fun z => f z*y.fn z := by
    filter_upwards [y.jet.smooth.continuousAt.eventually_ne ny] with z hz
    exact (div_mul_cancel₀ _ hz).symm
  have X := prod.congr eq
  have val : f 0=a := by change x.fn 0/y.fn 0=a; rw [x.jet.value,y.jet.value]
  have fb : deriv f 0=b := (eq_div_iff hy).mpr (by
    have e := X.first.symm.trans x.jet.first; rw [val] at e; linarith only [e])
  have fc : iteratedDeriv 2 f 0=2*c := by
    have e := X.second.symm.trans x.jet.second; rw [val,fb] at e
    dsimp only [c]
    field_simp [hy]
    linarith only [e]
  exact ⟨f,![a,b,c],sm,val,fb,fc⟩

open Polynomial in
private def algebraicProfile (f : ℝ → ℝ) (N D : ℝ[X]) (eq : ∀ z, f z=N.eval z/D.eval z)
    (x : RayValue) (hn : D.eval (x.terms 0)≠0) : RayValue := by
  let r := divRay (polynomialRay N x) (polynomialRay D x) hn
  exact ⟨f ∘ x.fn,r.terms,r.jet.congr (Filter.Eventually.of_forall (fun z => eq (x.fn z)))⟩

open Polynomial in
private def firstProfile (t : ℝ) (P : Bool) (x : RayValue) : RayValue :=
  if P then algebraicProfile (Pt t)
    ((C (16/5)+C (1/2)*X-C (2/5)*X^2)*(1-C (t^2)*(1+X)^2)) 1
    (fun z => by simp only [Pt,P0,eval_one,eval_mul,eval_add,eval_sub,eval_C,eval_X,eval_pow,div_one]; ring) x (by simp)
  else algebraicProfile Q (C 2*X^2-C (7/10)*X-C 4) 1 (fun z => by simp [Q]; ring) x (by simp)

open Polynomial in
private def normalProfileJets (t : ℝ) (ht : 0≤t) (x : RayValue) (hx : |x.terms 0|≤1) : Fin 4 → RayValue := by
  let T : ℝ[X] := C t
  let H : ℝ[X] := C (hh t)
  let a : ℝ[X] := C (1+t)
  let B := 1+T*(1+X)
  let d := a^2-T^2*X^2
  have hh := hh_pos ht
  have dn := D_pos ht ((sq_le_one_iff_abs_le_one _).mpr hx)
  have z := normalCorrection_denom_pos ht (abs_le.mp hx).1
  have evalD (y : ℝ) : d.eval y=Profiles.D t y := by simp [d,a,T,Profiles.D]
  refine ![algebraicProfile (normalM t) (MnumeratorExpr T X) (80*H^2*B) ?_ x ?_,
    algebraicProfile (normalN t) (NnumeratorExpr T X) (80*H^2*B^2) ?_ x ?_,
    algebraicProfile (varphi t) (a^2+T^2*X^2) (H*d^2) ?_ x ?_,
    algebraicProfile (psi t) (-(a*(H^2+6*H*T^2*X^2+T^4*(X^4-1)))) (H^2*d^3) ?_ x ?_]
  · intro y; simp [normalM,Mnumerator,MnumeratorExpr,T,H,B]
  · simpa [T,H,B] using z.1.ne'
  · intro y; simp [normalN,Nnumerator,NnumeratorExpr,T,H,B]
  · simpa [T,H,B] using z.2.ne'
  · intro y; simp [varphi,T,a,H,evalD]
  · simp only [eval_mul,eval_pow,H,eval_C,evalD]; positivity
  · intro y; simp [psi,T,a,H,evalD]
  · simp only [eval_mul,eval_pow,H,eval_C,evalD]; positivity

private def pointRay (v : FlatLocus.Representative) (d : Params) (left : Bool) (i : Fin 3) : RayValue :=
  if left then ⟨_,fun k => sphereTaylor v.val.1 v.val.2.1 (d.1.1-d.1.2) d.2.1 k i,(sphere_axes_jet v d i).1⟩
  else ⟨_,fun k => sphereTaylor v.val.1 v.val.2.2 (d.1.1+d.1.2) d.2.2 k i,(sphere_axes_jet v d i).2⟩

private def dotRay (v : FlatLocus.Representative) (d : Params) : RayValue :=
  let r (i : Fin 3) := mulRay (pointRay v d true i) (pointRay v d false i)
  ⟨fun z => pointDot ((coreChart v).symm (z • d)),fun k => ∑ i, (r i).terms k,jet_sum (fun i => (r i).jet)⟩

private def axisRay (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params)
    (opp : Bool) (a : Axis) (A : Fin 3 → R3)
    (ha : ∀ i, SpatialJet (fun z : ℝ => a ((coreChart v).symm (z • d)) i) (A 0 i) (A 1 i) (A 2 i))
    (j : Fin 4) : RayValue :=
  ⟨_,fun m => ∑ l, productJet (fun h => A h l) (loweredTaylor v t d (Pi.single l 1) (secondRotationAxis opp (Pi.single l 1)) j) m,
    moving_rotationFlat_jet v t ht d opp a A ha j⟩

private def fixedAxisRay (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params)
    (opp : Bool) (i : Fin 3) (j : Fin 4) : RayValue :=
  axisRay v t ht d opp (axis i) ![Pi.single i 1,0,0] (fun l => jet_const ((Pi.single i (1:ℝ) : R3) l)) j

private def variableAxisRay (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params)
    (plus : Bool) (j : Fin 4) : RayValue :=
  let P := sphereTaylor v.val.1 v.val.2.1 (d.1.1-d.1.2) d.2.1
  let Q := sphereTaylor v.val.1 v.val.2.2 (d.1.1+d.1.2) d.2.2
  if plus then axisRay v t ht d false (point₁+point₂) (P+Q)
    (fun i => jet_add (sphere_axes_jet v d i).1 (sphere_axes_jet v d i).2) j
  else axisRay v t ht d false (point₂-point₁) (Q-P)
    (fun i => jet_sub (sphere_axes_jet v d i).2 (sphere_axes_jet v d i).1) j

private def symRay (i j : Fin 4) (a b : Fin 4 → RayValue) : RayValue :=
  scaleRay (1/2) (addRay (mulRay (a i) (b j)) (mulRay (b i) (a j)))

private def firstRay (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (i j : Fin 4) : RayValue :=
  let u := dotRay v d
  let k := fixedAxisRay v t ht d false
  let J := fixedAxisRay v t ht d true
  let a := variableAxisRay v t ht d true
  let b := variableAxisRay v t ht d false
  let P := firstProfile t true
  let q := firstProfile t false
  let pr := symRay i j
  let A := addRay (mulRay (P (negRay u)) (pr a (k 0))) (mulRay (q (negRay u)) (pr b (J 0)))
  let B := addRay (mulRay (P u) (pr b (k 1))) (mulRay (q u) (pr a (J 1)))
  addRay (addRay (addRay A B) (scaleRay lamC (pr (k 2) (k 2)))) (scaleRay lamD (pr (k 0) (J 2)))

/-- Spatial Taylor coefficients of the six first-order channels, including derivatives of the moving axes. -/
def firstTensorTaylor (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (i j : Fin 4) :=
  (firstRay v t ht d i j).terms

set_option maxHeartbeats 900000 in
theorem firstTensor_jet (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (i j : Fin 4) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let C := firstTensorTaylor v t ht d i j
    SpatialJet (fun z : ℝ => tensor r s (firstOrderTensor t ht) (parameterBasis i) (parameterBasis j) (z • d))
      (C 0) (C 1) (C 2) := by
  apply (firstRay v t ht d i j).jet.congr
  filter_upwards with z
  let p := (coreChart v).symm (z • d)
  let V (k : Fin 4) := ambientVelocityL p (field (align _ _ v.property.1) (align _ _ v.property.2) (parameterBasis k) p)
  change (firstOrderTensor t ht).form p (V i) (V j) = _
  rw [firstOrderTensor_apply]
  simp only [firstRay,addRay,mulRay,scaleRay,negRay,symRay,
    variableAxisRay,fixedAxisRay,axisRay,dotRay,ite_true,Bool.false_eq_true,ite_false]
  simp only [div_eq_inv_mul,mul_one]
  rfl

private def speedRay (v : FlatLocus.Representative) (d : Params) (opp : Bool) (l : Fin 3) (i : Fin 4) : RayValue := by
  let A : R3 := Pi.single l 1
  let U := ((align _ _ v.property.1).symm (WithLp.toLp 2 A)).ofLp
  let V := ((align _ _ v.property.2).symm (WithLp.toLp 2 (secondRotationAxis opp A))).ofLp
  let T := axisRotationTaylor v d A (secondRotationAxis opp A)
  refine ⟨fun z => parameterBasis.equivFun (rotationCoordinates U V (z • d)) i,fun k => T k i,?_⟩
  have eq (z : ℝ) : line d.1.1 d.1.2 d.2.1 d.2.2 z = z • d := by ext <;> dsimp [line] <;> ring
  dsimp only [T]
  rw [axisRotationTaylor_eq]
  simpa only [eq] using rotationCoordinate_jet U V d.1.1 d.1.2 d.2.1 d.2.2 i

private theorem norm_eq (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (opp : Bool) (l : Fin 3) (y : Params) (hy : y ∈ (coreChart v).target) :
    let A : R3 := Pi.single l 1
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (coreChart v).symm y
    let U := rotationCoordinates (r.symm (WithLp.toLp 2 A)).ofLp (s.symm (WithLp.toLp 2 (secondRotationAxis opp A))).ofLp y
    rotationNormSq t ht opp (axis l) p =
      ∑ i, parameterBasis.equivFun U i * rotationFlat t ht opp (axis l) p (ambientVelocityL p (field r s (parameterBasis i) p)) := by
  intro A r s p U
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target hy)
  let a := rotationFlat t ht opp (axis l) p
  let φ := a.comp ((ambientVelocityL p).comp L.toContinuousLinearMap)
  have coord : ∀ d, φ d = a (ambientVelocityL p (field r s d p)) := fun d => congrArg (fun w => a (ambientVelocityL p w)) (hL d)
  have sum := congrArg φ (parameterBasis.equivFun.symm_apply_apply U)
  rw [parameterBasis.equivFun_symm_apply,map_sum] at sum
  simp_rw [φ.map_smul] at sum
  simp only [coord,smul_eq_mul] at sum
  rw [sum]
  change a (rotationField opp (axis l) p) = a (ambientVelocityL p (field r s U p))
  apply congrArg a
  change rotationField opp (axis l) p = ambientVelocityL ((chart r s).symm y) (field r s U ((chart r s).symm y))
  rw [ambient_field r s ((chart r s).map_target hy),(chart r s).right_inv hy]
  have vel := rotation_velocity_pair v A (secondRotationAxis opp A) hy
  cases opp
  · exact vel.symm
  · calc
      _ = (A ⨯₃ (ambientPoint p).1, (-A) ⨯₃ (ambientPoint p).2) := by rw [map_neg _ A]; rfl
      _ = _ := vel.symm

private def normRay (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (opp : Bool) (l : Fin 3) : RayValue := by
  let f (i : Fin 4) := mulRay (speedRay v d opp l i) (fixedAxisRay v t ht d opp l i)
  refine ⟨fun z => rotationNormSq t ht opp (axis l) ((coreChart v).symm (z • d)),fun m => ∑ i, (f i).terms m,?_⟩
  apply (jet_sum (fun i => (f i).jet)).congr
  have cont : Continuous (fun z : ℝ => z • d) := continuous_id.smul continuous_const
  have h0 : (0:ℝ) • d ∈ (coreChart v).target := by rw [zero_smul]; exact (center v).1
  filter_upwards [cont.continuousAt.preimage_mem_nhds ((coreChart v).open_target.mem_nhds h0)] with z hz
  exact norm_eq v t ht opp l _ hz


private def subRay (x y : RayValue) : RayValue :=
  ⟨_,x.terms-y.terms,jet_sub x.jet y.jet⟩

local instance : Add RayValue := ⟨addRay⟩
local instance : Sub RayValue := ⟨subRay⟩
local instance : Mul RayValue := ⟨mulRay⟩
local instance : Neg RayValue := ⟨negRay⟩

private def secondRay (profiles : Bool) (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (i j : Fin 4) : RayValue :=
  let u := dotRay v d
  let c := constantRay
  let P := pointRay v d true
  let Q := pointRay v d false
  let k := fixedAxisRay v t ht d false
  let J := fixedAxisRay v t ht d true
  let plus l := P l + Q l
  let minus l := Q l - P l
  let q := c 2*(u*u)-c 1
  let delta l m := Q l * Q m - P l * P m
  let hu : |u.terms 0| ≤ 1 := u.jet.value ▸ abs_pointDot_le _
  let hn : |(-u).terms 0| ≤ 1 := (abs_neg _).trans_le hu
  let F (x : RayValue) (h : |x.terms 0|≤1) := compRay fbb x (smoothAt_fbb (h.trans_lt (by norm_num)))
  let M (x : RayValue) (h : |x.terms 0|≤1) := normalProfileJets t ht x h 0
  let N (x : RayValue) (h : |x.terms 0|≤1) := normalProfileJets t ht x h 1
  let f := normalProfileJets t ht u hu 2
  let g := normalProfileJets t ht u hu 3
  let term w a b := w * symRay i j a b
  let aa := term (c 9 * F (-u) hn) (k 0) (k 0)
  let bb := term (c 9 * F u hu) (k 1) (k 1)
  let cc := term (normRay v t ht d false 2) (k 2) (k 2)
  let ac := term (c (1/20)*plus 2*(c (-5)-c 14*u+c 3*q)) (k 0) (k 2)
  let bc := term (c (1/20)*minus 2*(c (-5)+c 14*u+c 3*q)) (k 1) (k 2)
  let dd := term (c (1/(4*hh t))*normRay v t ht d true 0) (J 2) (J 2)
  let ad := term (c (1/400)*minus 0*(c (-406)-c 92*u+c 18*q)) (k 0) (k 2) +
    term (c (1/200)*minus 2*(c (-823)+c 154*u+c 9*q)) (k 0) (k 0) +
    term (-(M u hu*minus 0)) (J 0) (J 2) + term (-(N u hu*minus 2)) (J 0) (J 0)
  let bd := term (c (1/400)*plus 0*(c (-406)+c 92*u+c 18*q)) (k 1) (k 2) +
    term (c (1/200)*plus 2*(c (-823)-c 154*u+c 9*q)) (k 0) (k 1) +
    term (-(M (-u) hn*plus 0)) (J 1) (J 2) + term (-(N (-u) hn*plus 2)) (J 1) (J 0)
  let cd := c (-1/4)*(term (f*delta 2 0) (J 2) (J 2) + term (g*delta 2 2) (J 0) (J 2))
  let rational := c (lamC^2)*cc + c (2*lamC)*(ac+bc) + c (lamD^2)*dd + c (2*lamD)*(ad+bd) + c (2*lamC*lamD)*cd
  if profiles then aa + bb + rational else rational

/-- Spatial Taylor coefficients of all nine second-order channels, with the actual Chebyshev and normal profiles. -/
def secondTensorTaylor (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (i j : Fin 4) :=
  (secondRay true v t ht d i j).terms

private theorem fn_add (x y : RayValue) (z : ℝ) : (x+y).fn z = x.fn z + y.fn z := rfl
private theorem fn_sub (x y : RayValue) (z : ℝ) : (x-y).fn z = x.fn z - y.fn z := rfl
private theorem fn_mul (x y : RayValue) (z : ℝ) : (x*y).fn z = x.fn z * y.fn z := rfl
private theorem fn_neg (x : RayValue) (z : ℝ) : (-x).fn z = -x.fn z := rfl

set_option maxHeartbeats 900000 in
private theorem secondRay_fn (profiles : Bool) (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (i j : Fin 4) (z : ℝ) :
    tensor (align _ _ v.property.1) (align _ _ v.property.2) (if profiles then secondOrderTensor t ht else rationalSecondOrderTensor t ht)
      (parameterBasis i) (parameterBasis j) (z • d) = (secondRay profiles v t ht d i j).fn z := by
  let p := (coreChart v).symm (z • d)
  let V (k : Fin 4) := ambientVelocityL p (field (align _ _ v.property.1) (align _ _ v.property.2) (parameterBasis k) p)
  change (if profiles then secondOrderTensor t ht else rationalSecondOrderTensor t ht).form p (V i) (V j) = _
  cases profiles <;> simp only [secondRay,Bool.false_eq_true,ite_false,ite_true,fn_add,fn_sub,fn_mul,fn_neg]
  all_goals simp only [symRay,scaleRay,addRay,mulRay,constantRay,compRay,dotRay,normRay,
    fixedAxisRay,axisRay,pointRay,ite_true,Bool.false_eq_true,ite_false,Function.comp_apply]
  all_goals simp only [secondOrderTensor,rationalSecondOrderTensor,pow_two]
  all_goals rfl


set_option maxHeartbeats 1500000 in
theorem secondTensor_jet (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (i j : Fin 4) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let C := secondTensorTaylor v t ht d i j
    SpatialJet (fun z : ℝ => tensor r s (secondOrderTensor t ht) (parameterBasis i) (parameterBasis j) (z • d))
      (C 0) (C 1) (C 2) := by
  dsimp only
  unfold secondTensorTaylor
  refine (secondRay true v t ht d i j).jet.congr ?_
  exact .of_forall (secondRay_fn true v t ht d i j)

/-- Second spatial Taylor term of the seven rational channels. -/
def rationalTensorSecond (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params) (i j : Fin 4) :=
  (secondRay false v t ht d i j).terms 2

/-- The first-kind symbols of the first perturbation from its directional linear terms. -/
def firstSymbol (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (i j k : Fin 4) :=
  let L l a b := firstTensorTaylor v t ht (parameterBasis l) a b 1
  (L i j k+L j k i-L k i j)/2

theorem firstSymbol_eq (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (i j k : Fin 4) :
    let C := tensor (align _ _ v.property.1) (align _ _ v.property.2) (firstOrderTensor t ht)
    symbol C (parameterBasis i) (parameterBasis j) (parameterBasis k) 0=firstSymbol v t ht i j k := by
  intro C
  have dx (l a b : Fin 4) : D (parameterBasis l) (C (parameterBasis a) (parameterBasis b)) 0 =
      firstTensorTaylor v t ht (parameterBasis l) a b 1 :=
    (D_line _ (tensor_smooth _ _ _ _ _ (center v).1) _).trans (firstTensor_jet v t ht _ a b).first
  rw [symbol,dx,dx,dx]
  rfl

theorem rationalTensorSecond_curvature (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) :
    let C := tensor (align _ _ v.property.1) (align _ _ v.property.2) (rationalSecondOrderTensor t ht)
    let a := parameterBasis 0
    let b := parameterBasis 1
    let q := rationalTensorSecond v t ht
    second C a b 0 = q (a+b) 1 0-q a 1 0-q b 1 0-q a 1 1-q b 0 0 := by
  intro C a b q
  let h (d u w : Params) := iteratedDeriv 2 (fun s : ℝ => C u w (s • d)) 0/2
  have sm (u w : Params) (y : Params) (hy : y ∈ (coreChart v).target) : ContDiffAt ℝ ∞ (C u w) y := tensor_smooth _ _ _ _ _ hy
  have diag (d u w : Params) : D d (D d (C u w)) 0=2*h d u w := by
    rw [along_axis v _ d (sm u w) (center v).1]
    dsimp [h]; ring
  have jet (d : Params) (i j : Fin 4) : h d (parameterBasis i) (parameterBasis j)=q d i j := by
    have J := (secondRay false v t ht d i j).jet.congr (.of_forall (secondRay_fn false v t ht d i j))
    exact (div_eq_iff (by norm_num)).mpr (J.second.trans (mul_comm ..))
  rw [second_from_diagonal C h a b (fun u w => sm u w 0 (center v).1) diag]
  dsimp only [a,b]
  rw [jet,jet,jet,jet,jet]

/-- The dot product of the two sphere points on the opposite-longitude ray.
The coordinate speed of the separation angle is two. -/
theorem separation_opposite_jet (v : FlatLocus.Representative) :
    let n := v.val.1.val
    let p := v.val.2.1.val
    let q := v.val.2.2.val
    let b : Params := ((0,1),0)
    SpatialJet (fun s : ℝ => pointDot ((coreChart v).symm (s • b)))
      (p ⬝ᵥ q) (-2*((n ⨯₃ p) ⬝ᵥ q)) (-2*(p ⬝ᵥ q)) := by
  intro n p q b
  let u := n ⨯₃ p
  let w := n ⨯₃ q
  have pp := sphere_axes_jet v b
  have J (i : Fin 3) :
      SpatialJet (fun z : ℝ => point₁ ((coreChart v).symm (z • b)) i * point₂ ((coreChart v).symm (z • b)) i)
        (p i*q i) (-(u i)*q i+p i*w i) ((-(1/2:ℝ)*p i)*q i + -(u i)*w i+p i*(-(1/2:ℝ)*q i)) := by
    have d := jet_mul (pp i).1 (pp i).2
    simp [b,sphereTaylor] at d
    rw [←cross_anticomm v.val.1.val v.val.2.1.val] at d
    simpa [p,q,n,u,w,b] using d
  have sum := jet_sum J
  have alt : p ⬝ᵥ w = -(u ⬝ᵥ q) := by
    rw [dotProduct_comm u q]
    dsimp only [w,u]
    rw [triple_product_permutation p n q,triple_product_permutation q n p,←cross_anticomm p q,dotProduct_neg]
  have uv : u ⬝ᵥ w = p ⬝ᵥ q := by
    dsimp only [u,w]
    rw [cross_dot_cross,show n ⬝ᵥ n=1 from v.val.1.property, show n ⬝ᵥ q=0 from v.property.2]
    ring
  have fst : ∑ i, (-(u i)*q i+p i*w i) = -2*(u ⬝ᵥ q) := by
    simp only [neg_mul,Finset.sum_add_distrib,Finset.sum_neg_distrib]
    change -(u ⬝ᵥ q)+p ⬝ᵥ w=_
    rw [alt]; ring
  have snd : ∑ i, ((-(1/2:ℝ)*p i)*q i + -(u i)*w i+p i*(-(1/2:ℝ)*q i)) = -2*(p ⬝ᵥ q) := by
    calc
      _ = ∑ i, (-(p i*q i) - u i*w i) := Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by simp only [Finset.sum_sub_distrib,Finset.sum_neg_distrib]; change -(p ⬝ᵥ q)-u ⬝ᵥ w=_; rw [uv]; ring
  rw [fst,snd] at sum
  exact sum

/-- The angular second derivative used by both scalar profile channels. -/
theorem angular_profile_jet (v : FlatLocus.Representative) (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ 2 f (v.val.2.1.val ⬝ᵥ v.val.2.2.val)) :
    let u := v.val.2.1.val ⬝ᵥ v.val.2.2.val
    let b : Params := ((0,1),0)
    iteratedDeriv 2 (fun s : ℝ => f (pointDot ((coreChart v).symm (s • b)))) 0 =
      -4*(u*deriv f u+(u^2-1)*iteratedDeriv 2 f u) := by
  intro u b
  let w := (v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val
  let U (s : ℝ) := pointDot ((coreChart v).symm (s • b))
  have J : SpatialJet U u (-2*w) (-2*u) := separation_opposite_jet v
  have C : u^2+w^2=1 := separation_circle v
  change iteratedDeriv 2 (f ∘ U) 0=_
  rw [iteratedDeriv_comp_two (J.value ▸ hf : ContDiffAt ℝ 2 f (U 0)) (J.smooth.of_le (by simp)),J.value,J.first,J.second]
  linear_combination 4*iteratedDeriv 2 f u*C

/-- Actual fixed-plane curvature contraction of each nonpolynomial profile channel,
including its axis weight and both derivatives of the profile. -/
theorem profileChannel_second (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t)
    (i : Fin 3) (f : ℝ → ℝ) (hf : ∀ u, |u|≤1 → ContDiffAt ℝ ∞ f u) :
    let u := v.val.2.1.val ⬝ᵥ v.val.2.2.val
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    second (tensor r s (profileChannel t ht i f hf)) ((1,0),0) ((0,1),0) 0 =
      v.val.1.val i^2 * (18/(Profiles.hh t)^2) * (u*deriv f u+(u^2-1)*deriv (deriv f) u) := by
  intro u r s
  let F : Scalar := ⟨fun p => f (pointDot p),fun p => (hf _ (abs_pointDot_le p)).contMDiffAt.comp p (pointDot.contMDiff p)⟩
  let w := scalar 9 * F
  let b : Params := ((0,1),0)
  let g (z : ℝ) := f (pointDot ((coreChart v).symm (z • b)))
  have h := flat_profile_second v t ht i w
  change second (tensor r s (profileChannel t ht i f hf)) ((1,0),0) b 0 =
    -((v.val.1.val i/Profiles.hh t)^2/2) * iteratedDeriv 2 (fun z : ℝ => 9*g z) 0 at h
  have hu : |u|≤1 := abs_le.mpr (FlatLocus.frame v).2.2.2.2
  have calc₂ : iteratedDeriv 2 g 0 = -4*(u*deriv f u+(u^2-1)*iteratedDeriv 2 f u) :=
    angular_profile_jet v f ((hf _ hu).of_le (by simp))
  rw [h,iteratedDeriv_const_mul_field,calc₂,show iteratedDeriv 2 f = deriv (deriv f) by
    rw [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]]
  ring

end
end LocalHopf.SphereProduct.JetChart
