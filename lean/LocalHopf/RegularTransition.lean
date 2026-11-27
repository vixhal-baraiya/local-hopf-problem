import LocalHopf.RegularGraph

/-! The moving great circle and the graph coordinates of the transverse planes at a regular sphere pair. -/
namespace LocalHopf.BackgroundGrowth.Transverse
open Real Matrix Filter Set SphereProduct JetChart
open scoped ContDiff Topology
noncomputable section

private def signedSeparation (v : FlatLocus.Representative) :=
  (v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val

/-- Common unit normal of the two base points after the transverse height displacement,
with its sign chosen to agree with the original representative at height zero. -/
def movingNormal (v : FlatLocus.Representative) (h : ℝ) : R3 :=
  let w := signedSeparation v
  let rad := sqrt (1-h^2)
  (sqrt (1-h^2+(h/w)^2))⁻¹ • (rad • v.val.1.val - (h/w) • (v.val.1.val ⨯₃ v.val.2.1.val))

private theorem separation_ne (v : FlatLocus.Representative) (hv : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) :
    signedSeparation v ≠ 0 := by
  let p := v.val.2.1.val
  let q := v.val.2.2.val
  let c := p ⬝ᵥ q
  intro e
  have circle := separation_circle v
  change c^2+(signedSeparation v)^2=1 at circle
  rw [e,zero_pow (by decide : 2≠0),add_zero] at circle
  have hp : p ⬝ᵥ p=1 := v.val.2.1.property
  have hq : q ⬝ᵥ q=1 := v.val.2.2.property
  have sep : q≠p ∧ q≠-p := hv
  rcases sq_eq_one_iff.mp circle with h|h
  · apply sep.1
    apply sub_eq_zero.mp
    apply dotProduct_self_eq_zero.mp
    rw [sub_dotProduct,dotProduct_sub,dotProduct_sub,hp,hq,dotProduct_comm q p,show p ⬝ᵥ q=1 from h]
    norm_num
  · apply sep.2
    apply eq_neg_of_add_eq_zero_left
    apply dotProduct_self_eq_zero.mp
    rw [add_dotProduct,dotProduct_add,dotProduct_add,hp,hq,dotProduct_comm q p,show p ⬝ᵥ q= -1 from h]
    norm_num

theorem movingNormal_zero (v : FlatLocus.Representative) : movingNormal v 0 = v.val.1.val := by simp [movingNormal]

theorem movingNormal_smooth (v : FlatLocus.Representative) {h : ℝ} (hreg : |h|<1) :
    ContDiffAt ℝ ∞ (movingNormal v) h := by
  have pos : 0<1-h^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one ..).mpr hreg)
  have len : 0<1-h^2+(h/signedSeparation v)^2 := by positivity
  unfold movingNormal
  fun_prop (disch := first | exact pos.ne' | exact len.ne' | positivity)

private theorem movingNormal_frame (v : FlatLocus.Representative)
    (hv : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) {h : ℝ} (hr : |h|<1) :
    let n := movingNormal v h
    let p := v.val.2.1.val
    let q := point v.val.1.val v.val.2.2.val h
    n ⬝ᵥ n=1 ∧ n ⬝ᵥ p=0 ∧ n ⬝ᵥ q=0 ∧ q ⬝ᵥ q=1 := by
  let N := v.val.1.val
  let P := v.val.2.1.val
  let Q := v.val.2.2.val
  let L := N ⨯₃ P
  let w := signedSeparation v
  let R := sqrt (1-h^2)
  let H := 1-h^2+(h/w)^2
  have nn : N ⬝ᵥ N=1 := v.val.1.property
  have qq : Q ⬝ᵥ Q=1 := v.val.2.2.property
  have np : N ⬝ᵥ P=0 := v.property.1
  have nq : N ⬝ᵥ Q=0 := v.property.2
  have ll := (cross_unit N P nn v.val.2.1.property np).1
  have nl : N ⬝ᵥ L=0 := dot_self_cross N P
  have lp : L ⬝ᵥ P=0 := cross_dot_right ..
  have lq : L ⬝ᵥ Q=w := rfl
  have pos : 0<1-h^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one ..).mpr hr)
  have len : 0<H := add_pos_of_pos_of_nonneg pos (sq_nonneg _)
  have R2 : R^2=1-h^2 := sq_sqrt pos.le
  have wne := separation_ne v hv
  change ((sqrt H)⁻¹ • (R • N-(h/w) • L)) ⬝ᵥ _ = 1 ∧
    ((sqrt H)⁻¹ • (R • N-(h/w) • L)) ⬝ᵥ P = 0 ∧
    ((sqrt H)⁻¹ • (R • N-(h/w) • L)) ⬝ᵥ (R • Q+h • N) = 0 ∧ (R • Q+h • N) ⬝ᵥ (R • Q+h • N)=1
  change ((sqrt H)⁻¹ • (R • N-(h/w) • L)) ⬝ᵥ ((sqrt H)⁻¹ • (R • N-(h/w) • L)) = 1 ∧ _
  simp only [smul_dotProduct,dotProduct_smul,add_dotProduct,dotProduct_add,sub_dotProduct,dotProduct_sub,smul_eq_mul,
    nn,qq,np,nq,nl,lp,lq,show L ⬝ᵥ L=1 from ll,dotProduct_comm L N,dotProduct_comm Q N,mul_one,mul_zero,zero_add,add_zero,sub_zero]
  refine ⟨?_,trivial,?_,?_⟩
  · calc
      _ = (sqrt H)⁻¹^2*(R^2+(h/w)^2) := by ring
      _ = 1 := by rw [R2,inv_pow,sq_sqrt len.le]; exact inv_mul_cancel₀ len.ne'
  · have cancel : h/w*w=h := div_mul_cancel₀ h wne
    linear_combination -(sqrt H)⁻¹*R*cancel
  · nlinarith only [R2]

/-- Regular-locus parametrization of the base points of the actual transverse disk. -/
def movingRepresentative (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) (h : ℝ) (hr : |h|<1) : FlatLocus.Representative :=
  let H := movingNormal_frame v reg hr
  ⟨(⟨movingNormal v h,H.1⟩,v.val.2.1,⟨point v.val.1.val v.val.2.2.val h,H.2.2.2⟩),H.2.1,H.2.2.1⟩

/-- Longitude and height components obtained by resolving the two ambient velocities against the great-circle frame. -/
def readFrame (n p q : R3) (V : Cheeger.V) : Params :=
  let a := (n ⨯₃ p) ⬝ᵥ V.1
  let b := (n ⨯₃ q) ⬝ᵥ V.2
  (((a+b)/2,(b-a)/2),n ⬝ᵥ V.1,n ⬝ᵥ V.2)

theorem readFrame_field (v : FlatLocus.Representative) (d : Params) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    readFrame v.val.1.val v.val.2.1.val v.val.2.2.val (ambientVelocityL p (field r s d p))=d := by
  intro r s p
  have center : (0:Params) ∈ (chart r s).target := (JetChart.center v).1
  change readFrame _ _ _ (ambientVelocityL ((chart r s).symm 0) (field r s d ((chart r s).symm 0))) = d
  rw [ambient_field r s ((chart r s).map_target center),(chart r s).right_inv center]
  have vel := center_velocity v d
  change fderiv ℝ (ambientPoint ∘ (chart r s).symm) 0 d = _ at vel
  rw [vel]
  have U := (cross_unit _ _ v.val.1.property v.val.2.1.property v.property.1).1
  have V := (cross_unit _ _ v.val.1.property v.val.2.2.property v.property.2).1
  have unit : v.val.1.val ⬝ᵥ v.val.1.val=1 := v.val.1.property
  ext <;> simp [readFrame,dotProduct_add,dotProduct_smul,U,V,dot_self_cross,
      dotProduct_comm (v.val.1.val ⨯₃ v.val.2.1.val) v.val.1.val,
      dotProduct_comm (v.val.1.val ⨯₃ v.val.2.2.val) v.val.1.val,unit]

/-- Determinant of the angular block of a spanning pair in longitude-height coordinates. -/
def angularDet (a b : Params) := a.1.1*b.1.2-a.1.2*b.1.1

/-- Height graph of a plane, obtained by inverting its two-by-two angular block. -/
def resolveGraph (a b : Params) : Tilts :=
  let D := angularDet a b
  ![(b.1.2*a.2.1-a.1.2*b.2.1)/D,(b.1.2*a.2.2-a.1.2*b.2.2)/D,
    (a.1.1*b.2.1-b.1.1*a.2.1)/D,(a.1.1*b.2.2-b.1.1*a.2.2)/D]

private theorem resolve_spec (a b : Params) (hd : angularDet a b ≠ 0) :
    let z := resolveGraph a b
    let x : Params := ((1,0),z 0,z 1)
    let y : Params := ((0,1),z 2,z 3)
    a.1.1 • x + a.1.2 • y = a ∧ b.1.1 • x + b.1.2 • y = b := by
  constructor <;> ext <;> simp [resolveGraph] <;> field_simp [hd] <;> unfold angularDet <;> ring

private def pairCoords (v : FlatLocus.Representative) (w : TangentPair) : Params × Params :=
  let coord := readFrame v.val.1.val v.val.2.1.val v.val.2.2.val
  (coord (ambientVelocityL w.point w.first),coord (ambientVelocityL w.point w.second))

/-- Exact change of basis for every metric and both spanning vectors of a
plane at the moving base point. -/
theorem curvature_in_resolved_graph (v : FlatLocus.Representative) (w : TangentPair)
    (base : w.point = (coreChart v).symm 0)
    (hd : angularDet (pairCoords v w).1 (pairCoords v w).2 ≠ 0) (g : SmoothMetric) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    let d := pairCoords v w
    let z := resolveGraph d.1 d.2
    curvatureNumerator g w.point w.first w.second = (angularDet d.1 d.2)^2 *
      curvatureNumerator g p (field r s ((1,0),z 0,z 1) p) (field r s ((0,1),z 2,z 3) p) := by
  obtain ⟨bp,X,Y⟩ := w
  dsimp only at base
  subst bp
  intro r s p d z
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target (JetChart.center v).1)
  have back (u : Tangent p) : readFrame v.val.1.val v.val.2.1.val v.val.2.2.val (ambientVelocityL p u) = L.symm u := by
    have q := readFrame_field v (L.symm u)
    change readFrame _ _ _ (ambientVelocityL p (field r s (L.symm u) p)) = _ at q
    rwa [←hL,L.apply_symm_apply] at q
  have hx : L d.1 = X := (congrArg L (back X)).trans (L.apply_symm_apply X)
  have hy : L d.2 = Y := (congrArg L (back Y)).trans (L.apply_symm_apply Y)
  let a : Params := ((1,0),z 0,z 1)
  let b : Params := ((0,1),z 2,z 3)
  obtain ⟨ax,by'⟩ := resolve_spec d.1 d.2 hd
  have left : d.1.1.1 • L a+d.1.1.2 • L b=X := by
    rw [← L.map_smul,← L.map_smul,← L.map_add,ax,hx]
  have right : d.2.1.1 • L a+d.2.1.2 • L b=Y := by
    rw [← L.map_smul,← L.map_smul,← L.map_add,by',hy]
  have K := curvatureNumerator_basis_change g p (L a) (L b) d.1.1.1 d.1.1.2 d.2.1.1 d.2.1.2
  rw [left,right,hL a,hL b] at K
  exact K

/-- The compact transverse chart in longitude basis, read against the instantaneous great circle. -/
def transverseCoordinates (v : FlatLocus.Representative) (t : ℝ) (z : Tilts) : Params × Params :=
  let w := longitudePair t ((compactNormalChart t).frame (rawCore v,z))
  let D := frameData w
  let n := movingNormal v (z 2)
  let read := readFrame n D.1.1 D.1.2
  (read D.2.1,read D.2.2)

theorem transverseCoordinates_zero (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) :
    transverseCoordinates v t 0 = (((1,0),0),((0,1),0)) := by
  unfold transverseCoordinates
  dsimp only
  have eq := longitudePair_core v t ht
  rw [eq]
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (chart r s).symm 0
  have base : ambientPoint p = (v.val.2.1.val,v.val.2.2.val) := by
    rw [show p = _ from (JetChart.center v).2]; rfl
  change (readFrame (movingNormal v 0) (ambientPoint p).1 (ambientPoint p).2 _,
    readFrame (movingNormal v 0) (ambientPoint p).1 (ambientPoint p).2 _) = _
  rw [movingNormal_zero,base]
  exact Prod.ext (readFrame_field v ((1,0),0)) (readFrame_field v ((0,1),0))

/-- The base of the compact chart is the center of the new longitude-height chart at the displaced sphere pair. -/
private theorem movingBase (v : FlatLocus.Representative) (t : ℝ) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (z : Tilts) (hz : ∀ i, |z i|<1) :
    let u := movingRepresentative v reg (z 2) (hz 2)
    ((compactNormalChart t).frame (rawCore v,z)).point = (coreChart u).symm 0 := by
  intro u
  rw [show (coreChart u).symm 0 = _ from (JetChart.center u).2]
  have p := congrArg Prod.fst (core_frame_data t v hz)
  change ambientPoint _ = (v.val.2.1.val,point v.val.1.val v.val.2.2.val (z 2)) at p
  exact Prod.ext (Subtype.ext (congrArg (fun x : Cheeger.V => WithLp.toLp 2 x.1) p))
    (Subtype.ext (congrArg (fun x : Cheeger.V => WithLp.toLp 2 x.2) p))

theorem transverseCoordinates_smooth (v : FlatLocus.Representative) (t : ℝ) :
    ContDiffAt ℝ ∞ (transverseCoordinates v t) 0 := by
  let F (z : Tilts) := frameData ((compactNormalChart t).frame (rawCore v,z))
  have data : ContDiffAt ℝ ∞ F 0 :=
    (compact_chart_smooth t (core_fixed v).2 (fun i => by simp : ∀ i, |(0:Tilts) i|<1)).comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  let n (d : Tilts) := movingNormal v (d 2)
  have hn : ContDiffAt ℝ ∞ n 0 := (movingNormal_smooth v (h := 0) (by norm_num)).comp 0 (f := fun z : Tilts => z 2) (by fun_prop)
  have dot_smooth : ContDiff ℝ ∞ (fun x : R3 × R3 => x.1 ⬝ᵥ x.2) := by unfold dotProduct; fun_prop
  let R (z : Tilts) := readFrame (n z) (F z).1.1 (F z).1.2
  have read {W : Tilts → Cheeger.V} (h : ContDiffAt ℝ ∞ W 0) : ContDiffAt ℝ ∞ (fun z => R z (W z)) 0 := by
    let L := (Cheeger.smooth_cross.contDiffAt.comp 0 (hn.prodMk data.fst.fst))
    let M := (Cheeger.smooth_cross.contDiffAt.comp 0 (hn.prodMk data.fst.snd))
    have a := dot_smooth.contDiffAt.comp 0 (L.prodMk h.fst)
    have b := dot_smooth.contDiffAt.comp 0 (M.prodMk h.snd)
    exact (((a.add b).div_const 2).prodMk ((b.sub a).div_const 2)).prodMk
      ((dot_smooth.contDiffAt.comp 0 (hn.prodMk h.fst)).prodMk (dot_smooth.contDiffAt.comp 0 (hn.prodMk h.snd)))
  let a (z : Tilts) := (Profiles.hh t)⁻¹ • (F z).2.1 + (Profiles.hh t)⁻¹ • (F z).2.2
  let b (z : Tilts) := (-1:ℝ) • (F z).2.1 + (F z).2.2
  have lhs := read (((contDiffAt_const (c := (Profiles.hh t)⁻¹)).smul data.snd.fst).add ((contDiffAt_const (c := (Profiles.hh t)⁻¹)).smul data.snd.snd) : ContDiffAt ℝ ∞ a 0)
  have rhs := read (((contDiffAt_const (c := (-1:ℝ))).smul data.snd.fst).add data.snd.snd : ContDiffAt ℝ ∞ b 0)
  have eq : transverseCoordinates v t = fun z => (R z (a z),R z (b z)) := by
    funext z
    let w := (compactNormalChart t).frame (rawCore v,z)
    let V := ambientVelocityL w.point
    let c := (Profiles.hh t)⁻¹
    change (R z (V (c • w.first+c • w.second)),R z (V ((-1:ℝ) • w.first+w.second))) =
      (R z (c • V w.first+c • V w.second),R z ((-1:ℝ) • V w.first+V w.second))
    rw [V.map_add,V.map_add,V.map_smul,V.map_smul,V.map_smul]
  rw [eq]
  exact lhs.prodMk rhs


def transverseDet (v : FlatLocus.Representative) (t : ℝ) (z : Tilts) :=
  let c := transverseCoordinates v t z
  angularDet c.1 c.2

def transverseGraph (v : FlatLocus.Representative) (t : ℝ) (z : Tilts) :=
  let c := transverseCoordinates v t z
  resolveGraph c.1 c.2

theorem transverseGraph_at_core (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) :
    transverseDet v t 0=1 ∧ transverseGraph v t 0=0 := by
  unfold transverseDet transverseGraph
  rw [transverseCoordinates_zero v t ht]
  constructor
  · norm_num [angularDet]
  · ext i; fin_cases i <;> norm_num [resolveGraph]

theorem transverseGraph_smooth (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) :
    ContDiffAt ℝ ∞ (transverseDet v t) 0 ∧ ContDiffAt ℝ ∞ (transverseGraph v t) 0 := by
  have c := transverseCoordinates_smooth v t
  have det : ContDiffAt ℝ ∞ (transverseDet v t) 0 :=
    (c.fst.fst.fst.mul c.snd.fst.snd).sub (c.fst.fst.snd.mul c.snd.fst.fst)
  have nz : transverseDet v t 0 ≠ 0 := (transverseGraph_at_core v t ht).1.trans_ne one_ne_zero
  refine ⟨det,contDiffAt_pi.mpr (fun i => ?_)⟩
  fin_cases i
  · exact ((c.snd.fst.snd.mul c.fst.snd.fst).sub (c.fst.fst.snd.mul c.snd.snd.fst)).div det nz
  · exact ((c.snd.fst.snd.mul c.fst.snd.snd).sub (c.fst.fst.snd.mul c.snd.snd.snd)).div det nz
  · exact ((c.fst.fst.fst.mul c.snd.snd.fst).sub (c.snd.fst.fst.mul c.fst.snd.fst)).div det nz
  · exact ((c.fst.fst.fst.mul c.snd.snd.snd).sub (c.snd.fst.fst.mul c.fst.snd.snd)).div det nz

/-- Every nearby plane of the compact transverse disk over a regular core is an
actual graph at the displaced base point. The positive determinant factor is smooth and equals one at the core. -/
theorem regular_transition (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) :
    ∀ᶠ z in 𝓝 (0:Tilts), ∃ hz : |z 2|<1,
      let u := movingRepresentative v reg (z 2) hz
      let r := align _ _ u.property.1
      let s := align _ _ u.property.2
      let p := (chart r s).symm 0
      let w := longitudePair t ((compactNormalChart t).frame (rawCore v,z))
      let speed := transverseGraph v t z
      w.point=p ∧ 0<transverseDet v t z ∧ ∀ g : SmoothMetric,
        curvatureNumerator g w.point w.first w.second = (transverseDet v t z)^2 *
          curvatureNumerator g p (field r s ((1,0),speed 0,speed 1) p) (field r s ((0,1),speed 2,speed 3) p) := by
  have det := (transverseGraph_smooth v t ht).1.continuousAt.eventually_const_lt
    (show 0<transverseDet v t 0 by rw [(transverseGraph_at_core v t ht).1]; norm_num)
  have near : ∀ᶠ z in 𝓝 (0:Tilts), ∀ i, |z i|<1 := by
    apply (eventually_all.mpr (fun i => ?_))
    exact ((continuous_apply i).abs.continuousAt.eventually_lt_const (by simp))
  filter_upwards [det,near] with z pos hz
  refine ⟨hz 2,?_⟩
  intro u r s p w speed
  have base : w.point=p := movingBase v t reg z hz
  have back : pairCoords u w = transverseCoordinates v t z := by
    have co := congrArg Prod.fst (core_frame_data t v hz)
    change ambientPoint w.point = (v.val.2.1.val,point v.val.1.val v.val.2.2.val (z 2)) at co
    change _ = (readFrame _ (ambientPoint w.point).1 (ambientPoint w.point).2 _,readFrame _ (ambientPoint w.point).1 (ambientPoint w.point).2 _)
    rw [co]; rfl
  refine ⟨base,pos,fun g => ?_⟩
  have hd : angularDet (pairCoords u w).1 (pairCoords u w).2 ≠ 0 := by rw [back]; exact pos.ne'
  have eq := curvature_in_resolved_graph u w base hd g
  dsimp only at eq
  rw [back] at eq
  exact eq


theorem movingRepresentative_regular (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) {h : ℝ} (hr : |h|<1) :
    rangeFactorization FlatLocus.forgetOrientation (movingRepresentative v reg h hr) ∈ FlatLocus.regular := by
  let n := v.val.1.val
  let p := v.val.2.1.val
  let q := v.val.2.2.val
  let L := n ⨯₃ p
  have nonzero := separation_ne v reg
  have nz : L ⬝ᵥ point n q h ≠ 0 := by
    change L ⬝ᵥ (sqrt (1-h^2) • q + h • n) ≠ 0
    rw [dotProduct_add,dotProduct_smul,dotProduct_smul,show L ⬝ᵥ n=0 from (dotProduct_comm ..).trans (dot_self_cross ..)]
    simp only [smul_eq_mul,mul_zero,add_zero]
    change sqrt (1-h^2) * signedSeparation v ≠ 0
    exact mul_ne_zero (sqrt_pos.mpr (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one ..).mpr hr))).ne' nonzero
  have perp : L ⬝ᵥ p=0 := cross_dot_right ..
  change point n q h ≠ p ∧ point n q h ≠ -p
  exact ⟨fun e => nz (e ▸ perp),fun e => nz (by rw [e,dotProduct_neg,perp,neg_zero])⟩

theorem movingRepresentative_zero (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) :
    movingRepresentative v reg 0 (by norm_num) = v := by
  apply Subtype.ext
  refine Prod.ext (Subtype.ext (movingNormal_zero v)) (Prod.ext rfl (Subtype.ext ?_))
  change sqrt (1-(0:ℝ)^2) • v.val.2.2.val+(0:ℝ) • v.val.1.val=v.val.2.2.val
  simp


/-- Actual base representative on the open height chart, extended by its center outside the chart. -/
def regularBase (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (h : ℝ) := if hr : |h|<1 then movingRepresentative v reg h hr else v

/-- Pointwise finite calculation along the moving-base ray in the compact transverse chart. -/
def transverseRaw (v : FlatLocus.Representative) (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (a : Tilts) (h : ℝ) :=
  let z := h • a
  let base := regularBase v reg (z 2)
  let T := gramPolys base t ht
  let tilt := transverseGraph v t z
  let U : Params := ((1,0),tilt 0,tilt 1)
  let V : Params := ((0,1),tilt 2,tilt 3)
  (transverseDet v t z)^2*((chartPolynomial T U V).eval h/(T 0 0).det.eval h)

/-- Every uncorrected coefficient of the compact transverse chart is obtained from
the actual moving-base path, with its varying Gram determinant and both moving spanning vectors. -/
theorem transverse_coeff_eq_chart (v : FlatLocus.Representative)
    (reg : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0≤t) (a : Tilts) (n : ℕ) :
    let F := (compactNormalChart t).curvature (paperCoefficients t ht 0)
    UniformTube.coeff F n (rawCore v) a =
      (Profiles.hh t)^2/4 * (iteratedDeriv n (transverseRaw v reg t ht a) 0 / n.factorial) := by
  intro F
  let c := compactNormalChart t
  let A := paperCoefficients t ht 0
  let f (h : ℝ) := (longitudePair t (c.frame (rawCore v,h • a))).numerator A h
  have path : Tendsto (fun h : ℝ => h • a) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun h : ℝ => h • a) := continuous_id.smul continuous_const
    simpa only [zero_smul] using h.continuousAt.tendsto (x := (0:ℝ))
  have eq : f =ᶠ[𝓝 0] transverseRaw v reg t ht a := by
    filter_upwards [path.eventually (regular_transition v t ht reg),paper_metrics_realize t ht (0:Scalar)] with h step real
    obtain ⟨hz,_,_,K⟩ := step
    obtain ⟨g,hg⟩ := real
    let z := h • a
    let u := movingRepresentative v reg (z 2) hz
    let sp := transverseGraph v t z
    have cur := curvature_eq_chartPolynomial u t ht hg ((1,0),sp 0,sp 1) ((0,1),sp 2,sp 3)
    dsimp only at cur
    change (longitudePair t (c.frame (rawCore v,z))).numerator A h = _
    rw [TangentPair.numerator_eq _ hg,K g,cur]
    simp only [transverseRaw,regularBase,dite_eq_left hz]
    rfl
  have scale := longitudePair_coeff t ht 0 (rawCore v) a n
  change UniformTube.coeff F n (rawCore v) a = (Profiles.hh t)^2/4*(iteratedDeriv n f 0/n.factorial) at scale
  rw [scale,eq.iteratedDeriv_eq (n := n)]


end
end LocalHopf.BackgroundGrowth.Transverse
