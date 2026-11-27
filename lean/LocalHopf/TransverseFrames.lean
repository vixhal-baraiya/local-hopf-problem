import LocalHopf.FlatFrameEstimate
import LocalHopf.JetChart

/-! Transverse directions at a common-normal mixed plane. The two base points
may coincide or be antipodal. Height moves the second base point and the other
three coordinates vary the two-plane. -/
namespace LocalHopf.BackgroundGrowth.Transverse
open Matrix Real
noncomputable section

private def radius (x : ℝ) := sqrt (1-x^2)
private theorem radius_sq {x : ℝ} (hx : |x| ≤ 1) : radius x^2 = 1-x^2 :=
  sq_sqrt (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr hx))

/-- Tilt the second point off the core great circle. -/
def point (n q : R3) (h : ℝ) := radius h • q + h • n

/-- Rotate its normal within the new tangent plane, with signed sine k. -/
def normal (n q : R3) (h k : ℝ) :=
  radius k • (radius h • n - h • q) + k • (n ⨯₃ q)

/-- Adapted round-orthonormal frame with the two small components a,b. -/
def frame (p q n m : R3) (a b : ℝ) : (R3 × R3) × (R3 × R3) :=
  ((radius b • (n ⨯₃ p), b • m),(a • n, radius a • (m ⨯₃ q)))

theorem transverse_axes {n q : R3} (hn : n ⬝ᵥ n = 1) (hq : q ⬝ᵥ q = 1) (hnq : n ⬝ᵥ q = 0)
    {h k : ℝ} (hh : |h| ≤ 1) (hk : |k| ≤ 1) :
    let Q := point n q h
    let M := normal n q h k
    Q ⬝ᵥ Q = 1 ∧ M ⬝ᵥ M = 1 ∧ M ⬝ᵥ Q = 0 ∧ n ⬝ᵥ M = radius h*radius k := by
  have hqn := (dotProduct_comm q n).trans hnq
  have L := (cross_unit n q hn hq hnq).1
  have nL := dot_self_cross n q
  have qL := dot_cross_self n q
  have Ln := (dotProduct_comm _ n).trans nL
  have Lq := (dotProduct_comm _ q).trans qL
  simp only [point,normal,add_dotProduct,dotProduct_add,sub_dotProduct,dotProduct_sub,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,hn,hq,hnq,hqn,L,nL,qL,Ln,Lq]
  constructor
  · linear_combination radius_sq hh
  constructor
  · linear_combination (radius k)^2 * radius_sq hh + radius_sq hk
  exact ⟨by ring,by ring⟩

theorem adapted {p q n m : R3} (hp : p ⬝ᵥ p = 1) (hq : q ⬝ᵥ q = 1)
    (hn : n ⬝ᵥ n = 1) (hm : m ⬝ᵥ m = 1) (hnp : n ⬝ᵥ p = 0) (hmq : m ⬝ᵥ q = 0)
    {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    let (X,Y) := frame p q n m a b
    gprod X X = 1 ∧ gprod Y Y = 1 ∧ X.1 ⬝ᵥ Y.1 = 0 ∧ X.2 ⬝ᵥ Y.2 = 0 := by
  have nx := dot_self_cross n p
  have xn := (dotProduct_comm _ n).trans nx
  have my := dot_self_cross m q
  simp only [frame,gprod,smul_dotProduct,dotProduct_smul,smul_eq_mul,hn,hm,
    (cross_unit n p hn hp hnp).1,(cross_unit m q hm hq hmq).1,xn,my]
  exact ⟨by linear_combination radius_sq hb,by linear_combination radius_sq ha,by ring,by ring⟩

private theorem scale_sq (c : ℝ) (x : R3) : sqLength (c • x) = c^2*sqLength x := by
  simp [sqLength,smul_dotProduct,dotProduct_smul,sq,mul_assoc]

/-- Quadratic growth of the algebraic lower side of (Z) on a single uniform
transverse disk about every incidence representative. -/
theorem growth (v : FlatLocus.Representative) {t : ℝ} (ht : 0 < t) {a b h k : ℝ}
    (ha : |a| ≤ 1/2) (hb : |b| ≤ 1/2) (hh : |h| ≤ 1) (hk : |k| ≤ 1) :
    let n := v.val.1.val
    let p := v.val.2.1.val
    let q := point n v.val.2.2.val h
    let m := normal n v.val.2.2.val h k
    let (X,Y) := frame p q n m a b
    a^2+b^2+h^2+k^2 ≤ (66+32/t^3)*zillerLower p q t X Y := by
  let n := v.val.1.val
  let p := v.val.2.1.val
  let q₀ := v.val.2.2.val
  let q := point n q₀ h
  let m := normal n q₀ h k
  let X := (frame p q n m a b).1
  let Y := (frame p q n m a b).2
  change _ ≤ _ * zillerLower p q t X Y
  have bound {x : ℝ} (hx : |x| ≤ 1/2) : |x| ≤ 1 := hx.trans (by norm_num)
  have quarter {x : ℝ} (hx : |x| ≤ 1/2) : x^2 ≤ 1/4 := by
    have s := abs_le.mp hx
    nlinarith [mul_nonneg (sub_nonneg.mpr s.2) (show 0 ≤ 1/2+x by linarith [s.1])]
  have hn : n ⬝ᵥ n = 1 := v.val.1.property
  have hp : p ⬝ᵥ p = 1 := v.val.2.1.property
  have pn : n ⬝ᵥ p = 0 := v.property.1
  obtain ⟨hq,hm,mq,nm⟩ := transverse_axes hn v.val.2.2.property v.property.2 hh hk
  change q ⬝ᵥ q = 1 at hq; change m ⬝ᵥ m = 1 at hm; change m ⬝ᵥ q = 0 at mq
  change n ⬝ᵥ m = _ at nm
  obtain ⟨ux,uy,orth₁,orth₂⟩ := adapted hp hq hn hm pn mq (bound ha) (bound hb)
  change gprod X X = 1 at ux; change gprod Y Y = 1 at uy
  have sqn : sqLength (n ⨯₃ m) = h^2+(1-h^2)*k^2 := by
    rw [sqLength,cross_dot_cross,hn,hm,dotProduct_comm m n,nm]
    nlinarith only [radius_sq hk,radius_sq hh,
      congrArg (fun x : ℝ => x * (radius k)^2) (radius_sq hh),
      congrArg (fun x : ℝ => (1-h^2)*x) (radius_sq hk)]
  have undo (l s : R3) (hs : s ⬝ᵥ s = 1) (ls : l ⬝ᵥ s = 0) : s ⨯₃ (l ⨯₃ s) = l := by
    rw [cross_cross_eq_smul_sub_smul',hs,ls,one_smul,zero_smul,sub_zero]
  have ex : p ⨯₃ X.1 = radius b • n := by change p ⨯₃ (radius b • _) = _; rw [map_smul,undo n p hp pn]
  have ey : q ⨯₃ Y.2 = radius a • m := by change q ⨯₃ (radius a • _) = _; rw [map_smul,undo m q hq mq]
  have comp := normal_comparison p q X Y hp hq ux uy
  rw [ex,ey] at comp
  simp only [map_smul,LinearMap.smul_apply,scale_sq] at comp
  have ax : sqLength Y.1 = a^2 := by change sqLength (a • n) = _; rw [scale_sq,show sqLength n = 1 from hn,mul_one]
  have bx : sqLength X.2 = b^2 := by change sqLength (b • m) = _; rw [scale_sq,show sqLength m = 1 from hm,mul_one]
  rw [ax,bx] at comp
  have area : sqLength (X.1 ⨯₃ Y.1) + sqLength (X.2 ⨯₃ Y.2) =
      (1-b^2)*a^2 + b^2*(1-a^2) := by
    have xu := (cross_unit n p hn hp pn).1
    have yu := (cross_unit m q hm hq mq).1
    change sqLength ((radius b • (n ⨯₃ p)) ⨯₃ (a • n)) + sqLength ((b • m) ⨯₃ (radius a • (m ⨯₃ q))) = _
    have x₁ : sqLength ((n ⨯₃ p) ⨯₃ n) = 1 := by
      rw [sqLength,cross_dot_cross,xu,hn,dot_self_cross,mul_zero,sub_zero,mul_one]
    have y₂ : sqLength (m ⨯₃ (m ⨯₃ q)) = 1 := by
      rw [sqLength,cross_dot_cross,yu,hm,dot_self_cross,zero_mul,sub_zero,mul_one]
    simp only [map_smul,LinearMap.smul_apply,scale_sq,x₁,y₂,radius_sq (bound ha),radius_sq (bound hb)]
    ring
  let ν := zillerLower p q t X Y
  let B := sqLength (moment p q X ⨯₃ moment p q Y)
  have eq : ν = (1-b^2)*a^2+b^2*(1-a^2)+t^3/4*B := by dsimp only [ν,zillerLower,B]; rw [area]
  have hab : a^2+b^2 ≤ 2*ν := by
    nlinarith only [eq,mul_nonneg (show 0 ≤ 1/2-b^2 by linarith [quarter hb]) (sq_nonneg a),
      mul_nonneg (sq_nonneg b) (show 0 ≤ 1/2-a^2 by linarith [quarter ha]),
      mul_nonneg (pow_pos ht 3).le (sqLength_nonneg (moment p q X ⨯₃ moment p q Y))]
  have hB : B ≤ 4*ν/t^3 := by
    apply (le_div_iff₀ (pow_pos ht 3)).mpr
    nlinarith only [eq,mul_nonneg (show 0 ≤ 1-b^2 by linarith [quarter hb]) (sq_nonneg a),
      mul_nonneg (sq_nonneg b) (show 0 ≤ 1-a^2 by linarith [quarter ha])]
  have prod : 1/2 ≤ (radius a)^2*(radius b)^2 := by
    rw [radius_sq (bound ha),radius_sq (bound hb)]
    nlinarith [quarter ha,quarter hb,mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  have hnm := mul_le_mul_of_nonneg_right prod (sqLength_nonneg (n ⨯₃ m))
  have hs : (h^2+k^2)/2 ≤ sqLength (n ⨯₃ m) := by
    rw [sqn]
    nlinarith only [mul_nonneg (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr hh)) (sq_nonneg k),
      mul_nonneg (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr hk)) (sq_nonneg h)]
  change _ ≤ (66+32/t^3)*ν
  change _ ≤ 2*B+4*a^2+8*b^2 at comp
  rw [add_mul,div_mul_eq_mul_div]
  have hc : (h^2+k^2)/4 ≤ 2*B+4*a^2+8*b^2 := calc
    _ ≤ 1/2 * sqLength (n ⨯₃ m) := by linarith only [hs]
    _ ≤ _ := hnm.trans (by simpa only [mul_assoc] using comp)
  calc
    _ ≤ 66*ν + 8*B := by linarith only [hc,hab,sq_nonneg a]
    _ ≤ _ := by rw [show 32*ν/t^3=8*(4*ν/t^3) by ring]; linarith only [hB]


private theorem decompose (n q : FlatLocus.UnitVector) (hnq : n.val ⬝ᵥ q.val = 0) (x : R3) :
    x = (x ⬝ᵥ q.val) • q.val + (x ⬝ᵥ (n.val ⨯₃ q.val)) • (n.val ⨯₃ q.val) + (x ⬝ᵥ n.val) • n.val := by
  let b := SphereProduct.JetChart.axesBasis n q hnq
  have eq (i : Fin 3) : b i = SphereProduct.JetChart.axes n q i :=
    (b.repr_symm_single i).symm.trans (SphereProduct.JetChart.axesBasis_apply n q hnq i)
  have e := congrArg (fun y : SphereProduct.E3 => y.ofLp) (b.sum_repr' (WithLp.toLp 2 x))
  simpa [Fin.sum_univ_three,eq,SphereProduct.JetChart.axes,EuclideanSpace.inner_eq_star_dotProduct] using e.symm

/-- Recover the core great circle point and both normal coordinates from a
second sphere point and its oriented unit normal. This includes p₂ = ±p₁;
only the relative orientation of the two normals enters the inverse. -/
theorem recover (n Q M : FlatLocus.UnitVector) (hMQ : M.val ⬝ᵥ Q.val = 0) (hpos : 0 < n.val ⬝ᵥ M.val) :
    ∃ (q : FlatLocus.UnitVector) (h k : ℝ), n.val ⬝ᵥ q.val = 0 ∧ |h| < 1 ∧ |k| < 1 ∧
      point n.val q.val h = Q.val ∧ normal n.val q.val h k = M.val ∧
      h^2 ≤ 1-(n.val ⬝ᵥ M.val)^2 ∧ k^2 ≤ 1-(n.val ⬝ᵥ M.val)^2 := by
  let h := n.val ⬝ᵥ Q.val
  let j := n.val ⬝ᵥ M.val
  have hn : n.val ⬝ᵥ n.val = 1 := n.property
  have hQ : Q.val ⬝ᵥ Q.val = 1 := Q.property
  have hM : M.val ⬝ᵥ M.val = 1 := M.property
  have bound : h^2+j^2 ≤ 1 := by
    have H := sqLength_nonneg (n.val-h • Q.val-j • M.val)
    simp only [sqLength,sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul,
      smul_eq_mul,hn,hQ,hM,hMQ,dotProduct_comm Q.val M.val,dotProduct_comm Q.val n.val,
      dotProduct_comm M.val n.val] at H
    dsimp [h,j] at H ⊢
    nlinarith only [H]
  have hlt : |h| < 1 := (sq_lt_one_iff_abs_lt_one _).mp (by nlinarith [sq_pos_of_pos hpos])
  let R := radius h
  have hR : 0 < R := sqrt_pos.mpr (by nlinarith [(sq_lt_one_iff_abs_lt_one _).mpr hlt])
  have eR : R^2 = 1-h^2 := radius_sq hlt.le
  let qv := R⁻¹ • (Q.val-h • n.val)
  have qnorm : qv ⬝ᵥ qv = 1 := by
    simp only [qv,smul_dotProduct,dotProduct_smul,smul_eq_mul,sub_dotProduct,dotProduct_sub,
      hQ,hn,dotProduct_comm Q.val n.val]
    change R⁻¹*(R⁻¹*(1-h*h)-h*(R⁻¹*(h-h*1))) = 1
    field_simp [hR.ne']; nlinarith
  let q : FlatLocus.UnitVector := ⟨qv,qnorm⟩
  have nq : n.val ⬝ᵥ q.val = 0 := by
    change n.val ⬝ᵥ (R⁻¹ • (Q.val-h • n.val)) = 0
    simp [dotProduct_smul,dotProduct_sub,hn,h]
  have point_eq : point n.val q.val h = Q.val := by
    change R • (R⁻¹ • (Q.val-h • n.val)) + h • n.val = _
    rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul,sub_add_cancel]
  let T := n.val ⨯₃ q.val
  let k := M.val ⬝ᵥ T
  let c := j/R
  have cp : 0 < c := div_pos hpos hR
  have rc : R*c=j := mul_div_cancel₀ j hR.ne'
  have mq : M.val ⬝ᵥ q.val = -h*c := by
    change M.val ⬝ᵥ (R⁻¹ • (Q.val-h • n.val)) = _
    simp only [dotProduct_smul,dotProduct_sub,smul_eq_mul,hMQ,zero_sub,dotProduct_comm M.val n.val]
    change R⁻¹ * -(h*j) = -h*(j/R)
    ring
  have eq : M.val = c • (R • n.val - h • q.val) + k • T := by
    calc
      _ = (-h*c) • q.val + k • T + j • n.val := by
        simpa only [mq,dotProduct_comm M.val n.val] using decompose n q nq M.val
      _ = _ := by rw [← rc]; module
  have kt : T ⬝ᵥ T = 1 := (cross_unit n.val q.val hn qnorm nq).1
  have orth : (R • n.val - h • q.val) ⬝ᵥ T = 0 := by
    simp [T,sub_dotProduct,smul_dotProduct,dot_self_cross,dot_cross_self]
  have nn : (R • n.val-h • q.val) ⬝ᵥ (R • n.val-h • q.val) = 1 := by
    have qq : q.val ⬝ᵥ q.val = 1 := q.property
    simp only [sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul,hn,qq,nq,
      dotProduct_comm q.val n.val]
    nlinarith only [eR]
  have norm_eq := hM
  rw [eq] at norm_eq
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    kt,nn,orth,dotProduct_comm T (R • n.val-h • q.val)] at norm_eq
  have cs : c^2+k^2=1 := by nlinarith only [norm_eq]
  have hk : |k| < 1 := (sq_lt_one_iff_abs_lt_one _).mp (by nlinarith [sq_pos_of_pos cp])
  have ce : radius k = c := by
    unfold radius
    rw [show 1-k^2=c^2 by linarith, sqrt_sq cp.le]
  refine ⟨q,h,k,nq,hlt,hk,point_eq,?_,by change _ ≤ 1-j^2; linarith,?_⟩
  · change radius k • (R • n.val-h • q.val)+k • T = M.val
    rw [ce,← eq]
  · change _ ≤ 1-j^2
    rw [← rc, mul_pow, eR]
    nlinarith only [cs,mul_nonneg (sq_nonneg h) (sq_nonneg c)]



private theorem factor_axis (P : FlatLocus.UnitVector) {x y : R3} (hx : 0 < sqLength x)
    (px : P.val ⬝ᵥ x = 0) (py : P.val ⬝ᵥ y = 0) (xy : x ⬝ᵥ y = 0) :
    ∃ n : FlatLocus.UnitVector, n.val ⬝ᵥ P.val = 0 ∧
      x = sqrt (sqLength x) • (n.val ⨯₃ P.val) ∧ y = (y ⬝ᵥ n.val) • n.val ∧
      P.val ⨯₃ x = sqrt (sqLength x) • n.val := by
  let r := sqrt (sqLength x)
  have hr : 0 < r := sqrt_pos.mpr hx
  have rr : r^2 = x ⬝ᵥ x := sq_sqrt hx.le
  have pp : P.val ⬝ᵥ P.val = 1 := P.property
  let u := r⁻¹ • x
  have pu : P.val ⬝ᵥ u = 0 := by simp [u,dotProduct_smul,px]
  have uu : u ⬝ᵥ u = 1 := by
    simp only [u,smul_dotProduct,dotProduct_smul,smul_eq_mul,← rr]
    field_simp [hr.ne']
  let n : FlatLocus.UnitVector := ⟨P.val ⨯₃ u, (cross_unit P.val u pp uu pu).1⟩
  have np : n.val ⬝ᵥ P.val = 0 := (dotProduct_comm _ _).trans (dot_self_cross _ _)
  have undo : n.val ⨯₃ P.val = u := by
    change ((P.val ⨯₃ u) ⨯₃ P.val) = u
    rw [cross_cross_eq_smul_sub_smul,pp,dotProduct_comm u P.val,pu,one_smul,zero_smul,sub_zero]
  have xu : x = r • u := by simp [u,smul_smul,hr.ne']
  have uy : y ⬝ᵥ u = 0 := by simp [u,dotProduct_smul,dotProduct_comm y x,xy]
  refine ⟨n,np,undo.symm ▸ xu,?_,?_⟩
  · simpa only [undo,uy,dotProduct_comm y P.val,py,zero_smul,zero_add] using decompose n P np y
  · conv_lhs => rw [xu]
    rw [map_smul]

/-- Invert the transverse parametrization on a round-orthonormal adapted
frame after choosing the orientations of its two dominant factor lines. -/
theorem covers_adapted (P Q : FlatLocus.UnitVector) (X Y : R3 × R3)
    (xunit : gprod X X = 1) (yunit : gprod Y Y = 1)
    (px : P.val ⬝ᵥ X.1 = 0) (py : P.val ⬝ᵥ Y.1 = 0)
    (qx : Q.val ⬝ᵥ X.2 = 0) (qy : Q.val ⬝ᵥ Y.2 = 0)
    (o₁ : X.1 ⬝ᵥ Y.1 = 0) (o₂ : X.2 ⬝ᵥ Y.2 = 0)
    (aligned : 0 < (P.val ⨯₃ X.1) ⬝ᵥ (Q.val ⨯₃ Y.2)) :
    ∃ (v : FlatLocus.Representative) (a b h k : ℝ), v.val.2.1 = P ∧
      |a| < 1 ∧ |b| < 1 ∧ |h| < 1 ∧ |k| < 1 ∧
      a^2 = sqLength Y.1 ∧ b^2 = sqLength X.2 ∧ point v.val.1.val v.val.2.2.val h = Q.val ∧
      frame P.val Q.val v.val.1.val (normal v.val.1.val v.val.2.2.val h k) a b = (X,Y) := by
  have hx : 0 < sqLength X.1 := by
    by_contra! neg
    have e := dotProduct_self_eq_zero.mp (le_antisymm neg (sqLength_nonneg _))
    simp [e] at aligned
  have hy : 0 < sqLength Y.2 := by
    by_contra! neg
    have e := dotProduct_self_eq_zero.mp (le_antisymm neg (sqLength_nonneg _))
    simp [e] at aligned
  obtain ⟨n,np,X₁,Y₁,pX⟩ := factor_axis P hx px py o₁
  obtain ⟨m,mq,Y₂,X₂,qY⟩ := factor_axis Q hy qy qx ((dotProduct_comm _ _).trans o₂)
  have nm : 0 < n.val ⬝ᵥ m.val := by
    rw [pX,qY,smul_dotProduct,dotProduct_smul] at aligned
    change 0 < sqrt (sqLength X.1) * (sqrt (sqLength Y.2)*(n.val ⬝ᵥ m.val)) at aligned
    exact pos_of_mul_pos_right (pos_of_mul_pos_right aligned (sqrt_nonneg _)) (sqrt_nonneg _)
  obtain ⟨q,h,k,nq,hh,hk,poin,norm,_,_⟩ := recover n Q m mq nm
  let a := Y.1 ⬝ᵥ n.val
  let b := X.2 ⬝ᵥ m.val
  have sy : sqLength Y.1 = a^2 := by
    conv_lhs => rw [Y₁]
    rw [scale_sq,show sqLength n.val = 1 from n.property,mul_one]
  have sx : sqLength X.2 = b^2 := by
    conv_lhs => rw [X₂]
    rw [scale_sq,show sqLength m.val = 1 from m.property,mul_one]
  change sqLength X.1+sqLength X.2=1 at xunit
  change sqLength Y.1+sqLength Y.2=1 at yunit
  rw [sx] at xunit; rw [sy] at yunit
  let v : FlatLocus.Representative := ⟨(n,P,q),np,nq⟩
  refine ⟨v,a,b,h,k,rfl,(sq_lt_one_iff_abs_lt_one _).mp (by linarith),
    (sq_lt_one_iff_abs_lt_one _).mp (by linarith),hh,hk,sy.symm,sx.symm,poin,?_⟩
  change frame P.val Q.val n.val (normal n.val q.val h k) a b = (X,Y)
  rw [norm]
  have ra : radius a = sqrt (sqLength Y.2) := by rw [radius,show 1-a^2 = sqLength Y.2 by linarith]
  have rb : radius b = sqrt (sqLength X.1) := by rw [radius,show 1-b^2 = sqLength X.1 by linarith]
  unfold frame
  rw [ra, rb]
  exact Prod.ext (Prod.ext X₁.symm X₂.symm) (Prod.ext Y₁.symm Y₂.symm)



/-- Every tangent plane of sufficiently small algebraic penalty, at any base
pair, has an orthonormal basis in the same uniform transverse four-disk. -/
theorem covers_small (P Q : FlatLocus.UnitVector) {t : ℝ} (ht : 0 < t) (X Y : R3 × R3)
    (hx : gprod X X = 1) (hy : gprod Y Y = 1) (hxy : gprod X Y = 0)
    (px : P.val ⬝ᵥ X.1 = 0) (py : P.val ⬝ᵥ Y.1 = 0)
    (qx : Q.val ⬝ᵥ X.2 = 0) (qy : Q.val ⬝ᵥ Y.2 = 0)
    (small : (66+32/t^3)*zillerLower P.val Q.val t X Y ≤ 1/4) :
    ∃ (θ : ℝ) (U V : R3 × R3) (e : ℝ) (v : FlatLocus.Representative) (a b h k : ℝ),
      ((U,V) = rotatePair X Y θ ∨ (V,U) = rotatePair X Y θ) ∧ e^2 = 1 ∧ v.val.2.1 = P ∧
      point v.val.1.val v.val.2.2.val h = Q.val ∧
      frame P.val Q.val v.val.1.val (normal v.val.1.val v.val.2.2.val h k) a b = (U,e • V) ∧
      a^2+b^2+h^2+k^2 ≤ (66+32/t^3)*zillerLower P.val Q.val t X Y := by
  obtain ⟨θ,U,V,rot,o₁,o₂,u,v,pu,pv,qu,qv,eq,comp⟩ :=
    ordered_adapted P.val Q.val t ht.le X Y hx hy hxy px py qx qy
  let ν := zillerLower P.val Q.val t X Y
  let B := sqLength (moment P.val Q.val U ⨯₃ moment P.val Q.val V)
  let N := P.val ⨯₃ U.1
  let M := Q.val ⨯₃ V.2
  have νpos : 0 ≤ ν := by
    dsimp only [ν,zillerLower]
    exact add_nonneg (add_nonneg (sqLength_nonneg _) (sqLength_nonneg _))
      (mul_nonneg (by positivity) (sqLength_nonneg _))
  have Bbound : B*t^3 ≤ 4*ν := by
    change _ = ν at eq
    unfold zillerLower at eq
    dsimp only [B]
    linarith only [eq,sqLength_nonneg (U.1 ⨯₃ V.1),sqLength_nonneg (U.2 ⨯₃ V.2)]
  have bound : 66*ν+32*(ν/t^3) ≤ 1/4 := by
    change (66+32/t^3)*ν ≤ _ at small
    convert small using 1; ring
  have inv : 0 ≤ ν/t^3 := div_nonneg νpos (pow_pos ht 3).le
  have B' : B ≤ 4*(ν/t^3) := by rw [← mul_div_assoc]; exact (le_div_iff₀ (pow_pos ht 3)).mpr Bbound
  change sqLength U.2 + sqLength V.1 ≤ 2*ν at comp
  have ulen : sqLength U.1 + sqLength U.2 = 1 := u
  have vlen : sqLength V.1 + sqLength V.2 = 1 := v
  have hn : sqLength N = sqLength U.1 := by simp [N,sqLength,cross_dot_cross,show P.val ⬝ᵥ P.val = 1 from P.property,pu]
  have hm : sqLength M = sqLength V.2 := by simp [M,sqLength,cross_dot_cross,show Q.val ⬝ᵥ Q.val = 1 from Q.property,qv]
  have nd : N ⬝ᵥ M ≠ 0 := by
    intro zero
    have est := normal_comparison P.val Q.val U V P.property Q.property u v
    change sqLength (N ⨯₃ M) ≤ 2*B+4*sqLength V.1+8*sqLength U.2 at est
    have en : sqLength (N ⨯₃ M) = sqLength U.1*sqLength V.2 := by
      rw [← hn,← hm]
      simp [sqLength,cross_dot_cross,zero]
    rw [en] at est
    have first : (1:ℝ)/2 ≤ sqLength U.1 := by linarith [sqLength_nonneg V.1]
    have second : (1:ℝ)/2 ≤ sqLength V.2 := by linarith [sqLength_nonneg U.2]
    have product := mul_le_mul first second (by norm_num : 0 ≤ (1:ℝ)/2) (sqLength_nonneg _)
    linarith only [product,est,B',comp,bound,νpos,inv,sqLength_nonneg V.1]
  obtain ⟨e,es,aligned⟩ : ∃ e : ℝ, e^2=1 ∧ 0 < e*(N ⬝ᵥ M) := by
    rcases lt_or_gt_of_ne nd with h | h
    · exact ⟨-1,by norm_num,by linarith⟩
    · exact ⟨1,by norm_num,by simpa⟩
  have align : 0 < (P.val ⨯₃ U.1) ⬝ᵥ (Q.val ⨯₃ (e • V).2) := by
    simpa only [Prod.smul_snd,map_smul,dotProduct_smul,smul_eq_mul] using aligned
  have ev : gprod (e • V) (e • V) = 1 := by
    change sqLength (e • V.1)+sqLength (e • V.2)=1
    rw [scale_sq,scale_sq,es]; linarith
  obtain ⟨z,a,b,h,k,zp,_,_,hh,hk,asq,bsq,pt,fr⟩ :=
    covers_adapted P Q U (e • V) u ev pu (by simp [dotProduct_smul,pv]) qu
      (by simp [dotProduct_smul,qv]) (by simp [dotProduct_smul,o₁]) (by simp [dotProduct_smul,o₂]) align
  change a^2 = sqLength (e • V.1) at asq
  rw [scale_sq,es,one_mul] at asq
  have half {r : ℝ} (hr : r^2 ≤ 2*ν) : |r| ≤ 1/2 := by
    rw [abs_le]
    constructor <;> nlinarith only [hr,bound,inv,sq_nonneg (r+1/2),sq_nonneg (r-1/2)]
  have ha : |a| ≤ 1/2 := half (by rw [asq]; linarith [sqLength_nonneg U.2])
  have hb : |b| ≤ 1/2 := half (by rw [bsq]; linarith [sqLength_nonneg V.1])
  have grow := growth z ht ha hb hh.le hk.le
  dsimp only at grow
  rw [zp,pt,fr] at grow
  have scaled : zillerLower P.val Q.val t U (e • V) = zillerLower P.val Q.val t U V := by
    simp [zillerLower,moment,← smul_add,scale_sq,es]
  exact ⟨θ,U,V,e,z,a,b,h,k,rot,es,zp,pt,fr,by simpa only [scaled,eq] using grow⟩


end
end LocalHopf.BackgroundGrowth.Transverse
