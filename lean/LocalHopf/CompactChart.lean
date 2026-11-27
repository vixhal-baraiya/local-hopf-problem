import LocalHopf.CheegerCover
import LocalHopf.FlatTorusJet
import LocalHopf.FrameRegularity

/-! Compact core and Euclidean normal parameters for the common-normal incidence space. -/
namespace LocalHopf.BackgroundGrowth.Transverse
open Matrix Real Set Filter
open scoped ContDiff Topology
noncomputable section

abbrev CoreParameters := R3 × R3 × R3

def rawCore (v : FlatLocus.Representative) : CoreParameters := (v.val.1.val,v.val.2.1.val,v.val.2.2.val)

def coreSet : Set CoreParameters := range rawCore

theorem compact_core : IsCompact coreSet := isCompact_range (by unfold rawCore; fun_prop)

private def unit (u : R3) : R3 := (sqrt (u ⬝ᵥ u))⁻¹ • u
private def perp (n u : R3) : R3 := u - (n ⬝ᵥ u) • n

private theorem unit_self {u : R3} (hu : u ⬝ᵥ u=1) : unit u = u := by simp [unit,hu]
private theorem perp_self {n u : R3} (h : n ⬝ᵥ u=0) : perp n u = u := by simp [perp,h]

/-- Near the incidence set, normalize the axis and project each point onto its
orthogonal plane. This provides an extension in Euclidean core coordinates. -/
def projectCore (x : CoreParameters) : CoreParameters :=
  let n := unit x.1
  (n,unit (perp n x.2.1),unit (perp n x.2.2))

def validCore (x : CoreParameters) : Prop :=
  0 < x.1 ⬝ᵥ x.1 ∧ 0 < sqLength (perp (unit x.1) x.2.1) ∧ 0 < sqLength (perp (unit x.1) x.2.2)

theorem core_fixed (v : FlatLocus.Representative) :
    projectCore (rawCore v) = rawCore v ∧ validCore (rawCore v) := by
  simp only [projectCore,validCore,rawCore,unit_self v.val.1.property,perp_self v.property.1,
    perp_self v.property.2,unit_self v.val.2.1.property,unit_self v.val.2.2.property,
    sqLength]
  have pos (u : FlatLocus.UnitVector) : 0 < u.val ⬝ᵥ u.val := lt_of_lt_of_eq zero_lt_one u.property.symm
  exact ⟨trivial,pos _,pos _,pos _⟩

private theorem dot_smooth : ContDiff ℝ ∞ (fun x : R3 × R3 => x.1 ⬝ᵥ x.2) := by
  simp only [dotProduct,Fin.sum_univ_three]; fun_prop

private theorem unit_smooth {u : R3} (h : 0 < u ⬝ᵥ u) : ContDiffAt ℝ ∞ unit u := by
  have d : ContDiff ℝ ∞ (fun z : R3 => z ⬝ᵥ z) := dot_smooth.comp (contDiff_id.prodMk contDiff_id)
  exact ((d.contDiffAt.sqrt h.ne').inv (sqrt_pos.mpr h).ne').smul contDiffAt_id

private theorem perp_smooth : ContDiff ℝ ∞ (fun x : R3 × R3 => perp x.1 x.2) :=
  contDiff_snd.sub (dot_smooth.smul contDiff_fst)

theorem projectCore_smooth {x : CoreParameters} (h : validCore x) : ContDiffAt ℝ ∞ projectCore x := by
  have n := (unit_smooth h.1).comp x (contDiffAt_fst (n := ∞))
  have p := perp_smooth.contDiffAt.comp x (n.prodMk (contDiffAt_fst.comp x contDiffAt_snd))
  have q := perp_smooth.contDiffAt.comp x (n.prodMk (contDiffAt_snd.comp x contDiffAt_snd))
  have hp : ContDiffAt ℝ ∞ unit (perp (unit x.1) x.2.1) := unit_smooth h.2.1
  have hq : ContDiffAt ℝ ∞ unit (perp (unit x.1) x.2.2) := unit_smooth h.2.2
  have p' : ContDiffAt ℝ ∞ (fun z : CoreParameters => perp (unit z.1) z.2.1) x := p
  have q' : ContDiffAt ℝ ∞ (fun z : CoreParameters => perp (unit z.1) z.2.2) x := q
  have e := hp.comp (f := fun z : CoreParameters => perp (unit z.1) z.2.1) x p'
  have f := hq.comp (f := fun z : CoreParameters => perp (unit z.1) z.2.2) x q'
  exact n.prodMk (e.prodMk f)

theorem validCore_open : IsOpen {x | validCore x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have h : validCore x := hx
  have n := (unit_smooth h.1).comp x (contDiffAt_fst (n := ∞))
  have p := perp_smooth.contDiffAt.comp x (n.prodMk (contDiffAt_fst.comp x contDiffAt_snd))
  have q := perp_smooth.contDiffAt.comp x (n.prodMk (contDiffAt_snd.comp x contDiffAt_snd))
  have u := (dot_smooth.contDiffAt.comp x (contDiffAt_fst.prodMk contDiffAt_fst)).continuousAt.eventually_const_lt h.1
  have v := (dot_smooth.contDiffAt.comp x (p.prodMk p)).continuousAt.eventually_const_lt h.2.1
  have w := (dot_smooth.contDiffAt.comp x (q.prodMk q)).continuousAt.eventually_const_lt h.2.2
  exact u.and (v.and w)

private theorem normalize_unit {x : R3} (hx : 0 < x ⬝ᵥ x) : unit x ⬝ᵥ unit x=1 := by
  rw [unit,smul_dotProduct,dotProduct_smul]
  change (sqrt (x ⬝ᵥ x))⁻¹*((sqrt (x ⬝ᵥ x))⁻¹*(x ⬝ᵥ x))=1
  rw [← mul_assoc,← sq,inv_pow,sq_sqrt hx.le,inv_mul_cancel₀ hx.ne']

/-- Actual oriented sphere points and common normal from the smooth projection. -/
def projectedRepresentative (x : CoreParameters) (h : validCore x) : FlatLocus.Representative := by
  let n := unit x.1
  have hn : n ⬝ᵥ n=1 := normalize_unit h.1
  have orth (a : R3) : n ⬝ᵥ unit (perp n a)=0 := by simp [unit,perp,dotProduct_smul,dotProduct_sub,hn]
  exact ⟨(⟨n,hn⟩,⟨unit (perp n x.2.1),normalize_unit h.2.1⟩,⟨unit (perp n x.2.2),normalize_unit h.2.2⟩),
    orth _,orth _⟩

theorem projectedRepresentative_core (v : FlatLocus.Representative) :
    projectedRepresentative (rawCore v) (core_fixed v).2 = v := by
  apply Subtype.ext
  have e := (core_fixed v).1
  exact Prod.ext (Subtype.ext (congrArg Prod.fst e)) (Prod.ext
    (Subtype.ext (congrArg (fun x : CoreParameters => x.2.1) e)) (Subtype.ext (congrArg (fun x : CoreParameters => x.2.2) e)))

open SphereProduct

abbrev Tilts := Fin 4 → ℝ

/-- The base point and the two ambient velocities after the Cheeger change of plane. -/
def transverseData (t : ℝ) (x : CoreParameters) (z : Tilts) : Cheeger.V × Cheeger.V × Cheeger.V :=
  let n := x.1
  let P := x.2.1
  let Q := point n x.2.2 (z 2)
  let N := normal n x.2.2 (z 2) (z 3)
  let F := frame P Q n N (z 0) (z 1)
  let I := Cheeger.inverseOperator P Q t
  ((P,Q),I F.1,I F.2)

theorem frameData_injective : Function.Injective JetChart.frameData := by
  rintro ⟨⟨p,q⟩,U,V⟩ ⟨⟨p',q'⟩,U',V'⟩ eq
  have P : p=p' := Subtype.ext (congrArg (fun x : Cheeger.V × Cheeger.V × Cheeger.V => WithLp.toLp 2 x.1.1) eq)
  have Q : q=q' := Subtype.ext (congrArg (fun x : Cheeger.V × Cheeger.V × Cheeger.V => WithLp.toLp 2 x.1.2) eq)
  subst p'; subst q'
  have u : U=U' := ambientVelocityL_injective _ (congrArg (fun x : Cheeger.V × Cheeger.V × Cheeger.V => x.2.1) eq)
  have v : V=V' := ambientVelocityL_injective _ (congrArg (fun x : Cheeger.V × Cheeger.V × Cheeger.V => x.2.2) eq)
  cases u; cases v; rfl

private theorem intrinsic_data (t : ℝ) (v : FlatLocus.Representative) (z : Tilts)
    (small : ∀ i, |z i| < 1) : ∃ w : TangentPair, JetChart.frameData w = transverseData t (rawCore v) z := by
  let n := v.val.1
  let P := v.val.2.1
  let q := v.val.2.2
  let Q := point n.val q.val (z 2)
  let M := normal n.val q.val (z 2) (z 3)
  let F := frame P.val Q n.val M (z 0) (z 1)
  let I := Cheeger.inverseOperator P.val Q t
  obtain ⟨unitQ,_,orth,_⟩ := transverse_axes n.property q.property v.property.2 (small 2).le (small 3).le
  let Q' : FlatLocus.UnitVector := ⟨Q,unitQ⟩
  let p : Base := (unitSphere P,unitSphere Q')
  have tang (V : Cheeger.V) (a : P.val ⬝ᵥ V.1=0) (b : Q ⬝ᵥ V.2=0) :
      P.val ⬝ᵥ (I V).1=0 ∧ Q ⬝ᵥ (I V).2=0 := by
    change _ ⬝ᵥ (V+t • K P.val Q (moment P.val Q V)).1 = 0 ∧ _ ⬝ᵥ (V+t • K P.val Q (moment P.val Q V)).2 = 0
    simp [K,dotProduct_add,dotProduct_smul,a,b]
  have make (V : Cheeger.V) (a : P.val ⬝ᵥ V.1=0) (b : Q ⬝ᵥ V.2=0) :
      ∃ X : Tangent p, ambientVelocityL p X = I V := by
    obtain ⟨e,h⟩ := (exists_velocity_iff P _).mpr (tang V a b).1
    obtain ⟨f,k⟩ := (exists_velocity_iff Q' _).mpr (tang V a b).2
    exact ⟨(e,f),Prod.ext (congrArg WithLp.ofLp h) (congrArg WithLp.ofLp k)⟩
  have qM : Q ⬝ᵥ M=0 := (dotProduct_comm ..).trans orth
  have pn : P.val ⬝ᵥ n.val=0 := (dotProduct_comm ..).trans v.property.1
  obtain ⟨X,hx⟩ := make F.1 (by simp [F,frame,dotProduct_smul]) (by simp [F,frame,dotProduct_smul,qM])
  obtain ⟨Y,hy⟩ := make F.2 (by simp [F,frame,dotProduct_smul,pn]) (by simp [F,frame,dotProduct_smul])
  exact ⟨⟨p,X,Y⟩,Prod.ext rfl (Prod.ext hx hy)⟩

private def pairAt (t : ℝ) (q : CoreParameters × Tilts) : TangentPair := by
  classical
  exact if h : validCore q.1 ∧ ∀ i, |q.2 i| < 1 then
    (intrinsic_data t (projectedRepresentative q.1 h.1) q.2 h.2).choose
  else ⟨(equatorPoint 0,equatorPoint 0),0,0⟩

/-- One compact parameter set simultaneously covers the two singular orbits and
all intermediate separations. The disk uses the supremum norm on four tilts. -/
def compactNormalChart (t : ℝ) : NormalChart CoreParameters Tilts :=
  ⟨pairAt t,coreSet,compact_core,1/2,by norm_num⟩

private theorem chart_data (t : ℝ) {x : CoreParameters} {z : Tilts} (h : validCore x)
    (s : ∀ i, |z i| < 1) : JetChart.frameData ((compactNormalChart t).frame (x,z)) = transverseData t (projectCore x) z := by
  classical
  change JetChart.frameData (pairAt t (x,z)) = _
  simp only [pairAt,dite_eq_left (And.intro h s)]
  exact (intrinsic_data t (projectedRepresentative x h) z s).choose_spec

theorem core_frame_data (t : ℝ) (v : FlatLocus.Representative) {z : Tilts} (hz : ∀ i, |z i| < 1) :
    JetChart.frameData ((compactNormalChart t).frame (rawCore v,z)) = transverseData t (rawCore v) z := by
  exact (chart_data t (core_fixed v).2 hz).trans (congrArg (fun c => transverseData t c z) (core_fixed v).1)

/-- In Euclidean core coordinates the base point and tangent vectors of the
actual chart are jointly smooth on an open neighborhood of the closed disk. -/
theorem compact_chart_smooth (t : ℝ) {x : CoreParameters} {z : Tilts} (h : validCore x)
    (s : ∀ i, |z i| < 1) : ContDiffAt ℝ ∞ (JetChart.frameData ∘ (compactNormalChart t).frame) (x,z) := by
  let c := fun q : CoreParameters × Tilts => projectCore q.1
  have hc : ContDiffAt ℝ ∞ c (x,z) := (projectCore_smooth h).comp (f := Prod.fst) (x,z) contDiffAt_fst
  have n := contDiffAt_fst.comp (x,z) hc
  have p := contDiffAt_fst.comp (x,z) (contDiffAt_snd.comp (x,z) hc)
  have q := contDiffAt_snd.comp (x,z) (contDiffAt_snd.comp (x,z) hc)
  let f (i : Fin 4) := fun x : CoreParameters × Tilts => x.2 i
  have ff (i : Fin 4) : ContDiff ℝ ∞ (f i) := by unfold f; fun_prop
  have rr (i : Fin 4) : ContDiffAt ℝ ∞ (fun p => sqrt (1-(f i p)^2)) (x,z) := by
    apply (contDiffAt_const.sub ((ff i).contDiffAt.pow 2)).sqrt
    exact sub_ne_zero.mpr (ne_of_gt ((sq_lt_one_iff_abs_lt_one _).mpr (s i)))
  have cross {A B : CoreParameters × Tilts → R3} (a : ContDiffAt ℝ ∞ A (x,z)) (b : ContDiffAt ℝ ∞ B (x,z)) :
      ContDiffAt ℝ ∞ (fun u => A u ⨯₃ B u) (x,z) := Cheeger.smooth_cross.contDiffAt.comp _ (a.prodMk b)
  let Q := fun y => point (c y).1 (c y).2.2 (f 2 y)
  let M := fun y => normal (c y).1 (c y).2.2 (f 2 y) (f 3 y)
  have qh : ContDiffAt ℝ ∞ Q (x,z) := ((rr 2).smul q).add ((ff 2).contDiffAt.smul n)
  have mh : ContDiffAt ℝ ∞ M (x,z) :=
    ((rr 3).smul (((rr 2).smul n).sub ((ff 2).contDiffAt.smul q))).add ((ff 3).contDiffAt.smul (cross n q))
  have smoothI {A B : CoreParameters × Tilts → R3} (a : ContDiffAt ℝ ∞ A (x,z)) (b : ContDiffAt ℝ ∞ B (x,z)) :
      ContDiffAt ℝ ∞ (fun u => Cheeger.inverseOperator (c u).2.1 (Q u) t (A u,B u)) (x,z) := by
    have m := (cross p a).add (cross qh b)
    exact (a.add ((contDiffAt_const (c := t)).smul (cross m p))).prodMk (b.add ((contDiffAt_const (c := t)).smul (cross m qh)))
  have calcReg : ContDiffAt ℝ ∞ (fun y => transverseData t (c y) y.2) (x,z) :=
    (p.prodMk qh).prodMk ((smoothI ((rr 1).smul (cross n p)) ((ff 1).contDiffAt.smul mh)).prodMk
      (smoothI ((ff 0).contDiffAt.smul n) ((rr 0).smul (cross mh qh))))
  apply calcReg.congr_of_eventuallyEq
  have nh := (validCore_open.preimage continuous_fst).mem_nhds (show (x,z) ∈ _ from h)
  have ns : ∀ᶠ y in 𝓝 (x,z), ∀ i, |y.2 i|<1 := Filter.eventually_all.mpr fun i =>
    (continuous_abs.comp (ff i).continuous).continuousAt.eventually_lt_const (s i)
  filter_upwards [nh,ns] with y hy hz using chart_data t hy hz

/-- Every orthonormal plane is either in the normalized far region or is
represented by the concrete compact normal chart. This uses the plane-cover
relation accepted by `positive_metrics_of_plane_charts`. -/
theorem compact_chart_cover (P Q : FlatLocus.UnitVector) (t : ℝ) (ht : 0<t)
    (g : SmoothMetric) (X Y : Tangent (unitSphere P,unitSphere Q))
    (xx : g.inner _ X X=1) (yy : g.inner _ Y Y=1) (xy : g.inner _ X Y=0) :
    let p : Base := (unitSphere P,unitSphere Q)
    let C := Cheeger.operator P.val Q.val t ht.le
    (∃ U V : Cheeger.V, BasisChange (C (ambientVelocityL p X)) (C (ambientVelocityL p Y)) U V ∧
       gprod U U=1 ∧ gprod V V=1 ∧ gprod U V=0 ∧ 1/4 < (66+32/t^3)*zillerLower P.val Q.val t U V) ∨
    ∃ x ∈ (compactNormalChart t).core, ∃ z : Tilts, ‖z‖ ≤ (compactNormalChart t).radius ∧
      ((compactNormalChart t).frame (x,z)).Represents ⟨p,X,Y⟩ := by
  intro p C
  obtain ⟨U,V,changeBasis,uu,vv,uv,regions⟩ := cheeger_frame_cover P Q t ht g X Y xx yy xy
  rcases regions with far | ⟨v,a,b,h,k,base,pt,sum,small,_,T,W,m,et,ew,rep,_⟩
  · exact Or.inl ⟨U,V,changeBasis,uu,vv,uv,far⟩
  right
  let z : Tilts := ![a,b,h,k]
  have bound : ‖z‖ ≤ 1/2 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)).mpr
    intro i
    rw [Real.norm_eq_abs,abs_le]
    have total : a^2+b^2+h^2+k^2 ≤ 1/4 := sum.trans small
    fin_cases i <;> dsimp [z] <;> constructor <;>
      nlinarith only [total,sq_nonneg a,sq_nonneg b,sq_nonneg h,sq_nonneg k]
  have bs (i : Fin 4) : |z i| < 1 := (norm_le_pi_norm z i).trans_lt (lt_of_le_of_lt bound (by norm_num))
  refine ⟨rawCore v,⟨v,rfl⟩,z,bound,?_⟩
  have eq := chart_data t (core_fixed v).2 bs
  rw [(core_fixed v).1] at eq
  have target : transverseData t (rawCore v) z = JetChart.frameData (TangentPair.mk p T W) := by
    unfold transverseData rawCore
    dsimp only
    change ((v.val.2.1.val,point v.val.1.val v.val.2.2.val h),_,_) = ((P.val,Q.val),_,_)
    simp only [show z 0 = a from rfl,show z 1 = b from rfl,show z 2 = h from rfl,show z 3 = k from rfl,base,pt]
    exact Prod.ext rfl (Prod.ext et.symm ew.symm)
  rwa [frameData_injective (eq.trans target)]

private def leftAngle (t : ℝ) : ℝ × ℝ := ((1+2*t)/2,-1/2)
private def rightAngle (t : ℝ) : ℝ × ℝ := ((1+2*t)/2,1/2)

private theorem central_pair (v : FlatLocus.Representative) (t : ℝ) :
    let r := (JetChart.axesBasis _ _ v.property.1).repr.symm
    let s := (JetChart.axesBasis _ _ v.property.2).repr.symm
    let p := (JetChart.chart r s).symm 0
    (compactNormalChart t).frame (rawCore v,0) = ⟨p,JetChart.field r s (leftAngle t,0) p,
      JetChart.field r s (rightAngle t,0) p⟩ := by
  intro r s p
  apply frameData_injective
  have H := chart_data t (z := 0) (core_fixed v).2 (by simp)
  rw [(core_fixed v).1] at H
  refine H.trans ?_
  let n := v.val.1.val
  let P := v.val.2.1.val
  let Q := v.val.2.2.val
  have triple (A : FlatLocus.UnitVector) (orth : n ⬝ᵥ A.val=0) : A.val ⨯₃ (n ⨯₃ A.val)=n := by
    rw [cross_cross_eq_smul_sub_smul',show A.val ⬝ᵥ A.val=1 from A.property,
      orth,one_smul,zero_smul,sub_zero]
  have m₁ : moment P Q (n ⨯₃ P,0)=n := by simp [moment,P,triple _ v.property.1]
  have m₂ : moment P Q (0,n ⨯₃ Q)=n := by simp [moment,Q,triple _ v.property.2]
  have p₀ : point n Q 0 = Q := by
    change sqrt (1-(0:ℝ)^2) • Q + (0:ℝ) • n = Q
    simp
  have n₀ : normal n Q 0 0 = n := by
    change sqrt (1-(0:ℝ)^2) • (sqrt (1-(0:ℝ)^2) • n - (0:ℝ) • Q) + (0:ℝ) • _ = n
    simp
  have F₀ : frame P Q n n 0 0 = ((n ⨯₃ P,0),(0,n ⨯₃ Q)) := by
    change ((sqrt (1-(0:ℝ)^2) • _, (0:ℝ) • n),((0:ℝ) • n, sqrt (1-(0:ℝ)^2) • _)) = _
    simp
  change ((P,point n Q 0),Cheeger.inverseOperator P (point n Q 0) t (frame P (point n Q 0) n (normal n Q 0 0) 0 0).1,
    Cheeger.inverseOperator P (point n Q 0) t (frame P (point n Q 0) n (normal n Q 0 0) 0 0).2) =
    (ambientPoint p,ambientVelocityL p (JetChart.field r s (leftAngle t,0) p),ambientVelocityL p (JetChart.field r s (rightAngle t,0) p))
  rw [p₀,n₀,F₀,JetChart.center_longitude v (leftAngle t),JetChart.center_longitude v (rightAngle t)]
  have center : p = (unitSphere v.val.2.1,unitSphere v.val.2.2) := (JetChart.center v).2
  rw [center]
  have l : (leftAngle t).1-(leftAngle t).2=1+t := by unfold leftAngle; dsimp; ring
  have l' : (leftAngle t).1+(leftAngle t).2=t := by unfold leftAngle; dsimp; ring
  have r' : (rightAngle t).1-(rightAngle t).2=t := by unfold rightAngle; dsimp; ring
  have r'' : (rightAngle t).1+(rightAngle t).2=1+t := by unfold rightAngle; dsimp; ring
  rw [l,l',r',r'',Cheeger.inverseOperator_apply,Cheeger.inverseOperator_apply,m₁,m₂]
  simp [K,Cheeger.longitude,add_smul,P,Q,n,ambientPoint]
  exact ⟨rfl,rfl⟩

/-- Both the background curvature and the first perturbation derivative vanish
on the core of the same compact chart which covers the small-penalty planes. -/
theorem compact_chart_core_jet (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) {x : CoreParameters}
    (hx : x ∈ (compactNormalChart t).core) :
    let F := (compactNormalChart t).curvature (paperCoefficients t ht χ)
    F (x,0,0) = 0 ∧ HasDerivAt (fun s => F (x,0,s)) 0 0 := by
  obtain ⟨v,rfl⟩ := hx
  dsimp only [NormalChart.curvature]
  rw [central_pair]
  have bg : Realizes (backgroundMetric t ht) 0 (paperCoefficients t ht χ) := by
    intro p X Y
    simp only [cubicValue,zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 3 ≠ 0),zero_smul,add_zero]
    rfl
  constructor
  · rw [TangentPair.numerator_eq _ bg]
    exact JetChart.flat_torus_curvature v (y := 0) (JetChart.center v).1 rfl t ht (leftAngle t) (rightAngle t)
  · exact JetChart.flat_torus_first v (y := 0) (JetChart.center v).1 rfl t ht χ (leftAngle t) (rightAngle t)

/-- Change the spanning frame to the script's longitude basis on the flat core. -/
def longitudePair (t : ℝ) (w : TangentPair) : TangentPair :=
  ⟨w.point,(Profiles.hh t)⁻¹ • w.first+(Profiles.hh t)⁻¹ • w.second,(-1:ℝ) • w.first+w.second⟩

theorem longitudePair_core (v : FlatLocus.Representative) (t : ℝ) (ht : 0 ≤ t) :
    let r := (JetChart.axesBasis _ _ v.property.1).repr.symm
    let s := (JetChart.axesBasis _ _ v.property.2).repr.symm
    let p := (JetChart.chart r s).symm 0
    longitudePair t ((compactNormalChart t).frame (rawCore v,0)) =
      ⟨p,JetChart.field r s ((1,0),0) p,JetChart.field r s ((0,1),0) p⟩ := by
  intro r s p
  rw [central_pair]
  obtain ⟨L,hL⟩ := JetChart.field_equiv r s ((JetChart.chart r s).map_target (JetChart.center v).1)
  have a : (Profiles.hh t)⁻¹ • (leftAngle t, (0:ℝ × ℝ)) + (Profiles.hh t)⁻¹ • (rightAngle t,0) = ((1,0),0) := by
    ext <;> dsimp [leftAngle,rightAngle,Profiles.hh]
    all_goals field_simp [show 1+2*t ≠ 0 by linarith]; ring
  have b : (-1:ℝ) • (leftAngle t,(0:ℝ × ℝ)) + (rightAngle t,0) = ((0,1),0) := by
    ext <;> dsimp [leftAngle,rightAngle] <;> ring
  change TangentPair.mk p (_ • JetChart.field r s (leftAngle t,0) p + _ • JetChart.field r s (rightAngle t,0) p)
    ((-1:ℝ) • JetChart.field r s (leftAngle t,0) p + JetChart.field r s (rightAngle t,0) p) = _
  have field_basis (d : JetChart.Params) : JetChart.field r s d p = L d := (hL d).symm
  simp only [field_basis]
  exact congrArg₂ (TangentPair.mk p) (by simpa only [map_add,map_smul] using congrArg L a)
    (by simpa only [map_add,map_smul] using congrArg L b)

/-- Every Taylor coefficient along every moving tilt scales by the same area
factor when using the script's longitude basis. -/
theorem longitudePair_coeff (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) (x : CoreParameters) (a : Tilts) (n : ℕ) :
    let c := compactNormalChart t
    let A := paperCoefficients t ht χ
    let L := fun q : CoreParameters × Tilts × ℝ => (longitudePair t (c.frame (q.1,q.2.1))).numerator A q.2.2
    UniformTube.coeff (c.curvature A) n x a = (Profiles.hh t)^2/4 * UniformTube.coeff L n x a := by
  intro c A L
  let f := fun s : ℝ => c.curvature A (x,s • a,s)
  let l := fun s : ℝ => L (x,s • a,s)
  have h := Profiles.hh_pos ht
  have eq : l =ᶠ[𝓝 0] fun s => (2/(Profiles.hh t))^2*f s := by
    filter_upwards [paper_metrics_realize t ht χ] with s ⟨g,hg⟩
    let w := c.frame (x,s • a)
    change (longitudePair t w).numerator A s = _ * w.numerator A s
    rw [TangentPair.numerator_eq _ hg,TangentPair.numerator_eq _ hg]
    have cur := curvatureNumerator_basis_change g w.point w.first w.second (Profiles.hh t)⁻¹ (Profiles.hh t)⁻¹ (-1) 1
    simpa only [longitudePair,one_smul,mul_one,mul_neg_one,sub_neg_eq_add,div_eq_mul_inv,two_mul] using cur
  have jet := eq.iteratedDeriv_eq (n := n)
  rw [iteratedDeriv_const_mul_field] at jet
  change iteratedDeriv n f 0 / n.factorial = (Profiles.hh t)^2/4*(iteratedDeriv n l 0 / n.factorial)
  rw [jet]
  field_simp [h.ne']; ring

end
end LocalHopf.BackgroundGrowth.Transverse
