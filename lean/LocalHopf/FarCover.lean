import LocalHopf.CompactChart

/-! A compact parameter set for the complementary region of the plane cover. -/
namespace LocalHopf.BackgroundGrowth.Transverse
open Matrix Real Set SphereProduct Filter
open scoped Topology
noncomputable section

abbrev FarParameters := (FlatLocus.UnitVector × FlatLocus.UnitVector) × Cheeger.V × Cheeger.V

private def tangentAt (P Q : R3) (X : Cheeger.V) := P ⬝ᵥ X.1 = 0 ∧ Q ⬝ᵥ X.2 = 0

/-- The boundary is included so the far set is compact. -/
def farSet (t : ℝ) : Set FarParameters := {w |
  tangentAt w.1.1.val w.1.2.val w.2.1 ∧ tangentAt w.1.1.val w.1.2.val w.2.2 ∧
    gprod w.2.1 w.2.1=1 ∧ gprod w.2.2 w.2.2=1 ∧ gprod w.2.1 w.2.2=0 ∧
    1/4 ≤ (66+32/t^3)*zillerLower w.1.1.val w.1.2.val t w.2.1 w.2.2}

private theorem far_closed (t : ℝ) : IsClosed (farSet t) := by
  have grp {A B : FarParameters → Cheeger.V} (a : Continuous A) (b : Continuous B) :
      Continuous (fun w => gprod (A w) (B w)) :=
    ((continuous_fst.comp a).dotProduct (continuous_fst.comp b)).add ((continuous_snd.comp a).dotProduct (continuous_snd.comp b))
  unfold farSet tangentAt
  simp only [Set.ofPred_and]
  repeat' apply IsClosed.inter
  all_goals first | apply isClosed_eq | apply isClosed_le
  all_goals try exact continuous_const
  all_goals try exact Continuous.dotProduct (by fun_prop) (by fun_prop)
  all_goals try exact grp (by fun_prop) (by fun_prop)
  have cross {A B : FarParameters → R3} (h : Continuous A) (k : Continuous B) :
      Continuous (fun z => A z ⨯₃ B z) := Cheeger.smooth_cross.continuous.comp (h.prodMk k)
  have len {A : FarParameters → R3} (h : Continuous A) : Continuous (fun z => sqLength (A z)) := h.dotProduct h
  have mu (j : FarParameters → Cheeger.V) (h : Continuous j) :
      Continuous (fun z : FarParameters => moment z.1.1.val z.1.2.val (j z)) :=
    (cross (by fun_prop) (continuous_fst.comp h)).add (cross (by fun_prop) (continuous_snd.comp h))
  let U : FarParameters → Cheeger.V := fun w => w.2.1
  let V : FarParameters → Cheeger.V := fun w => w.2.2
  have hu : Continuous U := continuous_fst.comp continuous_snd
  have hv : Continuous V := continuous_snd.comp continuous_snd
  have c₁ := cross (continuous_fst.comp hu) (continuous_fst.comp hv)
  have c₂ := cross (continuous_snd.comp hu) (continuous_snd.comp hv)
  have c₃ := cross (mu U hu) (mu V hv)
  exact continuous_const.mul (((len c₁).add (len c₂)).add (continuous_const.mul (len c₃)))

theorem compact_far (t : ℝ) : IsCompact (farSet t) := by
  let one : Cheeger.V := (fun _ => 1,fun _ => 1)
  let B := Icc (-one) one
  have hB : IsCompact B := isCompact_Icc
  apply ((isCompact_univ (X := FlatLocus.UnitVector × FlatLocus.UnitVector)).prod (hB.prod hB)).of_isClosed_subset (far_closed t)
  intro w hw
  have bounds (X : Cheeger.V) (h : gprod X X=1) : X ∈ B := by
    have co (A : R3) (i : Fin 3) : A i ^ 2 ≤ sqLength A := by
      rw [sq]; exact Finset.single_le_sum (fun j _ => mul_self_nonneg (A j)) (Finset.mem_univ i)
    change sqLength X.1 + sqLength X.2=1 at h
    constructor <;> constructor <;> intro i
    all_goals dsimp [one]
    all_goals nlinarith only [h,co X.1 i,co X.2 i,sqLength_nonneg X.1,sqLength_nonneg X.2]
  exact ⟨trivial,bounds _ hw.2.2.1,bounds _ hw.2.2.2.1⟩

private theorem inverse_tangent {P Q : R3} (t : ℝ) {X : Cheeger.V} (h : tangentAt P Q X) :
    tangentAt P Q (Cheeger.inverseOperator P Q t X) := by
  simp [tangentAt,Cheeger.inverseOperator_apply,K,dotProduct_add,dotProduct_smul,h.1,h.2]

private def liftAt (P Q : FlatLocus.UnitVector) (X : Cheeger.V) (h : tangentAt P.val Q.val X) :
    Tangent (unitSphere P,unitSphere Q) :=
  ((exists_velocity_iff P X.1).mpr h.1 |>.choose,(exists_velocity_iff Q X.2).mpr h.2 |>.choose)

private theorem liftAt_eq (P Q : FlatLocus.UnitVector) (X : Cheeger.V) (h : tangentAt P.val Q.val X) :
    ambientVelocityL (unitSphere P,unitSphere Q) (liftAt P Q X h) = X :=
  Prod.ext (congrArg WithLp.ofLp ((exists_velocity_iff P X.1).mpr h.1).choose_spec)
    (congrArg WithLp.ofLp ((exists_velocity_iff Q X.2).mpr h.2).choose_spec)

/-- The ordered tangent pair obtained by applying the inverse Cheeger map to a
normalized far frame. The parameter space itself is compact. -/
def farPair (t : ℝ) (w : ↥(farSet t)) : TangentPair :=
  let P := w.val.1.1
  let Q := w.val.1.2
  let I := Cheeger.inverseOperator P.val Q.val t
  ⟨(unitSphere P,unitSphere Q),liftAt P Q (I w.val.2.1) (inverse_tangent t w.property.1),
    liftAt P Q (I w.val.2.2) (inverse_tangent t w.property.2.1)⟩

theorem farPair_ambient (t : ℝ) (w : ↥(farSet t)) :
    let I := Cheeger.inverseOperator w.val.1.1.val w.val.1.2.val t
    (farPair t w).toAmbient = ((unitSphere w.val.1.1,unitSphere w.val.1.2),I w.val.2.1,I w.val.2.2) := by
  exact Prod.ext rfl (Prod.ext (liftAt_eq _ _ _ (inverse_tangent t w.property.1)) (liftAt_eq _ _ _ (inverse_tangent t w.property.2.1)))

/-- The normalized frames in the compact far family and the compact normal
chart together represent every orthonormal two-plane of every smooth metric. -/
theorem compact_plane_cover (t : ℝ) (ht : 0<t) (g : SmoothMetric) (p : Base) (X Y : Tangent p)
    (xx : g.inner p X X = 1) (yy : g.inner p Y Y = 1) (xy : g.inner p X Y = 0) :
    (∃ w : ↥(farSet t), (farPair t w).Represents ⟨p,X,Y⟩) ∨
    ∃ x ∈ (compactNormalChart t).core, ∃ z : Tilts, ‖z‖ ≤ (compactNormalChart t).radius ∧
      ((compactNormalChart t).frame (x,z)).Represents ⟨p,X,Y⟩ := by
  obtain ⟨p₁,p₂⟩ := p
  obtain ⟨P,rfl⟩ := unitSphere.surjective p₁
  obtain ⟨Q,rfl⟩ := unitSphere.surjective p₂
  let p : Base := (unitSphere P,unitSphere Q)
  let v := ambientVelocityL p
  let C := Cheeger.operator P.val Q.val t ht.le
  let I := Cheeger.inverseOperator P.val Q.val t
  rcases compact_chart_cover P Q t ht g X Y xx yy xy with ⟨U,V,change,uu,vv,uv,far⟩ | near
  · left
    obtain ⟨a,b,c,d,det,e,f⟩ := change
    have tv (T : Tangent p) : tangentAt P.val Q.val (C (v T)) := by
      have h₁ := (exists_velocity_iff P _).mp ⟨T.1,rfl⟩
      have h₂ := (exists_velocity_iff Q _).mp ⟨T.2,rfl⟩
      have h := Cheeger.operator_preserves_tangent P.val Q.val t ht.le (v T)
        ((dotProduct_comm ..).trans h₁) ((dotProduct_comm ..).trans h₂)
      exact ⟨(dotProduct_comm ..).trans h.1,(dotProduct_comm ..).trans h.2⟩
    have lin (a b : ℝ) : tangentAt P.val Q.val (a • C (v X)+b • C (v Y)) := by
      simp [tangentAt,dotProduct_add,dotProduct_smul,(tv X).1,(tv X).2,(tv Y).1,(tv Y).2]
    have tu : tangentAt P.val Q.val U := e ▸ lin a b
    have tw : tangentAt P.val Q.val V := f ▸ lin c d
    let w : ↥(farSet t) := ⟨((P,Q),U,V),tu,tw,uu,vv,uv,far.le⟩
    refine ⟨w,a,b,c,d,det,?_⟩
    have idv (T : Tangent p) : I (C (v T)) = v T := Cheeger.inverse_operator _ _ _ ht.le _
    have hU : I U = v (a • X+b • Y) := by
      change U = a • C (v X)+b • C (v Y) at e
      rw [e,map_add,map_smul,map_smul,idv,idv,map_add,map_smul,map_smul]
    have hV : I V = v (c • X+d • Y) := by
      change V = c • C (v X)+d • C (v Y) at f
      rw [f,map_add,map_smul,map_smul,idv,idv,map_add,map_smul,map_smul]
    have h1 : (farPair t w).first = a • X+b • Y :=
      ambientVelocityL_injective p ((liftAt_eq P Q (I U) (inverse_tangent t tu)).trans hU)
    have h2 : (farPair t w).second = c • X+d • Y :=
      ambientVelocityL_injective p ((liftAt_eq P Q (I V) (inverse_tangent t tw)).trans hV)
    exact congrArg₂ (TangentPair.mk p) h1 h2
  · exact Or.inr near

/-- The global window theorem specialized to the two concrete compact pieces. -/
theorem positive_of_compact_plane_estimates (t : ℝ) (ht : 0<t) (χ : Scalar)
    (near : (compactNormalChart t).Estimates (paperCoefficients t ht.le χ))
    (farCont : ∀ w : ↥(farSet t), ContinuousAt (fun q : ↥(farSet t) × ℝ =>
      (farPair t q.1).numerator (paperCoefficients t ht.le χ) q.2) (w,0))
    (farPos : ∀ w : ↥(farSet t), 0 < (farPair t w).numerator (paperCoefficients t ht.le χ) 0) :
    ∀ᶠ s in nhdsWithin 0 (Ioi 0), ∃ g : SmoothMetric, Realizes g s (paperCoefficients t ht.le χ) ∧
      PositiveSectionalCurvature g := by
  let : CompactSpace ↥(farSet t) := isCompact_iff_compactSpace.mp (compact_far t)
  apply positive_metrics_of_plane_charts t ht.le χ (fun _ : Unit => compactNormalChart t) (fun _ => near)
    (farPair t) univ isCompact_univ (fun w _ => farCont w) (fun w _ => farPos w)
  filter_upwards [] with s
  intro g _ p X Y h₁ h₂ h₃
  rcases compact_plane_cover t ht g p X Y h₁ h₂ h₃ with ⟨w,e⟩ | ⟨x,hx,z,hz,e⟩
  · exact Or.inl ⟨w,trivial,e⟩
  · exact Or.inr ⟨(),x,hx,z,hz,e⟩


end
end LocalHopf.BackgroundGrowth.Transverse
