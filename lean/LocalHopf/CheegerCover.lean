import LocalHopf.CurvatureBasis
import LocalHopf.TransverseFrames
import LocalHopf.FrameCompactness

/-! Pointwise transfer of the transverse cover through the inverse Cheeger endomorphism. -/
namespace LocalHopf.BackgroundGrowth.Transverse
open Matrix Real SphereProduct
noncomputable section

/-- Ordered pairs span the same two-plane via the indicated invertible change of basis. -/
def BasisChange {E : Type*} [AddCommGroup E] [Module ℝ E] (X Y U V : E) : Prop :=
  ∃ a b c d : ℝ, a*d-b*c ≠ 0 ∧ U=a • X+b • Y ∧ V=c • X+d • Y

private theorem compose {E : Type*} [AddCommGroup E] [Module ℝ E] {X Y U V T W : E}
    (f : BasisChange X Y U V) (g : BasisChange U V T W) : BasisChange X Y T W := by
  obtain ⟨a,b,c,d,hd,rfl,rfl⟩ := f
  obtain ⟨A,B,C,D,hD,rfl,rfl⟩ := g
  refine ⟨A*a+B*c,A*b+B*d,C*a+D*c,C*b+D*d,?_,by module,by module⟩
  convert mul_ne_zero hD hd using 1; ring

private theorem map_change {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) {X Y U V : E} (e : BasisChange X Y U V) :
    BasisChange (L X) (L Y) (L U) (L V) := by
  obtain ⟨a,b,c,d,h,rfl,rfl⟩ := e
  exact ⟨a,b,c,d,h,by simp,by simp⟩

private theorem gram_schmidt (X Y : Cheeger.V) (nz : X ≠ 0) (ind : ∀ k : ℝ, Y ≠ k • X) :
    ∃ U V : Cheeger.V, BasisChange X Y U V ∧ gprod U U = 1 ∧ gprod V V = 1 ∧ gprod U V = 0 := by
  have positive (Z : Cheeger.V) (hn : Z ≠ 0) : 0 < gprod Z Z := by
    have hp := Cheeger.inverseOperator_pos (0:R3) 0 (t := 0) le_rfl hn
    simpa [Cheeger.inverseOperator_apply] using hp
  have lin (U V : Cheeger.V) (c d : ℝ) : gprod (c • U) (d • V) = c*d*gprod U V := by
    simp [gprod,smul_dotProduct,dotProduct_smul]; ring
  let k := gprod X Y / gprod X X
  let W := Y-k • X
  have w : W ≠ 0 := fun e => ind k (sub_eq_zero.mp e)
  have xy : gprod X W = 0 := by
    have expand : gprod X W = gprod X Y-k*gprod X X := by
      simp [W,gprod,dotProduct_sub,dotProduct_smul]; ring
    rw [expand,show k*gprod X X = gprod X Y from div_mul_cancel₀ _ (positive X nz).ne',sub_self]
  let a := (sqrt (gprod X X))⁻¹
  let d := (sqrt (gprod W W))⁻¹
  have normalized (Z : Cheeger.V) (hn : Z ≠ 0) : let b := (sqrt (gprod Z Z))⁻¹; gprod (b • Z) (b • Z) = 1 := by
    intro b
    rw [lin,← sq]
    change (sqrt (gprod Z Z))⁻¹^2 * gprod Z Z = 1
    rw [inv_pow,sq_sqrt (positive Z hn).le,inv_mul_cancel₀ (positive Z hn).ne']
  refine ⟨a • X,d • W,⟨a,0,-d*k,d,?_,by simp,?_⟩,normalized X nz,normalized W w,?_⟩
  · simp only [zero_mul,sub_zero]
    exact mul_ne_zero (inv_ne_zero (sqrt_pos.mpr (positive X nz)).ne') (inv_ne_zero (sqrt_pos.mpr (positive W w)).ne')
  · dsimp [W]; module
  · rw [lin,xy,mul_zero]

private theorem axis_change {X Y U V : Cheeger.V} {e θ : ℝ}
    (rot : (U,V)=rotatePair X Y θ ∨ (V,U)=rotatePair X Y θ) (he : e^2=1) :
    BasisChange X Y U (e • V) := by
  have en : e ≠ 0 := by intro h; simp [h] at he
  have unit : cos θ^2 + sin θ^2=1 := cos_sq_add_sin_sq θ
  rcases rot with h | h
  · obtain ⟨u,v⟩ := Prod.mk.inj h
    refine ⟨cos θ,sin θ,-e*sin θ,e*cos θ,?_,u,?_⟩
    · convert en using 1; linear_combination e*unit
    · rw [v]; module
  · obtain ⟨v,u⟩ := Prod.mk.inj h
    refine ⟨-sin θ,cos θ,e*cos θ,e*sin θ,?_,u,?_⟩
    · convert neg_ne_zero.mpr en using 1; linear_combination -e*unit
    · rw [v]; module

/-- An ambient basis change lifts to tangent vectors at the same sphere pair.
The area factor is positive and works for every metric on that tangent space. -/
private theorem lift_change {p : Base} {X Y : Tangent p} {U V : Cheeger.V}
    (rel : BasisChange (ambientVelocityL p X) (ambientVelocityL p Y) U V) :
    ∃ (T W : Tangent p) (m : ℝ), ambientVelocityL p T = U ∧ ambientVelocityL p W = V ∧
      (TangentPair.mk p T W).Represents ⟨p,X,Y⟩ ∧ 0 < m ∧
      ∀ g : SmoothMetric, curvatureNumerator g p T W = m*curvatureNumerator g p X Y := by
  obtain ⟨a,b,c,d,det,h,k⟩ := rel
  refine ⟨a • X+b • Y,c • X+d • Y,(a*d-b*c)^2,?_,?_,⟨a,b,c,d,det,rfl⟩,sq_pos_of_ne_zero det,?_⟩
  · simpa only [map_add,map_smul] using h.symm
  · simpa only [map_add,map_smul] using k.symm
  · intro g; exact curvatureNumerator_basis_change g p X Y a b c d

/-- An actual orthonormal tangent plane either has round preimage penalty above
the uniform threshold, or has a representative in the Cheeger image of the
transverse disk at its own base point. The two-plane change is invertible. -/
theorem cheeger_frame_cover (P Q : FlatLocus.UnitVector) (t : ℝ) (ht : 0 < t)
    (g : SmoothMetric) (X Y : Tangent (unitSphere P,unitSphere Q))
    (xx : g.inner _ X X = 1) (yy : g.inner _ Y Y=1) (xy : g.inner _ X Y=0) :
    let p : Base := (unitSphere P,unitSphere Q)
    let A := ambientVelocityL p X
    let B := ambientVelocityL p Y
    let C := Cheeger.operator P.val Q.val t ht.le
    let I := Cheeger.inverseOperator P.val Q.val t
    ∃ U V : Cheeger.V, BasisChange (C A) (C B) U V ∧
      gprod U U=1 ∧ gprod V V=1 ∧ gprod U V=0 ∧
      let bound := (66+32/t^3)*zillerLower P.val Q.val t U V
      1/4 < bound ∨ ∃ (v : FlatLocus.Representative) (a b h k : ℝ),
        v.val.2.1=P ∧ point v.val.1.val v.val.2.2.val h=Q.val ∧
        a^2+b^2+h^2+k^2 ≤ bound ∧ bound ≤ 1/4 ∧
        let F := frame P.val Q.val v.val.1.val (normal v.val.1.val v.val.2.2.val h k) a b
        BasisChange A B (I F.1) (I F.2) ∧ ∃ (T W : Tangent p) (m : ℝ),
          ambientVelocityL p T=I F.1 ∧ ambientVelocityL p W=I F.2 ∧
          (TangentPair.mk p T W).Represents ⟨p,X,Y⟩ ∧ 0 < m ∧
          ∀ g' : SmoothMetric, curvatureNumerator g' p T W=m*curvatureNumerator g' p X Y := by
  intro p A B C I
  have inj := ambientVelocityL_injective p
  have nonzero : C A ≠ 0 := by
    intro e
    have av : A=0 := C.map_eq_zero_iff.mp e
    have ax : X=0 := inj (av.trans ((ambientVelocityL p).map_zero).symm)
    simp [ax] at xx
  have ind (k : ℝ) : C B ≠ k • C A := by
    intro e
    rw [← C.map_smul] at e
    have y : Y=k • X := inj ((C.injective e).trans ((ambientVelocityL p).map_smul k X).symm)
    have h : k=0 := by simpa [y,xx] using xy
    simp [y,h] at yy
  obtain ⟨U,V,e,uu,vv,uv⟩ := gram_schmidt (C A) (C B) nonzero ind
  refine ⟨U,V,e,uu,vv,uv,?_⟩
  intro bound
  rcases lt_or_ge (1/4) bound with far | small
  · exact Or.inl far
  right
  have tangent (Z : Tangent p) :
      P.val ⬝ᵥ (C (ambientVelocityL p Z)).1 = 0 ∧ Q.val ⬝ᵥ (C (ambientVelocityL p Z)).2 = 0 := by
    have x : P.val ⬝ᵥ (ambientVelocityL p Z).1=0 := (exists_velocity_iff P _).mp ⟨Z.1,rfl⟩
    have y : Q.val ⬝ᵥ (ambientVelocityL p Z).2=0 := (exists_velocity_iff Q _).mp ⟨Z.2,rfl⟩
    have h := Cheeger.operator_preserves_tangent P.val Q.val t ht.le (ambientVelocityL p Z)
      ((dotProduct_comm ..).trans x) ((dotProduct_comm ..).trans y)
    exact ⟨(dotProduct_comm ..).trans h.1,(dotProduct_comm ..).trans h.2⟩
  have tu (a b : ℝ) : P.val ⬝ᵥ (a • C A+b • C B).1=0 ∧ Q.val ⬝ᵥ (a • C A+b • C B).2=0 := by
    have ex := tangent X
    have ey := tangent Y
    change P.val ⬝ᵥ (C A).1=0 ∧ Q.val ⬝ᵥ (C A).2=0 at ex
    change P.val ⬝ᵥ (C B).1=0 ∧ Q.val ⬝ᵥ (C B).2=0 at ey
    simp [dotProduct_add,dotProduct_smul,ex.1,ex.2,ey.1,ey.2]
  obtain ⟨a,b,c,d,det,ua,va⟩ := e
  have rel : BasisChange (C A) (C B) U V := ⟨a,b,c,d,det,ua,va⟩
  have uT := tu a b
  have vT := tu c d
  rw [← ua] at uT
  rw [← va] at vT
  obtain ⟨θ,T,W,f,v,x,y,h,k,rot,sign,base,pt,fr,sum⟩ :=
    covers_small P Q ht U V uu vv uv uT.1 vT.1 uT.2 vT.2 small
  refine ⟨v,x,y,h,k,base,pt,sum,small,?_⟩
  rw [fr]
  have act : BasisChange U V T (f • W) := axis_change rot sign
  have changed := map_change I (compose rel act)
  change BasisChange (I (C A)) (I (C B)) (I T) (I (f • W)) at changed
  rw [show I (C A) = A from Cheeger.inverse_operator _ _ _ ht.le A,
      show I (C B) = B from Cheeger.inverse_operator _ _ _ ht.le B] at changed
  exact ⟨changed,lift_change changed⟩

end
end LocalHopf.BackgroundGrowth.Transverse
