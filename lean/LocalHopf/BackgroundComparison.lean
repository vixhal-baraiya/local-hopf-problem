import LocalHopf.BackgroundJet
import LocalHopf.BackgroundCertificate
import LocalHopf.CompactPositivity

/-! Transfer of the signed-separation background calculation to the tangent
planes of the sphere product. -/
namespace LocalHopf.SphereProduct.JetChart
open Real Matrix BackgroundGrowth
noncomputable section

private theorem commonNormal (P Q : FlatLocus.UnitVector) :
    ∃ n : FlatLocus.UnitVector, n.val ⬝ᵥ P.val = 0 ∧ n.val ⬝ᵥ Q.val = 0 := by
  let f : R3 →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun z => (z ⬝ᵥ P.val,z ⬝ᵥ Q.val)
      map_add' := fun x y => by simp [add_dotProduct]
      map_smul' := fun a x => by simp [smul_dotProduct] }
  obtain ⟨z,hz,hn⟩ := (LinearMap.ker f).ne_bot_iff.mp (LinearMap.ker_ne_bot_of_finrank_lt (by simp [R3]))
  have eq : (z ⬝ᵥ P.val,z ⬝ᵥ Q.val) = (0,0) := hz
  have pos : 0<z ⬝ᵥ z := lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i))) (Ne.symm (dotProduct_self_eq_zero.not.mpr hn))
  let l := (sqrt (z ⬝ᵥ z))⁻¹
  have unit : (l • z) ⬝ᵥ (l • z) = 1 := by
    simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul,← mul_assoc,← sq,l,inv_pow,sq_sqrt pos.le,inv_mul_cancel₀ pos.ne']
  have ep : z ⬝ᵥ P.val = 0 := congrArg Prod.fst eq
  have eq' : z ⬝ᵥ Q.val = 0 := congrArg Prod.snd eq
  exact ⟨⟨l • z,unit⟩,by simp [smul_dotProduct,ep],by simp [smul_dotProduct,eq']⟩

private def physical (v : FlatLocus.Representative) (d : Params) : Cheeger.V :=
  let n := v.val.1.val
  let p := v.val.2.1.val
  let q := v.val.2.2.val
  ((d.1.1-d.1.2) • (n ⨯₃ p)+d.2.1 • n,(d.1.1+d.1.2) • (n ⨯₃ q)+d.2.2 • n)

/-- Coordinate action of the inverse Cheeger endomorphism. -/
def pullCoordinates (t c : ℝ) (x : Params) : Params :=
  (((1+2*t)*x.1.1,x.1.2),(1+t)*x.2.1+t*c*x.2.2,t*c*x.2.1+(1+t)*x.2.2)

private theorem inverse_physical (v : FlatLocus.Representative) (t : ℝ) (d : Params) :
    let p := v.val.2.1.val
    let q := v.val.2.2.val
    Cheeger.inverseOperator p q t (physical v d) = physical v (pullCoordinates t (p ⬝ᵥ q) d) := by
  intro p q
  let n := v.val.1.val
  let height := (d.2.1 • n,d.2.2 • n)
  have sum : physical v d = d.1.1 • K p q n + (-d.1.2) • J p q n + height := by
    ext <;> simp only [physical,K,J,height,n,p,q,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul] <;> ring
  have KJ : moment p q (K p q n) = (2:ℝ) • n ∧ moment p q (J p q n) = 0 := by
    have hp : p ⬝ᵥ p = 1 := v.val.2.1.property
    have hq : q ⬝ᵥ q = 1 := v.val.2.2.property
    have hnp : n ⬝ᵥ p = 0 := v.property.1
    have hnq : n ⬝ᵥ q = 0 := v.property.2
    simp [moment,K,J,cross_cross_eq_smul_sub_smul',hp,hq,hnp,hnq,dotProduct_comm q n,two_smul]
  have H : Cheeger.inverseOperator p q t (K p q n) = (1+2*t) • K p q n := by
    rw [Cheeger.inverseOperator_apply,KJ.1]
    simp [K,add_smul,smul_smul,mul_comm t 2]
  have JH : Cheeger.inverseOperator p q t (J p q n) = J p q n := by rw [Cheeger.inverseOperator_apply,KJ.2]; simp [K]
  rw [sum,map_add,map_add,map_smul,map_smul,H,JH,show Cheeger.inverseOperator p q t height = _ from
    inverse_height p q n t _ _ v.val.2.1.property v.val.2.2.property v.property.1 v.property.2]
  ext <;> simp only [physical,pullCoordinates,K,J,p,q,n,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul] <;> ring

private theorem pull_surjective (t c : ℝ) (ht : 0 ≤ t) (hc : c^2 ≤ 1) : Function.Surjective (pullCoordinates t c) := by
  intro d
  let den := Profiles.D t c
  have hd : den ≠ 0 := (Profiles.D_pos ht hc).ne'
  have hh : 1+2*t ≠ 0 := by linarith
  refine ⟨((d.1.1/(1+2*t),d.1.2),((1+t)*d.2.1-t*c*d.2.2)/den,((1+t)*d.2.2-t*c*d.2.1)/den),?_⟩
  ext <;> dsimp [pullCoordinates] <;> field_simp [hh,hd] <;> unfold den Profiles.D <;> ring

private theorem lower_physical (v : FlatLocus.Representative) (t : ℝ) (a b : Params) :
    let p := v.val.2.1.val
    let q := v.val.2.2.val
    let c := p ⬝ᵥ q
    let w := (v.val.1.val ⨯₃ p) ⬝ᵥ q
    zillerLower p q t (physical v a) (physical v b) =
      zillerLower ![1,0,0] ![c,w,0] t (chartVector c w (parameterBasis.equivFun a)) (chartVector c w (parameterBasis.equivFun b)) := by
  intro p q c w
  let n := v.val.1.val
  let r := align _ _ v.property.1
  let R (x : R3) := (r (WithLp.toLp 2 x)).ofLp
  have dot (x y : R3) : R x ⬝ᵥ R y = x ⬝ᵥ y := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using r.inner_map_map (WithLp.toLp 2 y) (WithLp.toLp 2 x)
  have cross (x y : R3) : R (x ⨯₃ y) = R x ⨯₃ R y := align_cross _ _ v.property.1 _ _
  have add (x y : R3) : R (x+y) = R x+R y := by simp [R,WithLp.toLp_add]
  have scale (k : ℝ) (x : R3) : R (k • x) = k • R x := by simp [R,WithLp.toLp_smul]
  have P : R ![1,0,0] = p := by simp [R,r,align_apply,p]
  have N : R ![0,0,1] = n := by simp [R,r,align_apply,n]
  have Q : R ![c,w,0] = q := by
    have e : (r.symm (WithLp.toLp 2 q)).ofLp = ![c,w,0] := by
      have e := align_coordinates _ _ v.property.1 (WithLp.toLp 2 q)
      change _ = ![c,w,n ⬝ᵥ q] at e
      exact e.trans (congrArg (fun z : ℝ => (![c,w,z] : R3)) v.property.2)
    rw [←e]
    exact congrArg WithLp.ofLp (r.apply_symm_apply _)
  let V (d : Params) := chartVector c w (parameterBasis.equivFun d)
  have vel (d : Params) : physical v d = (R (V d).1,R (V d).2) := by
    have eq : ((d.1.1-d.1.2) • ((![0,0,1] : R3) ⨯₃ ![1,0,0])+d.2.1 • (![0,0,1] : R3),
                (d.1.1+d.1.2) • ((![0,0,1] : R3) ⨯₃ ![c,w,0])+d.2.2 • (![0,0,1] : R3)) = V d := by
      dsimp only [V]
      rw [parameterBasis_coordinates]
      apply Prod.ext <;> ext i <;> fin_cases i <;> simp [chartVector,cross_apply] <;> ring
    change _ = (R (V d).1,R (V d).2)
    rw [←eq]; simp only [add,scale,cross,P,Q,N]; rfl
  have mo (d : Params) : moment p q (physical v d) = R (moment ![1,0,0] ![c,w,0] (V d)) := by
    rw [vel]; simp only [moment,add,cross,P,Q]
  rw [zillerLower,zillerLower,mo,mo,vel,vel]
  simp only [sqLength,←cross,dot,V]


/-- The finite signed-separation inequality suffices for the intrinsic (Z) at
every base point and for every spanning pair. -/
theorem comparison_of_separation_bound (t : ℝ) (ht : 0 ≤ t)
    (bound : ∀ c w : ℝ, c^2+w^2=1 → ∀ a b : Params,
      pulledCurvature t c (parameterBasis.equivFun a) (parameterBasis.equivFun b) ≤
        2*backgroundNumerator t c w (pullCoordinates t c a) (pullCoordinates t c b)) :
    BackgroundGrowth.Transverse.backgroundComparison t ht := by
  rintro ⟨base,U,V⟩ P Q X Y data
  let A := unitSphere.symm base.1
  let B := unitSphere.symm base.2
  have p : A.val = P := congrArg (fun e : AmbientPairData => e.1.1) data
  have q : B.val = Q := congrArg (fun e : AmbientPairData => e.1.2) data
  subst P; subst Q
  obtain ⟨n,hn,hq⟩ := commonNormal A B
  let v : FlatLocus.Representative := ⟨(n,A,B),hn,hq⟩
  let c := A.val ⬝ᵥ B.val
  let w := (n.val ⨯₃ A.val) ⬝ᵥ B.val
  let r := align n A hn
  let s := align n B hq
  have ctr : (chart r s).symm 0 = base := (center v).2.trans (Prod.ext (unitSphere.apply_symm_apply _) (unitSphere.apply_symm_apply _))
  have h0 : (0:Params) ∈ (chart r s).target := (center v).1
  have hp : base ∈ (chart r s).source := ctr ▸ (chart r s).map_target h0
  have at0 : chart r s base = 0 := ctr ▸ (chart r s).right_inv h0
  have circle : c^2+w^2=1 := separation_circle v
  obtain ⟨L,hL⟩ := field_equiv r s hp
  have chart_pair (Z : Tangent base) (T : Cheeger.V)
      (E : ambientVelocityL base Z = Cheeger.inverseOperator A.val B.val t T) :
      ∃ d : Params, physical v d = T ∧ field r s (pullCoordinates t c d) base = Z := by
    obtain ⟨d,hd⟩ := pull_surjective t c ht (by nlinarith only [circle,sq_nonneg w]) (L.symm Z)
    have eq : field r s (pullCoordinates t c d) base = Z := by rw [← hL,hd,L.apply_symm_apply]
    refine ⟨d,(Cheeger.inverseEquiv A.val B.val t ht).injective ?_,eq⟩
    change Cheeger.inverseOperator A.val B.val t (physical v d) = Cheeger.inverseOperator A.val B.val t T
    rw [show Cheeger.inverseOperator A.val B.val t (physical v d) = _ from inverse_physical v t d,←E,←eq,ambient_field r s hp,at0]
    exact (center_velocity v _).symm
  obtain ⟨a,ax,au⟩ := chart_pair U X (congrArg (fun e : AmbientPairData => e.2.1) data)
  obtain ⟨b,by',bv⟩ := chart_pair V Y (congrArg (fun e : AmbientPairData => e.2.2) data)
  have actual : curvatureNumerator (backgroundMetric t ht) base U V =
      backgroundNumerator t c w (pullCoordinates t c a) (pullCoordinates t c b) := by
    have eq := curvature_eq_backgroundNumerator v t ht (pullCoordinates t c a) (pullCoordinates t c b)
    change curvatureNumerator _ ((chart r s).symm 0) (field r s _ _) (field r s _ _) = _ at eq
    rwa [ctr,au,bv] at eq
  change zillerLower A.val B.val t X Y ≤ 2*curvatureNumerator (backgroundMetric t ht) base U V
  rw [←ax,←by',actual,show zillerLower A.val B.val t (physical v a) (physical v b) = _ from lower_physical v t a b]
  exact (zillerLower_le_chart ht circle _ _).trans (bound c w circle a b)


end
end LocalHopf.SphereProduct.JetChart
