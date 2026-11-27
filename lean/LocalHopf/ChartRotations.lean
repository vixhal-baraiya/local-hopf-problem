import LocalHopf.FlatTorusJet
import LocalHopf.ChartCometric
import LocalHopf.SpatialJet

/-! Rotation columns used by the spatial curvature calculation, as genuine coordinate velocities. -/
namespace LocalHopf.SphereProduct.JetChart
open Real Matrix Filter
open scoped Topology ContDiff
noncomputable section

/-- Each adapted orthonormal basis is positively oriented. -/
theorem align_cross (n p : FlatLocus.UnitVector) (hp : n.val ⬝ᵥ p.val=0) (x y : R3) :
    let r := align n p hp
    (r (WithLp.toLp 2 (x ⨯₃ y))).ofLp = (r (WithLp.toLp 2 x)).ofLp ⨯₃ (r (WithLp.toLp 2 y)).ofLp := by
  intro r
  let L := n.val ⨯₃ p.val
  have PL : p.val ⨯₃ L = n.val := by
    dsimp only [L]; rw [cross_cross_eq_smul_sub_smul',show p.val ⬝ᵥ p.val=1 from p.property,hp,one_smul,zero_smul,sub_zero]
  have NL : n.val ⨯₃ L = -p.val := by
    dsimp only [L]; rw [cross_cross_eq_smul_sub_smul',hp,show n.val ⬝ᵥ n.val=1 from n.property,one_smul,zero_smul,zero_sub]
  have LP : L ⨯₃ p.val = -n.val := by rw [← cross_anticomm p.val L,PL]
  have LN : L ⨯₃ n.val = p.val := by rw [← cross_anticomm n.val L,NL,neg_neg]
  have PN : p.val ⨯₃ n.val = -L := (cross_anticomm n.val p.val).symm
  dsimp only [r]
  rw [align_apply,align_apply,align_apply]
  change (x ⨯₃ y) 0 • p.val+(x ⨯₃ y) 1 • L+(x ⨯₃ y) 2 • n.val =
    (x 0 • p.val+x 1 • L+x 2 • n.val) ⨯₃ (y 0 • p.val+y 1 • L+y 2 • n.val)
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,cross_self,PL,NL,LP,LN,PN,smul_zero,add_zero,zero_add]
  change (x 1*y 2-x 2*y 1) • p.val+(x 2*y 0-x 0*y 2) • L+(x 0*y 1-x 1*y 0) • n.val = _
  rw [←show L = n.val ⨯₃ p.val from rfl]
  module

def longitudeSpeed (w : R3) (a z : ℝ) :=
  w 2 - z/sqrt (1-z^2)*(cos a*w 0 + sin a*w 1)
def heightSpeed (w : R3) (a z : ℝ) :=
  sqrt (1-z^2)*(sin a*w 0-cos a*w 1)

/-- The vector returned by `chart(...).rot` before truncating its Taylor series. -/
def rotationCoordinates (u v : R3) (y : Params) : Params :=
  let l := longitudeSpeed u (y.1.1-y.1.2) y.2.1
  let m := longitudeSpeed v (y.1.1+y.1.2) y.2.2
  (((l+m)/2,(m-l)/2),heightSpeed u (y.1.1-y.1.2) y.2.1,heightSpeed v (y.1.1+y.1.2) y.2.2)

theorem rotation_velocity_pair (v : FlatLocus.Representative) (axis₁ axis₂ : R3) {y : Params} (hy : y ∈ (coreChart v).target) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let U := (r.symm (WithLp.toLp 2 axis₁)).ofLp
    let V := (s.symm (WithLp.toLp 2 axis₂)).ofLp
    let p := ambientPoint ((chart r s).symm y)
    fderiv ℝ (ambientPoint ∘ (chart r s).symm) y (rotationCoordinates U V y) = (axis₁ ⨯₃ p.1,axis₂ ⨯₃ p.2) := by
  intro r s U V p
  have factor (axis : R3) (N P : FlatLocus.UnitVector) (hp : N.val ⬝ᵥ P.val=0) (a z : ℝ) (hz : |z|<1) :
      let r := align N P hp
      let u := (r.symm (WithLp.toLp 2 axis)).ofLp
      (r (WithLp.toLp 2 (longitudeSpeed u a z • LongitudeHeight.lonVector a z +
        heightSpeed u a z • LongitudeHeight.heightVector a z))).ofLp =
        axis ⨯₃ (sphereAction r (LongitudeHeight.point (a,z))).val.ofLp := by
    intro r u
    have act := LongitudeHeight.rotation_components u a z hz
    change u ⨯₃ _ = longitudeSpeed u a z • _ + heightSpeed u a z • _ at act
    rw [←act,align_cross]
    have undo : (r (WithLp.toLp 2 u)).ofLp = axis := congrArg WithLp.ofLp (r.apply_symm_apply (WithLp.toLp 2 axis))
    rw [undo]
    rfl
  let a := longitudeSpeed U (y.1.1-y.1.2) y.2.1
  let b := longitudeSpeed V (y.1.1+y.1.2) y.2.2
  have l : (rotationCoordinates U V y).1.1-(rotationCoordinates U V y).1.2=a := by dsimp [rotationCoordinates,a]; ring
  have m : (rotationCoordinates U V y).1.1+(rotationCoordinates U V y).1.2=b := by dsimp [rotationCoordinates,b]; ring
  rw [chart_velocity r s hy,l,m]
  exact Prod.ext (factor axis₁ _ _ v.property.1 _ _ hy.2.1.1.2) (factor axis₂ _ _ v.property.2 _ _ hy.2.2.1.2)

theorem rotation_velocity (v : FlatLocus.Representative) (axis : R3) {y : Params} (hy : y ∈ (coreChart v).target) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let U := (r.symm (WithLp.toLp 2 axis)).ofLp
    let V := (s.symm (WithLp.toLp 2 axis)).ofLp
    let p := ambientPoint ((chart r s).symm y)
    fderiv ℝ (ambientPoint ∘ (chart r s).symm) y (rotationCoordinates U V y) = K p.1 p.2 axis :=
  rotation_velocity_pair v axis axis hy

/-- At every height and longitude, the rotation coordinates returned by the
script are precisely the entries used by the inverse metric of the manifold. -/
theorem rotationEntry_adapted (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (i : Fin 4) (k : Fin 3) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let axis := WithLp.toLp 2 (Pi.single k (1:ℝ))
    let a := rotationCoordinates (r.symm axis).ofLp (s.symm axis).ofLp y
    rotationEntry r s y i k = parameterBasis.equivFun a i := by
  intro r s axis a
  let p := (chart r s).symm y
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target hy)
  let b := parameterBasis.map L.toLinearEquiv
  have hb (j : Fin 4) : b j=field r s (parameterBasis j) p := by simpa [b] using hL (parameterBasis j)
  have rot : rotationVector p (Pi.single k 1) = L a := by
    apply ambientVelocityL_injective p
    rw [ambient_rotationVector,hL a,ambient_field r s ((chart r s).map_target hy),(chart r s).right_inv hy]
    exact (rotation_velocity v (Pi.single k 1) hy).symm
  rw [← rotationEntry_coordinates r s hy b hb k i]
  change b.equivFun (rotationVector p _) i = _
  rw [rot]
  simp [b,Module.Basis.equivFun_apply]


end
end LocalHopf.SphereProduct.JetChart
