import LocalHopf.BackgroundJet

/-! The index-lowered rotation fields of the perturbation tensors in the
verifier's longitude-height chart. -/
namespace LocalHopf.SphereProduct.JetChart
open Real Matrix Filter Set LongitudeHeight
open scoped ContDiff Topology
noncomputable section

/-- A covector component obtained by lowering independent ambient rotation
axes on the two spheres with the actual background metric. -/
def rotationCovector (v : FlatLocus.Representative) (t : ℝ) (A B : R3) (j : Fin 4) (y : Params) :=
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (chart r s).symm y
  let w := ambientPoint p
  ambientBackground t p (A ⨯₃ w.1,B ⨯₃ w.2) (ambientVelocityL p (field r s (parameterBasis j) p))

theorem rotationFlat_entry (v : FlatLocus.Representative) (t : ℝ) (ht : 0 ≤ t) (opp : Bool)
    (a : Axis) (j : Fin 4) (y : Params) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm y
    rotationFlat t ht opp a p (ambientVelocityL p (field r s (parameterBasis j) p)) =
      rotationCovector v t (a p) (if opp then -a p else a p) j y := by
  intro r s p
  cases opp
  · rfl
  · change _ = ambientBackground t p (_ , (-a p) ⨯₃ (ambientPoint p).2) _
    rw [map_neg _ (a p)]
    rfl

private theorem gram_row (r s : E3 ≃ₗᵢ[ℝ] E3) {y : Params} (hy : y ∈ (chart r s).target)
    (g : SmoothMetric) (a : Params) (j : Fin 4) :
    coefficient r s g a (parameterBasis j) y = ∑ i, parameterBasis.equivFun a i *
      coefficient r s g (parameterBasis i) (parameterBasis j) y := by
  let p := (chart r s).symm y
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target hy)
  have sum := congrArg L (parameterBasis.equivFun.symm_apply_apply a)
  rw [parameterBasis.equivFun_symm_apply,map_sum] at sum
  simp_rw [L.map_smul] at sum
  simp_rw [hL] at sum
  change g.inner p (field r s a p) (field r s (parameterBasis j) p) = _
  rw [←sum]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul]
  rfl

/-- At every point of the open chart, lowering a rotation column is exactly
multiplication by the covariant Gram matrix. -/
theorem rotationCovector_eq (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (A B : R3) (j : Fin 4)
    {y : Params} (hy : y ∈ (coreChart v).target) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let u := rotationCoordinates (r.symm (WithLp.toLp 2 A)).ofLp (s.symm (WithLp.toLp 2 B)).ofLp y
    rotationCovector v t A B j y = ∑ i, parameterBasis.equivFun u i *
      coefficient r s (backgroundMetric t ht) (parameterBasis i) (parameterBasis j) y := by
  intro r s u
  let p := (chart r s).symm y
  have vel : ambientVelocityL p (field r s u p) = (A ⨯₃ (ambientPoint p).1,B ⨯₃ (ambientPoint p).2) := by
    rw [ambient_field r s ((chart r s).map_target hy),(chart r s).right_inv hy]
    exact rotation_velocity_pair v A B hy
  change ambientBackground t p (A ⨯₃ (ambientPoint p).1,B ⨯₃ (ambientPoint p).2) _ = _
  rw [← vel]
  exact gram_row r s hy (backgroundMetric t ht) u j

/-- All spatial derivatives through order two of a lowered rotation column
for any pair of constant ambient axes. This includes each K and J column with
axis equal to a standard ambient coordinate vector. -/
theorem rotationCovector_jet (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params)
    (A B : R3) (j : Fin 4) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let T := rotationTaylor (r.symm (WithLp.toLp 2 A)).ofLp (s.symm (WithLp.toLp 2 B)).ofLp d.1.1 d.1.2 d.2.1 d.2.2
    let G := metricTaylor t (v.val.2.1.val ⬝ᵥ v.val.2.2.val) ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val) d
    SpatialJet (fun z : ℝ => rotationCovector v t A B j (z • d))
      (∑ i, T 0 i*G 0 i j) (∑ i, (T 1 i*G 0 i j+T 0 i*G 1 i j))
      (∑ i, (T 2 i*G 0 i j+T 1 i*G 1 i j+T 0 i*G 2 i j)) := by
  intro r s T G
  let U := (r.symm (WithLp.toLp 2 A)).ofLp
  let V := (s.symm (WithLp.toLp 2 B)).ofLp
  have ln (z : ℝ) : line d.1.1 d.1.2 d.2.1 d.2.2 z = z • d := by ext <;> dsimp [line] <;> ring
  have rot (i : Fin 4) : SpatialJet (fun z : ℝ => parameterBasis.equivFun (rotationCoordinates U V (z • d)) i)
      (T 0 i) (T 1 i) (T 2 i) := by simpa only [ln] using rotationCoordinate_jet U V d.1.1 d.1.2 d.2.1 d.2.2 i
  have full := jet_sum (fun i => jet_mul (rot i) (coordinate_gram_jet v t ht d i j))
  apply full.congr
  have path : Continuous (fun z : ℝ => z • d) := continuous_id.smul continuous_const
  have h0 : (0:ℝ) • d ∈ (chart r s).target := by rw [zero_smul]; exact (center v).1
  filter_upwards [path.continuousAt.preimage_mem_nhds ((chart r s).open_target.mem_nhds h0)] with z hz
  exact rotationCovector_eq v t ht A B j hz

/-- Convolution of two scalar Taylor polynomials modulo the cube of the spatial parameter. -/
def productJet (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 0*y 0,x 1*y 0+x 0*y 1,x 2*y 0+x 1*y 1+x 0*y 2]

/-- Rotation jets evaluated directly from the ambient coordinates of both axes. -/
def axisRotationTaylor (v : FlatLocus.Representative) (d : Params) (A B : R3) :=
  let n := v.val.1.val
  let components (p X : R3) : R3 := ![p ⬝ᵥ X,(n ⨯₃ p) ⬝ᵥ X,n ⬝ᵥ X]
  rotationTaylor (components v.val.2.1.val A) (components v.val.2.2.val B) d.1.1 d.1.2 d.2.1 d.2.2

theorem axisRotationTaylor_eq (v : FlatLocus.Representative) (d : Params) (A B : R3) :
    axisRotationTaylor v d A B = rotationTaylor
      ((align _ _ v.property.1).symm (WithLp.toLp 2 A)).ofLp ((align _ _ v.property.2).symm (WithLp.toLp 2 B)).ofLp
      d.1.1 d.1.2 d.2.1 d.2.2 := by
  rw [align_coordinates,align_coordinates]
  rfl

/-- Taylor polynomial of an index-lowered column with fixed ambient axes. -/
def loweredTaylor (v : FlatLocus.Representative) (t : ℝ) (d : Params) (A B : R3) (j : Fin 4) (m : Fin 3) :=
  let R := axisRotationTaylor v d A B
  let G := metricTaylor t (v.val.2.1.val ⬝ᵥ v.val.2.2.val) ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val) d
  ∑ i, productJet (fun h => R h i) (fun h => G h i j) m

def secondRotationAxis (opp : Bool) (x : R3) := if opp then -x else x

private theorem linear_axis (v : FlatLocus.Representative) (t : ℝ) (opp : Bool)
    (a : R3) (j : Fin 4) (y : Params) :
    rotationCovector v t a (secondRotationAxis opp a) j y =
      ∑ i, a i * rotationCovector v t (Pi.single i 1) (secondRotationAxis opp (Pi.single i 1)) j y := by
  let p := (coreChart v).symm y
  let w := ambientPoint p
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let V := ambientVelocityL p (field r s (parameterBasis j) p)
  let signMap : R3 →ₗ[ℝ] R3 := if opp then -LinearMap.id else LinearMap.id
  let R := (crossProduct.flip w.1).prod ((crossProduct.flip w.2).comp signMap)
  let L := ((ambientBackground t p).flip V).toLinearMap.comp R
  have eval (x : R3) : L x = rotationCovector v t x (secondRotationAxis opp x) j y := by cases opp <;> rfl
  have e : ∑ i, a i • (Pi.single i (1:ℝ) : R3) = a := by ext k; simp [Pi.single_apply]
  have z := congrArg L e
  rw [map_sum] at z
  simp_rw [L.map_smul] at z
  simp only [eval,smul_eq_mul] at z
  exact z.symm

/-- Spatial two-jet of a lowered field with a varying axis, including the
point-sum and point-difference axes of the first-order perturbation. -/
theorem moving_rotationFlat_jet (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (d : Params)
    (opp : Bool) (a : Axis) (A : Fin 3 → R3)
    (ha : ∀ l, SpatialJet (fun z : ℝ => a ((coreChart v).symm (z • d)) l) (A 0 l) (A 1 l) (A 2 l)) (j : Fin 4) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let T (m : Fin 3) := ∑ l, productJet (fun h => A h l)
      (loweredTaylor v t d (Pi.single l 1) (secondRotationAxis opp (Pi.single l 1)) j) m
    SpatialJet (fun z : ℝ =>
      let p := (chart r s).symm (z • d)
      rotationFlat t ht opp a p (ambientVelocityL p (field r s (parameterBasis j) p))) (T 0) (T 1) (T 2) := by
  intro r s T
  have cols (l : Fin 3) :=
    rotationCovector_jet v t ht d (Pi.single l 1) (secondRotationAxis opp (Pi.single l 1)) j
  dsimp only at cols
  simp only [align_coordinates] at cols
  have J := jet_sum (fun l => jet_mul (ha l) (cols l))
  apply J.congr
  filter_upwards with z
  exact (rotationFlat_entry v t ht opp a j (z • d)).trans (linear_axis v t opp _ j (z • d))

/-- Actual ambient coordinates of a sphere point on a chart ray. -/
def sphereTaylor (n p : FlatLocus.UnitVector) (a h : ℝ) : Fin 3 → R3 :=
  ![p.val,a • (n.val ⨯₃ p.val)+h • n.val,(-((a^2+h^2)/2)) • p.val]

private theorem aligned_point_jet (n p : FlatLocus.UnitVector) (perp : n.val ⬝ᵥ p.val=0) (a h : ℝ) (i : Fin 3) :
    let r := align n p perp
    let T := sphereTaylor n p a h
    SpatialJet (fun z : ℝ => (r (point (a*z,h*z)).val).ofLp i) (T 0 i) (T 1 i) (T 2 i) := by
  intro r T
  have J := point_jets 0 a h
  simp only [zero_add,cos_zero,sin_zero,mul_zero,mul_one] at J
  have v := jet_add (jet_add (jet_scale (p.val i) J.1) (jet_scale ((n.val ⨯₃ p.val) i) J.2.1)) (jet_scale (n.val i) J.2.2)
  apply SpatialJet.congr (f := fun z : ℝ => p.val i*(point (a*z,h*z)).val.ofLp 0+
      (n.val ⨯₃ p.val) i*(point (a*z,h*z)).val.ofLp 1+n.val i*(point (a*z,h*z)).val.ofLp 2) ?_ ?_
  · convert v using 1 <;> simp [T,sphereTaylor] <;> ring
  · filter_upwards with z
    have eq := congrFun (align_apply n p perp (point (a*z,h*z)).val.ofLp) i
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using eq

theorem sphere_axes_jet (v : FlatLocus.Representative) (d : Params) (i : Fin 3) :
    let P := sphereTaylor v.val.1 v.val.2.1 (d.1.1-d.1.2) d.2.1
    let Q := sphereTaylor v.val.1 v.val.2.2 (d.1.1+d.1.2) d.2.2
    SpatialJet (fun z : ℝ => point₁ ((coreChart v).symm (z • d)) i) (P 0 i) (P 1 i) (P 2 i) ∧
    SpatialJet (fun z : ℝ => point₂ ((coreChart v).symm (z • d)) i) (Q 0 i) (Q 1 i) (Q 2 i) := by
  intro P Q
  constructor
  · apply (aligned_point_jet _ _ v.property.1 (d.1.1-d.1.2) d.2.1 i).congr
    filter_upwards with z
    change ((align _ _ v.property.1 (point (z*d.1.1-z*d.1.2,z*d.2.1)).val).ofLp i) = _
    rw [show z*d.1.1-z*d.1.2=(d.1.1-d.1.2)*z by ring,mul_comm z d.2.1]
  · apply (aligned_point_jet _ _ v.property.2 (d.1.1+d.1.2) d.2.2 i).congr
    filter_upwards with z
    change ((align _ _ v.property.2 (point (z*d.1.1+z*d.1.2,z*d.2.2)).val).ofLp i) = _
    rw [show z*d.1.1+z*d.1.2=(d.1.1+d.1.2)*z by ring,mul_comm z d.2.2]

end
end LocalHopf.SphereProduct.JetChart
