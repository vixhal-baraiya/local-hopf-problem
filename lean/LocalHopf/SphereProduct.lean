import LocalHopf.Cheeger
import LocalHopf.FlatLocus
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! # The round product and the mixed tangent planes in §1

The differential of the sphere inclusion identifies intrinsic tangent vectors
with the vectors perpendicular to the base point in three-dimensional Euclidean space.
-/

namespace LocalHopf.SphereProduct

open Set Metric Matrix FlatLocus
open scoped Manifold ContDiff EuclideanSpace

noncomputable section

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := ↥(sphere (0 : E3) 1)
abbrev Base := Sphere × Sphere

private theorem norm_sq (p : R3) : ‖WithLp.toLp 2 p‖ ^ 2 = p ⬝ᵥ p := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

/-- The coordinate unit vectors of the incidence description are exactly Mathlib's unit sphere. -/
def unitSphere : UnitVector ≃ₜ Sphere where
  toFun p := ⟨WithLp.toLp 2 p.val, mem_sphere_zero_iff_norm.mpr (by
    have h := norm_sq p.val
    have hp : p.val ⬝ᵥ p.val = 1 := p.property
    rw [hp] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 p.val)])⟩
  invFun x := ⟨x.val.ofLp, by
    change x.val.ofLp ⬝ᵥ x.val.ofLp = 1
    rw [← norm_sq, WithLp.toLp_ofLp, mem_sphere_zero_iff_norm.mp x.property, one_pow]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp 2 _).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val

/-- Smooth metrics on the product of the two sphere manifolds in Mathlib. -/
abbrev SmoothMetric := Bundle.ContMDiffRiemannianMetric ((𝓡 2).prod (𝓡 2)) ∞
  (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) (TangentSpace ((𝓡 2).prod (𝓡 2)) : Base → Type)

/-- Ambient components of an intrinsic tangent vector. -/
def velocity (x : Sphere) : TangentSpace (𝓡 2) x →L[ℝ] E3 :=
  mvfderiv (𝓡 2) (Subtype.val : Sphere → E3) x

theorem velocity_injective (x : Sphere) : Function.Injective (velocity x) :=
  injective_mvfderiv_subtypeVal_sphere x

theorem exists_velocity_iff (p : UnitVector) (v : R3) :
    (∃ X, velocity (unitSphere p) X = WithLp.toLp 2 v) ↔ p.val ⬝ᵥ v = 0 := by
  change WithLp.toLp 2 v ∈ (velocity (unitSphere p)).range ↔ _
  rw [show (velocity (unitSphere p)).range = (ℝ ∙ (unitSphere p).val)ᗮ from range_mvfderiv_subtypeVal _,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [EuclideanSpace.inner_eq_star_dotProduct, unitSphere, dotProduct_comm]

abbrev ProductTangent (p : Base) := TangentSpace (𝓡 2) p.1 × TangentSpace (𝓡 2) p.2

/-- The ambient velocity depends smoothly on both the sphere point and tangent vector. -/
theorem smooth_velocity : ContMDiff (𝓡 2).tangent 𝓘(ℝ, E3) ∞
    (fun v : TangentBundle (𝓡 2) Sphere => velocity v.1 v.2) := by
  have h : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (Subtype.val : Sphere → E3) := contMDiff_coe_sphere
  exact (contMDiff_snd_tangentBundle_modelSpace E3 𝓘(ℝ, E3)).comp
    (h.contMDiff_tangentMap (m := ∞) (by simp))

/-- The pointwise round product pairing, induced by the two sphere inclusions. -/
def roundPair (p : Base) (X Y : ProductTangent p) : ℝ :=
  inner ℝ (velocity p.1 X.1) (velocity p.1 Y.1) + inner ℝ (velocity p.2 X.2) (velocity p.2 Y.2)

theorem roundPair_pos (p : Base) {X : ProductTangent p} (hX : X ≠ 0) : 0 < roundPair p X X := by
  have hv : velocity p.1 X.1 ≠ 0 ∨ velocity p.2 X.2 ≠ 0 := by
    by_contra! h
    apply hX
    exact Prod.ext ((velocity_injective _ ) (h.1.trans (map_zero _).symm))
      ((velocity_injective _) (h.2.trans (map_zero _).symm))
  unfold roundPair
  rcases hv with h | h
  · exact add_pos_of_pos_of_nonneg (real_inner_self_pos.mpr h) real_inner_self_nonneg
  · exact add_pos_of_nonneg_of_pos real_inner_self_nonneg (real_inner_self_pos.mpr h)

/-- Smoothness of the squared round-product length on the product of tangent bundles. -/
theorem smooth_round_energy :
    ContMDiff ((𝓡 2).tangent.prod (𝓡 2).tangent) 𝓘(ℝ, ℝ) ∞
      (fun v : TangentBundle (𝓡 2) Sphere × TangentBundle (𝓡 2) Sphere =>
        roundPair (v.1.1, v.2.1) (v.1.2, v.2.2) (v.1.2, v.2.2)) := by
  have h₁ := smooth_velocity.comp
    (contMDiff_fst (I := (𝓡 2).tangent) (J := (𝓡 2).tangent) (M := TangentBundle (𝓡 2) Sphere)
      (N := TangentBundle (𝓡 2) Sphere))
  have h₂ := smooth_velocity.comp
    (contMDiff_snd (I := (𝓡 2).tangent) (J := (𝓡 2).tangent) (M := TangentBundle (𝓡 2) Sphere)
      (N := TangentBundle (𝓡 2) Sphere))
  have hi : ContDiff ℝ ∞ (fun v : E3 => inner ℝ v v) :=
    ContDiff.inner ℝ contDiff_id contDiff_id
  exact (hi.contMDiff.comp h₁).add (hi.contMDiff.comp h₂)

/-- Coordinates of a pair of intrinsic tangent vectors in the ambient product. -/
def ambientVelocity (p : Base) (X : ProductTangent p) : Cheeger.V :=
  ((velocity p.1 X.1).ofLp, (velocity p.2 X.2).ofLp)

theorem roundPair_ambient (p : Base) (X Y : ProductTangent p) :
    roundPair p X Y = gprod (ambientVelocity p X) (ambientVelocity p Y) := by
  simp [roundPair, ambientVelocity, gprod, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- The paper's background pairing: half of the metric induced by the horizontal lift. -/
def backgroundPair (p : Base) (t : ℝ) (ht : 0 ≤ t) (X Y : ProductTangent p) : ℝ :=
  Cheeger.pairing p.1.val.ofLp p.2.val.ofLp t ht (ambientVelocity p X) (ambientVelocity p Y) / 2

theorem backgroundPair_pos (p : Base) (t : ℝ) (ht : 0 ≤ t) {X : ProductTangent p} (hn : X ≠ 0) :
    0 < backgroundPair p t ht X X := by
  apply div_pos _ (by norm_num)
  apply Cheeger.pairing_pos _ _ _ ht
  intro hz
  have h := roundPair_pos p hn
  rw [roundPair_ambient, hz] at h
  simp [gprod] at h

theorem twice_backgroundPair_zero (p : Base) (X Y : ProductTangent p) :
    2 * backgroundPair p 0 le_rfl X Y = roundPair p X Y := by
  rw [backgroundPair, Cheeger.pairing_zero, roundPair_ambient]
  ring

private def circleTangent (n p : UnitVector) :
    TangentSpace (𝓡 2) (unitSphere p) :=
  ((exists_velocity_iff p (n.val ⨯₃ p.val)).2 (dot_cross_self n.val p.val)).choose

private theorem velocity_circleTangent (n p : UnitVector) :
    velocity _ (circleTangent n p) = WithLp.toLp 2 (n.val ⨯₃ p.val) :=
  ((exists_velocity_iff p (n.val ⨯₃ p.val)).2 (dot_cross_self n.val p.val)).choose_spec

private theorem tangent_unit (n p : UnitVector) (hp : n.val ⬝ᵥ p.val = 0) :
    inner ℝ (velocity _ (circleTangent n p)) (velocity _ (circleTangent n p)) = 1 := by
  rw [velocity_circleTangent, real_inner_self_eq_norm_sq, norm_sq]
  exact (cross_unit _ _ n.property p.property hp).1

/-- Base point in the product manifold corresponding to the incidence data. -/
def base (x : Plane) : Base := (unitSphere (oriented x).val.2.1, unitSphere (oriented x).val.2.2)

/-- The mixed spanning pair of §1 as intrinsic tangent vectors at the actual sphere points. -/
def mixedBasis (x : Plane) : Fin 2 → ProductTangent (base x) :=
  ![(circleTangent (oriented x).val.1 (oriented x).val.2.1, 0), (0, circleTangent (oriented x).val.1 (oriented x).val.2.2)]

theorem mixedBasis_orthonormal (x : Plane) :
    roundPair _ (mixedBasis x 0) (mixedBasis x 0) = 1 ∧
    roundPair _ (mixedBasis x 1) (mixedBasis x 1) = 1 ∧
    roundPair _ (mixedBasis x 0) (mixedBasis x 1) = 0 := by
  let v := oriented x
  let p := (unitSphere v.val.2.1, unitSphere v.val.2.2)
  let X := circleTangent v.val.1 v.val.2.1
  let Y := circleTangent v.val.1 v.val.2.2
  change roundPair p (X, 0) (X, 0) = 1 ∧ roundPair p (0, Y) (0, Y) = 1 ∧
    roundPair p (X, 0) (0, Y) = 0
  dsimp only [roundPair, p, X, Y]
  rw [(velocity _).map_zero, (velocity _).map_zero]
  simp only [inner_zero_left, inner_zero_right, add_zero, zero_add]
  exact ⟨tangent_unit _ _ v.property.1, tangent_unit _ _ v.property.2, trivial⟩

/-- The tangent subspace represented by the incidence point. -/
def mixedPlane (x : Plane) : Submodule ℝ (ProductTangent (base x)) :=
  Submodule.span ℝ (range (mixedBasis x))

theorem mixedPlane_finrank (x : Plane) : Module.finrank ℝ (mixedPlane x) = 2 := by
  have ne (n p : UnitVector) (h : n.val ⬝ᵥ p.val = 0) : circleTangent n p ≠ 0 := by
    intro hz
    have H := tangent_unit n p h
    simp [hz] at H
  have hi : LinearIndependent ℝ (mixedBasis x) := by
    apply LinearIndependent.pair_iff.mpr
    intro a b h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change a • circleTangent (oriented x).val.1 (oriented x).val.2.1 + b • 0 = 0 at h₁
    change a • 0 + b • circleTangent (oriented x).val.1 (oriented x).val.2.2 = 0 at h₂
    rw [smul_zero, add_zero] at h₁
    rw [smul_zero, zero_add] at h₂
    exact ⟨(smul_eq_zero.mp h₁).resolve_right (ne _ _ (oriented x).property.1),
      (smul_eq_zero.mp h₂).resolve_right (ne _ _ (oriented x).property.2)⟩
  exact finrank_span_eq_card hi

end
end LocalHopf.SphereProduct
