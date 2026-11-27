import LocalHopf.CurvatureMatrix

/-! # The Cheeger cometric used to initialize the coordinate calculation

Lower ambient velocities with the unit round product. On these covectors, the
inverse metric is twice the round cometric plus the sum of the three diagonal
rotation terms with weight `2t`. This holds in every frame at every sphere pair.
-/
namespace LocalHopf.SphereProduct
open Matrix Bundle
open scoped EuclideanSpace
noncomputable section

private theorem exists_rot (p : Sphere) (ω : R3) :
    ∃ x, velocity p x = WithLp.toLp 2 (ω ⨯₃ p.val.ofLp) := by
  change WithLp.toLp 2 (ω ⨯₃ p.val.ofLp) ∈ (velocity p).range
  rw [show (velocity p).range = (ℝ ∙ p.val)ᗮ from range_mvfderiv_subtypeVal _,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- The diagonal Killing field as an intrinsic tangent vector at a sphere pair. -/
def rotationVector (p : Base) (ω : R3) : Tangent p := ((exists_rot p.1 ω).choose, (exists_rot p.2 ω).choose)

theorem ambient_rotationVector (p : Base) (ω : R3) :
    ambientVelocityL p (rotationVector p ω) = K (ambientPoint p).1 (ambientPoint p).2 ω := by
  change ((velocity p.1 (exists_rot p.1 ω).choose).ofLp, (velocity p.2 (exists_rot p.2 ω).choose).ofLp) = _
  rw [(exists_rot p.1 ω).choose_spec, (exists_rot p.2 ω).choose_spec]
  rfl

/-- Raise the round covector corresponding to `X` using the half-Cheeger metric. -/
def backgroundSharp (p : Base) (t : ℝ) (X : Tangent p) : Tangent p :=
  (2:ℝ) • (X + t • rotationVector p (moment (ambientPoint p).1 (ambientPoint p).2 (ambientVelocityL p X)))

private theorem sharp_velocity (p : Base) (t : ℝ) (X : Tangent p) :
    ambientVelocityL p (backgroundSharp p t X) =
      (2:ℝ) • Cheeger.inverseOperator (ambientPoint p).1 (ambientPoint p).2 t (ambientVelocityL p X) := by
  simp only [backgroundSharp, map_smul, map_add, ambient_rotationVector, Cheeger.inverseOperator_apply]

theorem backgroundSharp_lower (p : Base) (t : ℝ) (ht : 0 ≤ t) (X Y : Tangent p) :
    (backgroundMetric t ht).inner p (backgroundSharp p t X) Y = roundPair p (X.1,X.2) (Y.1,Y.2) := by
  rw [roundPair_ambient]
  change ambientBackground t p (ambientVelocityL p (backgroundSharp p t X)) (ambientVelocityL p Y) = _
  rw [ambientBackground_apply p ht, sharp_velocity]
  simp only [Cheeger.pairing, map_smul]
  have h : Cheeger.operator (ambientPoint p).1 (ambientPoint p).2 t ht
      (Cheeger.inverseOperator (ambientPoint p).1 (ambientPoint p).2 t (ambientVelocityL p X)) =
      ambientVelocityL p X := (Cheeger.inverseEquiv _ _ t ht).symm_apply_apply _
  rw [h]
  change gprod ((2:ℝ) • ambientVelocityL p X) (ambientVelocityL p Y) / 2 = gprod (ambientVelocityL p X) (ambientVelocityL p Y)
  simp [gprod, smul_dotProduct]
  ring

def roundCovector {p : Base} (b : Frame p) (X : Tangent p) (i : Fin 4) :=
  roundPair p (X.1,X.2) ((b i).1,(b i).2)

/-- The inverse matrix of the actual background in any intrinsic frame. The dot
product of moments is the sum of the three rotation terms in the scripts. -/
theorem background_cometric (p : Base) (b : Frame p) (t : ℝ) (ht : 0 ≤ t) (X Y : Tangent p) :
    let m (V : Tangent p) := moment (ambientPoint p).1 (ambientPoint p).2 (ambientVelocityL p V)
    roundCovector b X ⬝ᵥ (gramMatrix (backgroundMetric t ht) b)⁻¹ *ᵥ roundCovector b Y =
      2*(roundPair p (X.1,X.2) (Y.1,Y.2) + t * (m X ⬝ᵥ m Y)) := by
  dsimp only
  let g := backgroundMetric t ht
  have h (Z : Tangent p) : frameCovector g b (backgroundSharp p t Z) = roundCovector b Z := by
    funext i
    exact (g.symm p _ _).trans (backgroundSharp_lower p t ht _ _)
  rw [← h X, ← h Y, ← metric_inverse_pair g b]
  rw [show g.inner p (backgroundSharp p t X) (backgroundSharp p t Y) =
    roundPair p (X.1,X.2) ((backgroundSharp p t Y).1,(backgroundSharp p t Y).2) from backgroundSharp_lower ..]
  simp only [roundPair_ambient, ← ambientVelocityL_apply, sharp_velocity]
  have H := Cheeger.inverseOperator_pair (ambientPoint p).1 (ambientPoint p).2 t (ambientVelocityL p Y) (ambientVelocityL p X)
  have sym (a b : Cheeger.V) : gprod a b = gprod b a := by
    simp only [gprod, dotProduct_comm a.1 b.1, dotProduct_comm a.2 b.2]
  rw [sym, show ∀ a c : Cheeger.V, gprod ((2:ℝ) • a) c = 2*gprod a c by
    intro a c; simp [gprod, smul_dotProduct, mul_add], H, sym (ambientVelocityL p Y), dotProduct_comm]

private theorem round_dual {p : Base} (b : Frame p) (i : Fin 4) :
    ∃ X : Tangent p, ∀ Y : Tangent p, roundPair p (X.1,X.2) (Y.1,Y.2) = b.equivFun Y i := by
  let g := backgroundMetric 0 le_rfl
  let G := gramMatrix g b
  let e : Fin 4 → ℝ := Pi.single i (1/2)
  let x := G⁻¹ *ᵥ e
  let X := b.equivFun.symm x
  have h : G *ᵥ x = e := by rw [show G *ᵥ x = (G*G⁻¹) *ᵥ e from mulVec_mulVec ..,
    mul_nonsing_inv G (gram_isUnit g b),one_mulVec]
  have lower : frameCovector g b X = e := by
    rw [← h]
    funext j
    simp [G,X,gramMatrix,frameCovector,b.equivFun_symm_apply,mulVec,dotProduct,mul_comm]
  refine ⟨X,fun Y => ?_⟩
  have d : g.inner p X Y = frameCovector g b X ⬝ᵥ b.equivFun Y := by
    conv_lhs => rw [← b.equivFun.symm_apply_apply Y]
    simp only [b.equivFun_symm_apply,map_sum,map_smul,smul_eq_mul,frameCovector,dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [g.symm p X (b j),mul_comm]
  rw [← twice_backgroundMetric_zero]
  change 2*g.inner p X Y = _
  rw [d,lower,single_dotProduct]
  ring

/-- In every frame the inverse background Gram matrix is its undeformed value
plus twice t times the three outer products of the diagonal rotations. -/
theorem cometric_entries (p : Base) (b : Frame p) (t : ℝ) (ht : 0 ≤ t) (i j : Fin 4) :
    let rot (k : Fin 3) := b.equivFun (rotationVector p (Pi.single k 1))
    (gramMatrix (backgroundMetric t ht) b)⁻¹ i j = (gramMatrix (backgroundMetric 0 le_rfl) b)⁻¹ i j +
      2*t*(∑ k, rot k i*rot k j) := by
  dsimp only
  let m (X : Tangent p) := moment (ambientPoint p).1 (ambientPoint p).2 (ambientVelocityL p X)
  obtain ⟨X,hx⟩ := round_dual b i
  obtain ⟨Y,hy⟩ := round_dual b j
  have entries (k : Fin 4) (Z : Tangent p) (hz : ∀ W : Tangent p, roundPair p (Z.1,Z.2) (W.1,W.2) = b.equivFun W k) :
      roundCovector b Z = Pi.single k 1 ∧ ∀ l : Fin 3, m Z l = b.equivFun (rotationVector p (Pi.single l 1)) k := by
    constructor
    · funext l
      rw [roundCovector,hz (b l)]
      by_cases e : k=l
      · subst l; simp
      · simp [e,Ne.symm e,Module.Basis.equivFun]
    · intro l
      rw [← hz _,roundPair_ambient]
      change m Z l = gprod (ambientVelocityL p Z) (ambientVelocityL p (rotationVector p (Pi.single l 1)))
      rw [ambient_rotationVector,gprod_K_eq_moment,dotProduct_single,mul_one]
  obtain ⟨ex,mx⟩ := entries i X hx
  obtain ⟨ey,my⟩ := entries j Y hy
  have eq (t : ℝ) (ht : 0 ≤ t) := background_cometric p b t ht X Y
  have H := eq t ht
  have F := eq 0 le_rfl
  simp only [ex,ey,single_dotProduct,one_mul,mulVec_single,MulOpposite.op_one,one_smul,Matrix.col_apply,zero_mul,add_zero] at H F
  change _ = 2*(_+t*(m X ⬝ᵥ m Y)) at H
  rw [dotProduct] at H
  simp_rw [mx,my] at H
  rw [H,F]; ring

end
end LocalHopf.SphereProduct
