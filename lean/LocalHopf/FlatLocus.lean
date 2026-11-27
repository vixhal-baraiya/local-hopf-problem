import LocalHopf.FlatLocusData
import LocalHopf.Vectors
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # The incidence space of the candidate flat planes in §1

A point records the two unit sphere points and their common unoriented normal line.
The matrix `n nᵀ` represents that line without choosing a sign. Over a coincident
or antipodal pair the line is still part of the point.
-/

namespace LocalHopf.FlatLocus

open Set Matrix

abbrev UnitVector := ↥({p : R3 | p ⬝ᵥ p = 1} : Set R3)

private theorem coord_sq_le (p : UnitVector) (i : Fin 3) : p.val i ^ 2 ≤ 1 := by
  calc
    _ = p.val i * p.val i := sq _
    _ ≤ p.val ⬝ᵥ p.val := Finset.single_le_sum (fun j _ => mul_self_nonneg (p.val j)) (Finset.mem_univ i)
    _ = 1 := p.property

instance : CompactSpace UnitVector := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_Icc (a := fun _ : Fin 3 => (-1 : ℝ)) (b := fun _ => 1)).of_isClosed_subset
  · apply isClosed_eq _ continuous_const
    simp only [dotProduct, Fin.sum_univ_three]
    fun_prop
  · intro p hp
    constructor <;> intro i <;> have h := coord_sq_le ⟨p, hp⟩ i <;> dsimp <;> nlinarith

/-- Oriented representatives `(n,p₁,p₂)` of the incidence space. -/
abbrev Representative := ↥({v : UnitVector × UnitVector × UnitVector |
  v.1.val ⬝ᵥ v.2.1.val = 0 ∧ v.1.val ⬝ᵥ v.2.2.val = 0} : Set _)

instance : CompactSpace Representative := by
  apply isCompact_iff_compactSpace.mp
  apply IsClosed.isCompact
  change IsClosed (({v : UnitVector × UnitVector × UnitVector | v.1.val ⬝ᵥ v.2.1.val = 0}) ∩
    {v | v.1.val ⬝ᵥ v.2.2.val = 0})
  apply IsClosed.inter <;> apply isClosed_eq _ continuous_const <;>
    apply Continuous.dotProduct <;> fun_prop

abbrev Ambient := (R3 × R3) × Matrix (Fin 3) (Fin 3) ℝ

def forgetOrientation (v : Representative) : Ambient :=
  ((v.val.2.1.val, v.val.2.2.val), vecMulVec v.val.1.val v.val.1.val)

/-- The §1 parameter space `([n], p₁, p₂)` with its subspace topology. -/
abbrev Plane := ↥(range forgetOrientation)

private theorem continuous_forget : Continuous forgetOrientation := by
  unfold forgetOrientation
  apply Continuous.prodMk
  · fun_prop
  · apply continuous_matrix
    intro i j
    have hc (k : Fin 3) : Continuous (fun v : Representative => v.val.1.val k) :=
      (continuous_apply k).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    exact (hc i).mul (hc j)

instance : CompactSpace Plane := isCompact_iff_compactSpace.mp (isCompact_range continuous_forget)

/-- The weight `1 - n_z²` is independent of the orientation. -/
def weight (x : Plane) : ℝ := 1 - x.val.2 2 2

theorem continuous_weight : Continuous weight := by
  unfold weight
  fun_prop

theorem weight_nonneg (x : Plane) : 0 ≤ weight x := by
  obtain ⟨v, hv⟩ := x.property
  unfold weight
  rw [← hv]
  simpa [forgetOrientation, vecMulVec_apply, sq] using sub_nonneg.mpr (coord_sq_le v.val.1 2)

def regular : Set Plane := {x | x.val.1.2 ≠ x.val.1.1 ∧ x.val.1.2 ≠ -x.val.1.1}

private noncomputable def along (n p : UnitVector) (a : ℝ) : R3 :=
  Real.cos a • p.val + Real.sin a • (n.val ⨯₃ p.val)

private theorem along_unit (n p : UnitVector) (h : n.val ⬝ᵥ p.val = 0) (a : ℝ) :
    along n p a ⬝ᵥ along n p a = 1 := by
  have hc := cross_unit n.val p.val n.property p.property h
  simp only [along, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hc.1, hc.2, dot_cross_self, mul_zero, mul_one, add_zero, zero_add]
  rw [show p.val ⬝ᵥ p.val = 1 from p.property]
  nlinarith [Real.cos_sq_add_sin_sq a]

private theorem along_perp (n p : UnitVector) (h : n.val ⬝ᵥ p.val = 0) (a : ℝ) :
    n.val ⬝ᵥ along n p a = 0 := by
  simp [along, dotProduct_add, dotProduct_smul, h, dot_self_cross]

private noncomputable def rotate (v : Representative) (a : ℝ) : Plane :=
  Set.rangeFactorization forgetOrientation
    ⟨(v.val.1, v.val.2.1, ⟨along v.val.1 v.val.2.1 a, along_unit _ _ v.property.1 a⟩),
      v.property.1, along_perp _ _ v.property.1 a⟩

private theorem continuous_rotate (v : Representative) : Continuous (rotate v) := by
  apply Continuous.subtype_mk
  change Continuous (fun a : ℝ => ((v.val.2.1.val, along v.val.1 v.val.2.1 a),
    vecMulVec v.val.1.val v.val.1.val))
  unfold along
  fun_prop

private theorem rotate_regular (v : Representative) {a : ℝ} (ha : a ∈ Ioo 0 Real.pi) :
    rotate v a ∈ regular := by
  let p := v.val.2.1.val
  let q := v.val.1.val ⨯₃ p
  have hq := cross_unit v.val.1.val p v.val.1.property v.val.2.1.property v.property.1
  have hcoord : q ⬝ᵥ along v.val.1 v.val.2.1 a = Real.sin a := by
    simp [along, dotProduct_add, dotProduct_smul, q, p, hq.1, hq.2]
  have hsin := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  change along _ _ a ≠ p ∧ along _ _ a ≠ -p
  constructor <;> intro he <;> rw [he] at hcoord
  · linarith [hq.2]
  · rw [dotProduct_neg] at hcoord
    linarith [hq.2]

/-- Regular pairs approximate every incidence point while keeping its normal line fixed. -/
theorem mem_closure_regular_weight (x : Plane) :
    x ∈ closure {y | y ∈ regular ∧ weight y = weight x} := by
  obtain ⟨v, hv⟩ := x.property
  by_cases hr : x ∈ regular
  · exact subset_closure ⟨hr, rfl⟩
  have H : Set.MapsTo (rotate v) (Ioo 0 Real.pi) {y | y ∈ regular ∧ weight y = weight x} := by
    intro a ha
    exact ⟨rotate_regular v ha, by unfold weight; rw [← hv]; rfl⟩
  have H' := H.closure (continuous_rotate v)
  rw [closure_Ioo Real.pi_pos.ne] at H'
  change ¬(x.val.1.2 ≠ x.val.1.1 ∧ x.val.1.2 ≠ -x.val.1.1) at hr
  rw [← hv] at hr
  by_cases he : v.val.2.2.val = v.val.2.1.val
  · have hx : rotate v 0 = x := by
      apply Subtype.ext
      rw [← hv]
      change ((_, along _ _ 0), _) = _
      simp [along, forgetOrientation, he]
    exact hx ▸ H' (left_mem_Icc.mpr Real.pi_pos.le)
  · have hn : v.val.2.2.val = -v.val.2.1.val := by
      by_contra hn
      exact hr ⟨he, hn⟩
    have hx : rotate v Real.pi = x := by
      apply Subtype.ext
      rw [← hv]
      change ((_, along _ _ Real.pi), _) = _
      simp [along, forgetOrientation, hn]
    exact hx ▸ H' (right_mem_Icc.mpr Real.pi_pos.le)

/-- Density on the oriented incidence space itself, keeping the entire normal
fixed. This also approximates each individual plane over a singular pair. -/
theorem regular_representative_dense (v : Representative) :
    v ∈ closure {w : Representative | (Set.rangeFactorization forgetOrientation w) ∈ regular ∧ w.val.1=v.val.1} := by
  by_cases hr : Set.rangeFactorization forgetOrientation v ∈ regular
  · exact subset_closure ⟨hr,rfl⟩
  let path (a : ℝ) : Representative :=
    ⟨(v.val.1, v.val.2.1, ⟨along v.val.1 v.val.2.1 a, along_unit _ _ v.property.1 a⟩),
      v.property.1,along_perp _ _ v.property.1 a⟩
  have cont : Continuous path := by
    unfold path along
    fun_prop
  have maps : Set.MapsTo path (Ioo 0 Real.pi) {w | Set.rangeFactorization forgetOrientation w ∈ regular ∧ w.val.1=v.val.1} :=
    fun _ h => ⟨rotate_regular v h,rfl⟩
  have den := maps.closure cont
  rw [closure_Ioo Real.pi_pos.ne] at den
  change ¬(v.val.2.2.val ≠ v.val.2.1.val ∧ v.val.2.2.val ≠ -v.val.2.1.val) at hr
  by_cases he : v.val.2.2.val = v.val.2.1.val
  · have eq : path 0 = v := by
      apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ (Subtype.ext ?_)) <;> try rfl
      simp [path,along,he]
    exact eq ▸ den (left_mem_Icc.mpr Real.pi_pos.le)
  · have hn : v.val.2.2.val = -v.val.2.1.val := by by_contra h; exact hr ⟨he,h⟩
    have eq : path Real.pi = v := by
      apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ (Subtype.ext ?_)) <;> try rfl
      simp [path,along,hn]
    exact eq ▸ den (right_mem_Icc.mpr Real.pi_pos.le)

theorem regular_dense : Dense regular := fun x =>
  closure_mono (show {y | y ∈ regular ∧ weight y = weight x} ⊆ regular from fun _ hy => hy.1)
    (mem_closure_regular_weight x)

theorem equator_dense (x : Plane) (hx : weight x = 0) :
    x ∈ closure {y | y ∈ regular ∧ weight y = 0} := by
  simpa only [hx] using mem_closure_regular_weight x

/-- For unit normals the projector identifies exactly the two signs of the same line. -/
theorem normal_line_eq {n m : R3} (hn : n ⬝ᵥ n = 1) (hm : m ⬝ᵥ m = 1) :
    vecMulVec n n = vecMulVec m m ↔ n = m ∨ n = -m := by
  constructor
  · intro h
    have hmul := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A *ᵥ n) h
    simp only [vecMulVec_mulVec, hn, op_smul_eq_smul, one_smul] at hmul
    have hsq := congrArg (fun v : R3 => v ⬝ᵥ v) hmul
    simp only [hn, smul_dotProduct, dotProduct_smul, smul_eq_mul, hm, mul_one] at hsq
    rcases (mul_self_eq_one_iff.mp hsq.symm) with hpos | hneg
    · left; simpa only [hpos, one_smul] using hmul
    · right; simpa only [hneg, neg_one_smul] using hmul
  · rintro (rfl | rfl)
    · rfl
    · ext i j
      simp [vecMulVec_apply]

/-- On a mixed product plane, the bracket term of the Cheeger curvature bound (Z)
vanishes exactly for the common-normal planes of §1. The statement also applies over
coincident and antipodal points. -/
theorem mixed_bracket_eq_zero_iff (p q X Y : UnitVector)
    (hp : p.val ⬝ᵥ X.val = 0) (hq : q.val ⬝ᵥ Y.val = 0) :
    (p.val ⨯₃ X.val) ⨯₃ (q.val ⨯₃ Y.val) = 0 ↔
    ∃ n : UnitVector, n.val ⬝ᵥ p.val = 0 ∧ n.val ⬝ᵥ q.val = 0 ∧
      X.val = n.val ⨯₃ p.val ∧ (Y.val = n.val ⨯₃ q.val ∨ Y.val = -(n.val ⨯₃ q.val)) := by
  let b := p.val ⨯₃ X.val
  let c := q.val ⨯₃ Y.val
  have hb : b ⬝ᵥ b = 1 := (cross_unit _ _ p.property X.property hp).1
  have hc : c ⬝ᵥ c = 1 := (cross_unit _ _ q.property Y.property hq).1
  have recover (u v : UnitVector) (huv : u.val ⬝ᵥ v.val = 0) :
      (u.val ⨯₃ v.val) ⨯₃ u.val = v.val := by
    rw [cross_cross_eq_smul_sub_smul, show u.val ⬝ᵥ u.val = 1 from u.property,
      dotProduct_comm v.val u.val, huv, zero_smul, one_smul, sub_zero]
  constructor
  · intro h
    have line : b = c ∨ b = -c := by
      have hparallel := cross_cross_eq_smul_sub_smul b c c
      change b ⨯₃ c = 0 at h
      rw [h, map_zero, LinearMap.zero_apply, hc, one_smul] at hparallel
      have heq : (b ⬝ᵥ c) • c = b := sub_eq_zero.mp hparallel.symm
      have hn := congrArg (fun v : R3 => v ⬝ᵥ v) heq
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hc, hb, mul_one] at hn
      rcases mul_self_eq_one_iff.mp hn with hpos | hneg
      · left; simpa [hpos] using heq.symm
      · right; simpa [hneg] using heq.symm
    have hbp : b ⬝ᵥ p.val = 0 := by rw [dotProduct_comm]; exact dot_self_cross ..
    have hcq : c ⬝ᵥ q.val = 0 := by rw [dotProduct_comm]; exact dot_self_cross ..
    have hx : X.val = b ⨯₃ p.val := (recover p X hp).symm
    have hy : Y.val = c ⨯₃ q.val := (recover q Y hq).symm
    refine ⟨⟨b,hb⟩, hbp, ?_, hx, ?_⟩
    · rcases line with h | h <;> simp [h, hcq, neg_dotProduct]
    · change Y.val = b ⨯₃ q.val ∨ Y.val = -(b ⨯₃ q.val)
      rcases line with h | h
      · exact Or.inl (h.symm ▸ hy)
      · right; simpa [h] using hy
  · rintro ⟨n, hnp, hnq, hx, hy⟩
    have undo (u : UnitVector) (h : n.val ⬝ᵥ u.val = 0) : u.val ⨯₃ (n.val ⨯₃ u.val) = n.val := by
      rw [cross_cross_eq_smul_sub_smul', show u.val ⬝ᵥ u.val = 1 from u.property, h,
        one_smul, zero_smul, sub_zero]
    rw [hx, undo p hnp]
    rcases hy with h | h
    · rw [h, undo q hnq, cross_self]
    · rw [h, map_neg, undo q hnq, map_neg, cross_self, neg_zero]

/-- Coordinates of a fixed Euclidean axis in the circle plane basis $(p₁,n×p₁)$. -/
def projectedAxis (v : Representative) (i : Fin 3) : Fin 2 → ℝ :=
  ![v.val.2.1.val i, (v.val.1.val ⨯₃ v.val.2.1.val) i]

private theorem projectedAxis_sq (v : Representative) (i : Fin 3) :
    projectedAxis v i ⬝ᵥ projectedAxis v i = 1 - v.val.1.val i ^ 2 := by
  let n := v.val.1.val
  let p := v.val.2.1.val
  have hn : n ⬝ᵥ n = 1 := v.val.1.property
  have hp : p ⬝ᵥ p = 1 := v.val.2.1.property
  have hnp : n ⬝ᵥ p = 0 := v.property.1
  have h : (n ⨯₃ p) i ^ 2 =
      (n ⬝ᵥ n) * (p ⬝ᵥ p) - (n ⬝ᵥ p)^2 - (n ⬝ᵥ n) * p i ^ 2 -
      (p ⬝ᵥ p) * n i ^ 2 + 2 * (n ⬝ᵥ p) * n i * p i := by
    fin_cases i <;> simp [cross_apply, dotProduct, Fin.sum_univ_three] <;> ring
  rw [hn, hp, hnp] at h
  change ![p i, (n ⨯₃ p) i] ⬝ᵥ ![p i, (n ⨯₃ p) i] = 1 - n i ^ 2
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith

/-- Every representative satisfies the five component and range identities of §5. -/
theorem frame (v : Representative) :
    let n := v.val.1.val
    let x := rangeFactorization forgetOrientation v
    n 0 ^ 2 + n 1 ^ 2 = weight x ∧ n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 ∧
      projectedAxis v 2 ⬝ᵥ projectedAxis v 2 = weight x ∧
      projectedAxis v 0 ⬝ᵥ projectedAxis v 0 ≤ 1 ∧
      v.val.2.1.val ⬝ᵥ v.val.2.2.val ∈ Icc (-1 : ℝ) 1 := by
  have hn : v.val.1.val ⬝ᵥ v.val.1.val = 1 := v.val.1.property
  simp only [dotProduct, Fin.sum_univ_three, ← sq] at hn
  have hw : weight (rangeFactorization forgetOrientation v) = 1 - v.val.1.val 2 ^ 2 := by
    simp [weight, rangeFactorization, forgetOrientation, vecMulVec_apply, sq]
  refine ⟨?_, hn, (projectedAxis_sq v 2).trans hw.symm, ?_, ?_⟩
  · rw [hw]; linarith
  · rw [projectedAxis_sq]; nlinarith [sq_nonneg (v.val.1.val 0)]
  · let p := v.val.2.1.val
    let q := v.val.2.2.val
    have hp : p ⬝ᵥ p = 1 := v.val.2.1.property
    have hq : q ⬝ᵥ q = 1 := v.val.2.2.property
    have nonneg (a : R3) : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)
    have hplus := nonneg (p + q)
    have hminus := nonneg (p - q)
    rw [add_dotProduct, dotProduct_add, dotProduct_add, hp, hq, dotProduct_comm q p] at hplus
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hp, hq, dotProduct_comm q p] at hminus
    change -1 ≤ p ⬝ᵥ q ∧ p ⬝ᵥ q ≤ 1
    constructor <;> linarith

/-- Choose the normal agreeing with the orientation of the regular pair.
At a singular pair either sign represents the same plane. -/
private theorem exists_oriented (x : Plane) :
    ∃ v : Representative, forgetOrientation v = x.val ∧
      0 ≤ v.val.1.val ⬝ᵥ (v.val.2.1.val ⨯₃ v.val.2.2.val) := by
  obtain ⟨v, hv⟩ := x.property
  by_cases h : 0 ≤ v.val.1.val ⬝ᵥ (v.val.2.1.val ⨯₃ v.val.2.2.val)
  · exact ⟨v, hv, h⟩
  · let n : UnitVector := ⟨-v.val.1.val, by
      change (-v.val.1.val) ⬝ᵥ (-v.val.1.val) = 1
      rw [neg_dotProduct, dotProduct_neg, neg_neg]
      exact v.val.1.property⟩
    let w : Representative := ⟨(n, v.val.2), by
      change (-_) ⬝ᵥ _ = 0 ∧ (-_) ⬝ᵥ _ = 0
      simp only [neg_dotProduct, v.property.1, v.property.2, neg_zero, and_self]⟩
    refine ⟨w, ?_, ?_⟩
    · rw [← hv]
      unfold forgetOrientation
      exact congrArg (Prod.mk (v.val.2.1.val, v.val.2.2.val))
        ((normal_line_eq n.property v.val.1.property).2 (Or.inr rfl))
    · change 0 ≤ (-v.val.1.val) ⬝ᵥ _
      rw [neg_dotProduct]
      exact neg_nonneg.mpr (le_of_not_ge h)

noncomputable def oriented (x : Plane) : Representative := (exists_oriented x).choose

theorem oriented_spec (x : Plane) : forgetOrientation (oriented x) = x.val ∧
    0 ≤ (oriented x).val.1.val ⬝ᵥ ((oriented x).val.2.1.val ⨯₃ (oriented x).val.2.2.val) :=
  (exists_oriented x).choose_spec

/-- Concrete values for all flat-locus fields of `LocalHopfInput`. -/
noncomputable def data : FlatLocusData where
  Z := Plane
  ρ := weight
  ρ_cont := continuous_weight
  ρ_nonneg := weight_nonneg
  Ω := regular
  Ω_dense := regular_dense
  Sig_dense := equator_dense
  nx := fun x => (oriented x).val.1.val 0
  ny := fun x => (oriented x).val.1.val 1
  nz := fun x => (oriented x).val.1.val 2
  xp := fun x => projectedAxis (oriented x) 0
  zp := fun x => projectedAxis (oriented x) 2
  sep := fun x => x.val.1.1 ⬝ᵥ x.val.1.2
  frame := by
    intro x _
    have h : rangeFactorization forgetOrientation (oriented x) = x :=
      Subtype.ext (oriented_spec x).1
    have sep := congrArg (fun v : Ambient => v.1.1 ⬝ᵥ v.1.2) (oriented_spec x).1
    have hf := frame (oriented x)
    dsimp only at hf sep
    rw [h] at hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, sep ▸ hf.2.2.2.2⟩

end LocalHopf.FlatLocus
