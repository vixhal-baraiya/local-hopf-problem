import LocalHopf.Vectors
import LocalHopf.FlatLocus

/-! # The algebraic estimates in Lemma 4.1

The three squared cross products are the lower side of (Z). In the mixed case
they control the misalignment of the two great-circle normals, with an explicit
constant even over coincident and antipodal sphere points.
-/
namespace LocalHopf.BackgroundGrowth
open Matrix
noncomputable section

def sqLength (a : R3) : ℝ := a ⬝ᵥ a

theorem sqLength_nonneg (a : R3) : 0 ≤ sqLength a :=
  by unfold sqLength dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

/-- The explicit lower side of the Müter–Ziller curvature inequality (Z). -/
def zillerLower (p q : R3) (t : ℝ) (X Y : R3 × R3) : ℝ :=
  sqLength (X.1 ⨯₃ Y.1) + sqLength (X.2 ⨯₃ Y.2) +
    t^3/4 * sqLength (moment p q X ⨯₃ moment p q Y)

/-- Small curvature on the right of (Z) bounds both component areas and the bracket. -/
theorem component_bounds {p q : R3} {t ε : ℝ} {X Y : R3 × R3} (ht : 0 < t)
    (h : zillerLower p q t X Y ≤ ε^2) :
    sqLength (X.1 ⨯₃ Y.1) ≤ ε^2 ∧ sqLength (X.2 ⨯₃ Y.2) ≤ ε^2 ∧
    sqLength (moment p q X ⨯₃ moment p q Y) ≤ 4 * ε^2 / t^3 := by
  unfold zillerLower at h
  have hx := sqLength_nonneg (X.1 ⨯₃ Y.1)
  have hy := sqLength_nonneg (X.2 ⨯₃ Y.2)
  have hm := mul_nonneg (by positivity : 0 ≤ t^3/4) (sqLength_nonneg (moment p q X ⨯₃ moment p q Y))
  refine ⟨by linarith, by linarith, (le_div_iff₀ (pow_pos ht 3)).2 ?_⟩
  linarith

/-- The nearer of the two signs of a unit normal is controlled by the cross product. -/
theorem normals_estimate (b c : R3) (hb : sqLength b = 1) (hc : sqLength c = 1) :
    min (sqLength (b-c)) (sqLength (b+c)) ≤ 2 * sqLength (b ⨯₃ c) := by
  unfold sqLength at *
  rw [cross_dot_cross, hb, hc, dotProduct_comm c b, sub_dotProduct, add_dotProduct,
    dotProduct_sub, dotProduct_sub, dotProduct_add, dotProduct_add, hb, hc, dotProduct_comm c b]
  have hx := sqLength_nonneg (b ⨯₃ c)
  unfold sqLength at hx
  rw [cross_dot_cross, hb, hc, dotProduct_comm c b] at hx
  by_cases s : 0 ≤ b ⬝ᵥ c
  · apply le_trans (min_le_left ..)
    nlinarith [mul_nonneg s (show 0 ≤ 1 - b ⬝ᵥ c by nlinarith)]
  · apply le_trans (min_le_right ..)
    nlinarith [mul_nonneg (show 0 ≤ -(b ⬝ᵥ c) by linarith) (show 0 ≤ 1 + b ⬝ᵥ c by nlinarith)]

/-- On a product-mixed unit plane only the group-bracket penalty survives.
It bounds squared distance between the two normal lines with stiffness `t³/8`. -/
theorem mixed_growth (p q x y : R3) (t : ℝ) (ht : 0 ≤ t)
    (hp : sqLength p = 1) (hq : sqLength q = 1) (hx : sqLength x = 1)
    (hy : sqLength y = 1) (hpx : p ⬝ᵥ x = 0) (hqy : q ⬝ᵥ y = 0) :
    let b := p ⨯₃ x
    let c := q ⨯₃ y
    t^3/8 * min (sqLength (b-c)) (sqLength (b+c)) ≤ zillerLower p q t (x,0) (0,y) := by
  dsimp only
  have hb : sqLength (p ⨯₃ x) = 1 := by
    unfold sqLength at *
    rw [cross_dot_cross, hp, hx, hpx]; ring
  have hc : sqLength (q ⨯₃ y) = 1 := by
    unfold sqLength at *
    rw [cross_dot_cross, hq, hy, hqy]; ring
  have h := mul_le_mul_of_nonneg_left (normals_estimate _ _ hb hc) (by positivity : 0 ≤ t^3/8)
  have he : zillerLower p q t (x,0) (0,y) = t^3/4 * sqLength ((p ⨯₃ x) ⨯₃ (q ⨯₃ y)) := by
    simp [zillerLower, moment, sqLength]
  rw [he]
  linarith

/-- Move the second sphere point into the great circle perpendicular to `b`.
The formula remains regular when the two oriented normals agree. -/
def transported (b c q : R3) := q - ((q ⬝ᵥ b)/(1+b ⬝ᵥ c)) • (b+c)

theorem transported_unit_perp (b c q : R3) (hb : sqLength b = 1) (hc : sqLength c = 1)
    (hq : sqLength q = 1) (hqc : q ⬝ᵥ c = 0) (hbc : 0 ≤ b ⬝ᵥ c) :
    sqLength (transported b c q) = 1 ∧ transported b c q ⬝ᵥ b = 0 := by
  have hd : 1+b ⬝ᵥ c ≠ 0 := by linarith
  unfold transported sqLength at *
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, add_dotProduct,
    dotProduct_add, smul_eq_mul, hb, hc, hq, hqc, dotProduct_comm c q, dotProduct_comm b q,
    dotProduct_comm c b]
  constructor <;> field_simp <;> ring

/-- Squared displacement of the base point under the comparison in Lemma 4.1. -/
theorem transported_displacement (b c q : R3) (hb : sqLength b = 1) (hc : sqLength c = 1)
    (hq : sqLength q = 1) (hqc : q ⬝ᵥ c = 0) (hbc : 0 ≤ b ⬝ᵥ c) :
    sqLength (transported b c q - q) ≤ 2 * sqLength (b-c) := by
  have hd : 0 < 1+b ⬝ᵥ c := by linarith
  have h := sqLength_nonneg (q ⨯₃ (b-c))
  change 0 ≤ (q ⨯₃ (b-c)) ⬝ᵥ (q ⨯₃ (b-c)) at h
  rw [cross_dot_cross, dotProduct_comm (b-c) q, dotProduct_sub q, hqc, sub_zero] at h
  change q ⬝ᵥ q = 1 at hq
  rw [hq, one_mul] at h
  have hs : sqLength (b+c) = 2*(1+b ⬝ᵥ c) := by
    unfold sqLength at *
    rw [add_dotProduct, dotProduct_add, dotProduct_add, hb, hc, dotProduct_comm c b]; ring
  have he : sqLength (transported b c q - q) = (q ⬝ᵥ b/(1+b ⬝ᵥ c))^2 * sqLength (b+c) := by
    rw [transported, sub_sub_cancel_left]
    simp [sqLength, smul_dotProduct, dotProduct_smul, sq, mul_assoc]
    ring
  rw [he, hs]
  have he' : (q ⬝ᵥ b/(1+b ⬝ᵥ c))^2 * (2*(1+b ⬝ᵥ c)) = 2*(q ⬝ᵥ b)^2/(1+b ⬝ᵥ c) := by
    field_simp
  rw [he', div_le_iff₀ hd]
  change 0 ≤ sqLength (b-c) - _ at h
  nlinarith [mul_nonneg hbc (sqLength_nonneg (b-c))]


/-- Rotate the two spanning vectors in their own plane. -/
def rotatePair (X Y : R3 × R3) (θ : ℝ) : (R3 × R3) × (R3 × R3) :=
  (Real.cos θ • X + Real.sin θ • Y, -(Real.sin θ) • X + Real.cos θ • Y)

private theorem rot_cross (a b : R3) (θ : ℝ) :
    (Real.cos θ • a + Real.sin θ • b) ⨯₃ (-(Real.sin θ) • a + Real.cos θ • b) = a ⨯₃ b := by
  have H : Real.cos θ^2 + Real.sin θ^2 = 1 := by linarith [Real.sin_sq_add_cos_sq θ]
  have bilinear (c s : ℝ) :
      (c • a + s • b) ⨯₃ (-s • a + c • b) = (c^2+s^2) • (a ⨯₃ b) := by
    ext i
    fin_cases i <;> simp [cross_apply] <;> ring
  rw [bilinear, H, one_smul]

/-- All three curvature penalties survive the in-plane basis change unchanged. -/
theorem rotate_lower (p q : R3) (t : ℝ) (X Y : R3 × R3) (θ : ℝ) :
    zillerLower p q t (rotatePair X Y θ).1 (rotatePair X Y θ).2 = zillerLower p q t X Y := by
  have hm (a b : ℝ) : moment p q (a • X + b • Y) = a • moment p q X + b • moment p q Y := by
    simp [moment, smul_add, add_add_add_comm]
  simp only [zillerLower, rotatePair, hm, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    rot_cross]

/-- Every orthogonal pair admits an in-plane rotation that makes the projections
orthogonal in each factor. This uses a zero of a continuous function of the angle. -/
theorem exists_adapted_angle (X Y : R3 × R3) (hxy : gprod X Y = 0)
    (hx : gprod X X = 1) (hy : gprod Y Y = 1) :
    ∃ θ : ℝ, let (U,V) := rotatePair X Y θ
      U.1 ⬝ᵥ V.1 = 0 ∧ U.2 ⬝ᵥ V.2 = 0 ∧ gprod U U = 1 ∧ gprod V V = 1 := by
  let f (θ : ℝ) := (rotatePair X Y θ).1.1 ⬝ᵥ (rotatePair X Y θ).2.1
  have hf : Continuous f := by unfold f rotatePair; fun_prop
  have f0 : f 0 = X.1 ⬝ᵥ Y.1 := by simp [f, rotatePair]
  have fπ : f (Real.pi/2) = -(X.1 ⬝ᵥ Y.1) := by simp [f, rotatePair, dotProduct_comm Y.1 X.1]
  have hex : ∃ θ, f θ = 0 := by
    have hab : (0:ℝ) ≤ Real.pi/2 := by positivity
    by_cases sign : 0 ≤ X.1 ⬝ᵥ Y.1
    · obtain ⟨θ,_,h⟩ := intermediate_value_Icc' hab hf.continuousOn
          (show (0:ℝ) ∈ Set.Icc (f (Real.pi/2)) (f 0) by rw [fπ,f0]; exact ⟨neg_nonpos.mpr sign,sign⟩)
      exact ⟨θ,h⟩
    · obtain ⟨θ,_,h⟩ := intermediate_value_Icc hab hf.continuousOn
          (show (0:ℝ) ∈ Set.Icc (f 0) (f (Real.pi/2)) by rw [fπ,f0]; exact ⟨le_of_not_ge sign, neg_nonneg.mpr (le_of_not_ge sign)⟩)
      exact ⟨θ,h⟩
  obtain ⟨θ,hθ⟩ := hex
  refine ⟨θ,hθ,?_⟩
  unfold f rotatePair at hθ
  unfold gprod at *
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm Y.1 X.1, dotProduct_comm Y.2 X.2] at *
  obtain ⟨e₁,e₂,e₃⟩ : X.2 ⬝ᵥ X.2 = 1-X.1 ⬝ᵥ X.1 ∧ Y.2 ⬝ᵥ Y.2 = 1-Y.1 ⬝ᵥ Y.1 ∧
      X.2 ⬝ᵥ Y.2 = -(X.1 ⬝ᵥ Y.1) := ⟨by linarith,by linarith,by linarith⟩
  rw [e₁,e₂,e₃]
  constructor
  · linear_combination -hθ
  · constructor <;> linear_combination Real.sin_sq_add_cos_sq θ

/-- In an adapted unit frame, after taking the better ordering, squared length in
the two unwanted factors is at most twice the background component-area penalty. -/
theorem adapted_component_estimate (X Y : R3 × R3)
    (hx : gprod X X = 1) (hy : gprod Y Y = 1) (h₁ : X.1 ⬝ᵥ Y.1 = 0) (h₂ : X.2 ⬝ᵥ Y.2 = 0) :
    min (sqLength X.2 + sqLength Y.1) (sqLength X.1 + sqLength Y.2) ≤
      2 * (sqLength (X.1 ⨯₃ Y.1) + sqLength (X.2 ⨯₃ Y.2)) := by
  let a := sqLength X.1
  let b := sqLength Y.1
  have hx' : sqLength X.2 = 1-a := by change a + sqLength X.2 = 1 at hx; linarith
  have hy' : sqLength Y.2 = 1-b := by change b + sqLength Y.2 = 1 at hy; linarith
  have cross (u v : R3) (h : u ⬝ᵥ v = 0) : sqLength (u ⨯₃ v) = sqLength u*sqLength v := by
    simp [sqLength, cross_dot_cross, h]
  rw [cross _ _ h₁, cross _ _ h₂, hx', hy']
  change min (1-a+b) (a+(1-b)) ≤ 2*(a*b+(1-a)*(1-b))
  have ha : 0 ≤ a := sqLength_nonneg _
  have hb : 0 ≤ b := sqLength_nonneg _
  have ha' : 0 ≤ 1-a := hx' ▸ sqLength_nonneg _
  have hb' : 0 ≤ 1-b := hy' ▸ sqLength_nonneg _
  by_cases h : b ≤ a
  · apply (min_le_left ..).trans
    nlinarith [sq_nonneg (a+b-1), mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 1-(a-b) by linarith)]
  · apply (min_le_right ..).trans
    nlinarith [sq_nonneg (a+b-1), mul_nonneg (show 0 ≤ b-a by linarith) (show 0 ≤ 1-(b-a) by linarith)]


/-- The component-area estimate on an arbitrary round orthonormal frame after
an in-plane rotation. No lower bound on `t` is needed for this part. -/
theorem exists_adapted_estimate (p q : R3) (t : ℝ) (ht : 0 ≤ t) (X Y : R3 × R3)
    (hx : gprod X X = 1) (hy : gprod Y Y = 1) (hxy : gprod X Y = 0) :
    ∃ θ : ℝ, let (U,V) := rotatePair X Y θ
      min (sqLength U.2 + sqLength V.1) (sqLength U.1 + sqLength V.2) ≤ 2*zillerLower p q t X Y := by
  obtain ⟨θ,h₁,h₂,hu,hv⟩ := exists_adapted_angle X Y hxy hx hy
  let U := (rotatePair X Y θ).1
  let V := (rotatePair X Y θ).2
  refine ⟨θ,?_⟩
  rw [← rotate_lower p q t X Y θ]
  apply (adapted_component_estimate U V hu hv h₁ h₂).trans
  change _ ≤ 2*(sqLength (U.1 ⨯₃ V.1) + sqLength (U.2 ⨯₃ V.2) + _)
  linarith [mul_nonneg (by positivity : 0 ≤ t^3/4) (sqLength_nonneg (moment p q U ⨯₃ moment p q V))]

theorem sqLength_cross_le (a b : R3) : sqLength (a ⨯₃ b) ≤ sqLength a * sqLength b := by
  unfold sqLength
  rw [cross_dot_cross, dotProduct_comm b a]
  nlinarith [sq_nonneg (a ⬝ᵥ b)]

theorem sqLength_sum_le (a b : R3) : sqLength (a+b) ≤ 2*(sqLength a + sqLength b) := by
  have h := sqLength_nonneg (a-b)
  unfold sqLength at *
  simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add, dotProduct_comm b a] at *
  linarith

theorem sqLength_neg (a : R3) : sqLength (-a) = sqLength a := by simp [sqLength]

/-- For a frame near a mixed plane, control the cross product of the two
unnormalized great-circle normals by the moment penalty and the two unwanted
components. This supplies the comparison in step 3 of Lemma 4.1 before normalization. -/
theorem normal_comparison (p q : R3) (X Y : R3 × R3)
    (hp : sqLength p = 1) (hq : sqLength q = 1) (hx : gprod X X = 1) (hy : gprod Y Y = 1) :
    sqLength ((p ⨯₃ X.1) ⨯₃ (q ⨯₃ Y.2)) ≤ 2*sqLength (moment p q X ⨯₃ moment p q Y) +
      4*sqLength Y.1 + 8*sqLength X.2 := by
  let a := p ⨯₃ X.1
  let b := q ⨯₃ Y.2
  let c := q ⨯₃ X.2
  let d := p ⨯₃ Y.1
  let m := moment p q Y
  have hunit (v w : R3) (h : sqLength v = 1) : sqLength (v ⨯₃ w) ≤ sqLength w := by
    simpa only [h, one_mul] using sqLength_cross_le v w
  have ha : sqLength a ≤ 1 := by
    apply (hunit _ _ hp).trans
    change sqLength X.1 + sqLength X.2 = 1 at hx
    linarith [sqLength_nonneg X.2]
  have hm : sqLength m ≤ 2 := by
    have H := sqLength_sum_le d b
    change sqLength Y.1 + sqLength Y.2 = 1 at hy
    change sqLength (d+b) ≤ 2
    have hd : sqLength d ≤ sqLength Y.1 := hunit p Y.1 hp
    have hb : sqLength b ≤ sqLength Y.2 := hunit q Y.2 hq
    linarith
  have he : a ⨯₃ b = moment p q X ⨯₃ m + -((a ⨯₃ d) + (c ⨯₃ m)) := by
    change a ⨯₃ b = (a+c) ⨯₃ (d+b) + -((a ⨯₃ d) + (c ⨯₃ (d+b)))
    simp only [map_add, LinearMap.add_apply]
    abel
  have h₁ : sqLength (a ⨯₃ d) ≤ sqLength Y.1 := calc
    _ ≤ sqLength a * sqLength d := sqLength_cross_le _ _
    _ ≤ 1 * sqLength d := mul_le_mul_of_nonneg_right ha (sqLength_nonneg _)
    _ ≤ _ := by simpa using hunit p Y.1 hp
  have h₂ : sqLength (c ⨯₃ m) ≤ sqLength X.2 * 2 :=
    (sqLength_cross_le _ _).trans (mul_le_mul (hunit q X.2 hq) hm (sqLength_nonneg _) (sqLength_nonneg _))
  change sqLength (a ⨯₃ b) ≤ 2*sqLength (moment p q X ⨯₃ m) + 4*sqLength Y.1 + 8*sqLength X.2
  rw [he]
  apply (sqLength_sum_le _ _).trans
  rw [sqLength_neg]
  linarith [sqLength_sum_le (a ⨯₃ d) (c ⨯₃ m)]


end
end LocalHopf.BackgroundGrowth
