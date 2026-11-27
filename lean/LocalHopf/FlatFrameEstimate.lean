import LocalHopf.BackgroundGrowth

/-! # Comparison with an actual flat frame

The estimate is in the ambient coordinates of the base point and of an
orthonormal spanning frame, with an in-plane rotation, swap and sign allowed.
It includes coincident and antipodal sphere pairs.
-/
namespace LocalHopf.BackgroundGrowth
open Matrix
noncomputable section

private theorem sq_smul (r : ℝ) (a : R3) : sqLength (r • a) = r^2*sqLength a := by
  simp [sqLength,smul_dotProduct,dotProduct_smul,sq,mul_assoc]

private theorem sq_sub_comm (a b : R3) : sqLength (a-b) = sqLength (b-a) := by
  rw [← neg_sub b a,sqLength_neg]

private def unitize (a : R3) : R3 := (Real.sqrt (sqLength a))⁻¹ • a

private theorem unitize_spec (a : R3) (ha : 0 < sqLength a) (h1 : sqLength a ≤ 1) :
    sqLength (unitize a) = 1 ∧ Real.sqrt (sqLength a) • unitize a = a ∧
    sqLength (a-unitize a) ≤ 1-sqLength a := by
  let r := Real.sqrt (sqLength a)
  have hr : 0 < r := Real.sqrt_pos.mpr ha
  have hr2 : r^2 = sqLength a := Real.sq_sqrt ha.le
  have hr1 : r ≤ 1 := by nlinarith
  have hu : sqLength (unitize a) = 1 := by
    change sqLength (r⁻¹ • a) = 1
    rw [sq_smul,← hr2]
    field_simp
  have he : r • unitize a = a := by simp [r,unitize,smul_smul,hr.ne']
  refine ⟨hu,he,?_⟩
  have eq : a-unitize a = (r-1) • unitize a := by rw [sub_smul,one_smul,he]
  rw [eq,sq_smul,hu]
  nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr1)]

private theorem align (b d : R3) (hb : sqLength b = 1) (hd : sqLength d = 1) :
    ∃ e : ℝ, e^2 = 1 ∧ 0 ≤ b ⬝ᵥ (e • d) ∧ sqLength (b-e • d) ≤ 2*sqLength (b ⨯₃ d) := by
  have h := normals_estimate b d hb hd
  have diff : sqLength (b+d) - sqLength (b-d) = 4*(b ⬝ᵥ d) := by
    simp [sqLength,add_dotProduct,sub_dotProduct,dotProduct_add,dotProduct_sub,dotProduct_comm d b]
    ring
  by_cases hbd : 0 ≤ b ⬝ᵥ d
  · refine ⟨1,by norm_num,by simpa using hbd,?_⟩
    simpa [min_eq_left (show sqLength (b-d) ≤ sqLength (b+d) by linarith)] using h
  · refine ⟨-1,by norm_num,by simpa using (neg_nonneg.mpr (le_of_not_ge hbd)),?_⟩
    simpa [min_eq_right (show sqLength (b+d) ≤ sqLength (b-d) by linarith)] using h

private theorem cross_displacement (b d p q : R3) (hb : sqLength b = 1) (hp : sqLength p = 1) :
    sqLength (d ⨯₃ p - b ⨯₃ q) ≤ 2*sqLength (b-d) + 2*sqLength (q-p) := by
  have eq : d ⨯₃ p - b ⨯₃ q = (d-b) ⨯₃ p + b ⨯₃ (p-q) := by simp
  rw [eq]
  have h := sqLength_sum_le ((d-b) ⨯₃ p) (b ⨯₃ (p-q))
  have h₁ := sqLength_cross_le (d-b) p
  have h₂ := sqLength_cross_le b (p-q)
  rw [hp,mul_one,sq_sub_comm d b] at h₁
  rw [hb,one_mul,sq_sub_comm p q] at h₂
  linarith

private theorem oriented_estimate (p q : R3) (t : ℝ) (ht : 0 < t) (U V : R3 × R3)
    (hp : sqLength p = 1) (hq : sqLength q = 1) (hU : gprod U U = 1) (hV : gprod V V = 1)
    (hpu : p ⬝ᵥ U.1 = 0) (hqv : q ⬝ᵥ V.2 = 0)
    {ν : ℝ} (hν : zillerLower p q t U V = ν) (hsmall : ν ≤ 1/4)
    (hw : sqLength U.2 + sqLength V.1 ≤ 2*ν) :
    ∃ (b q' : R3) (e : ℝ), sqLength b = 1 ∧ b ⬝ᵥ p = 0 ∧ sqLength q' = 1 ∧ b ⬝ᵥ q' = 0 ∧
      e^2 = 1 ∧ sqLength (q'-q) + sqLength (U.1 - b ⨯₃ p) + sqLength U.2 + sqLength V.1 +
        sqLength (e • V.2 - b ⨯₃ q') ≤ (2000+1000/t^3)*ν := by
  change sqLength U.1 + sqLength U.2 = 1 at hU
  change sqLength V.1 + sqLength V.2 = 1 at hV
  have hU₂ := sqLength_nonneg U.2
  have hV₁ := sqLength_nonneg V.1
  have hu : 1/2 ≤ sqLength U.1 := by linarith
  have hv : 1/2 ≤ sqLength V.2 := by linarith
  let x := unitize U.1
  let y := unitize V.2
  obtain ⟨hx,ex,dx⟩ := unitize_spec U.1 (by linarith) (by linarith)
  obtain ⟨hy,ey,dy⟩ := unitize_spec V.2 (by linarith) (by linarith)
  have hpx : p ⬝ᵥ x = 0 := by simp [x,unitize,dotProduct_smul,hpu]
  have hqy : q ⬝ᵥ y = 0 := by simp [y,unitize,dotProduct_smul,hqv]
  let b := p ⨯₃ x
  let d := q ⨯₃ y
  have hb := (cross_unit p x hp hx hpx).1
  have hd := (cross_unit q y hq hy hqy).1
  have hbp : b ⬝ᵥ p = 0 := by rw [dotProduct_comm]; exact dot_self_cross p x
  have hdq : q ⬝ᵥ d = 0 := dot_self_cross q y
  have eb : b ⨯₃ p = x := by simp [b,cross_cross_eq_smul_sub_smul,show p ⬝ᵥ p = 1 from hp,hpx,dotProduct_comm x p]
  have ed : d ⨯₃ q = y := by simp [d,cross_cross_eq_smul_sub_smul,show q ⬝ᵥ q = 1 from hq,hqy,dotProduct_comm y q]
  have hc := normal_comparison p q U V hp hq hU hV
  have scale : sqLength ((p ⨯₃ U.1) ⨯₃ (q ⨯₃ V.2)) =
      (sqLength U.1 * sqLength V.2)*sqLength (b ⨯₃ d) := by
    conv_lhs => rw [← ex,← ey]
    simp [x,y,b,d,sq_smul,Real.sq_sqrt (sqLength_nonneg _),mul_assoc]
    ring
  rw [scale] at hc
  have hprod : 1/4 ≤ sqLength U.1 * sqLength V.2 := by
    nlinarith [mul_le_mul hu hv (by norm_num : (0:ℝ) ≤ 1/2) (sqLength_nonneg U.1)]
  have bracket : sqLength (moment p q U ⨯₃ moment p q V) ≤ 4*ν/t^3 := by
    apply (le_div_iff₀ (pow_pos ht 3)).mpr
    unfold zillerLower at hν
    linarith [sqLength_nonneg (U.1 ⨯₃ V.1),sqLength_nonneg (U.2 ⨯₃ V.2)]
  have hc' : sqLength (b ⨯₃ d) ≤ 32*ν/t^3+64*ν := by
    have hm := mul_le_mul_of_nonneg_right hprod (sqLength_nonneg (b ⨯₃ d))
    ring_nf at hm hc bracket ⊢
    linarith only [hm,hc,bracket,hw,hV₁]
  obtain ⟨e,he,hbd,dist⟩ := align b d hb hd
  let q' := transported b (e • d) q
  have hd' : sqLength (e • d) = 1 := by rw [sq_smul,he,show sqLength d=1 from hd,mul_one]
  have hqd' : q ⬝ᵥ (e • d) = 0 := by simp [dotProduct_smul,hdq]
  obtain ⟨hq',perp⟩ := transported_unit_perp b _ q hb hd' hq hqd' hbd
  have base := transported_displacement b _ q hb hd' hq hqd' hbd
  change sqLength (q'-q) ≤ _ at base
  have hyy := cross_displacement b (e • d) q q' hb hq
  have ey' : (e • d) ⨯₃ q = e • y := by simp [ed]
  rw [ey'] at hyy
  have err := sqLength_sum_le (e • (V.2-y)) (e • y - b ⨯₃ q')
  rw [smul_sub,sub_add_sub_cancel] at err
  rw [← smul_sub,sq_smul,he,one_mul] at err
  refine ⟨b,q',e,hb,hbp,hq',by rwa [dotProduct_comm],he,?_⟩
  rw [eb]
  change sqLength (U.1-x) ≤ _ at dx
  change sqLength (V.2-y) ≤ _ at dy
  have hνpos : 0 ≤ ν := by linarith
  have htpos : 0 ≤ ν/t^3 := by positivity
  ring_nf at hc' htpos ⊢
  linarith

/-- Order an adapted basis so the two small components are in opposite factors. -/
theorem ordered_adapted (p q : R3) (t : ℝ) (ht : 0 ≤ t) (X Y : R3 × R3)
    (hx : gprod X X = 1) (hy : gprod Y Y = 1) (hxy : gprod X Y = 0)
    (hpx : p ⬝ᵥ X.1 = 0) (hpy : p ⬝ᵥ Y.1 = 0) (hqx : q ⬝ᵥ X.2 = 0) (hqy : q ⬝ᵥ Y.2 = 0) :
    ∃ (θ : ℝ) (U V : R3 × R3), ((U,V) = rotatePair X Y θ ∨ (V,U) = rotatePair X Y θ) ∧
      U.1 ⬝ᵥ V.1 = 0 ∧ U.2 ⬝ᵥ V.2 = 0 ∧ gprod U U = 1 ∧ gprod V V = 1 ∧
      p ⬝ᵥ U.1 = 0 ∧ p ⬝ᵥ V.1 = 0 ∧ q ⬝ᵥ U.2 = 0 ∧ q ⬝ᵥ V.2 = 0 ∧
      zillerLower p q t U V = zillerLower p q t X Y ∧
      sqLength U.2 + sqLength V.1 ≤ 2*zillerLower p q t X Y := by
  obtain ⟨θ,h₁,h₂,hu,hv⟩ := exists_adapted_angle X Y hxy hx hy
  let U := (rotatePair X Y θ).1
  let V := (rotatePair X Y θ).2
  have rot : zillerLower p q t U V = zillerLower p q t X Y := rotate_lower ..
  have hw := adapted_component_estimate U V hu hv h₁ h₂
  have hm : min (sqLength U.2+sqLength V.1) (sqLength U.1+sqLength V.2) ≤ 2*zillerLower p q t X Y := by
    rw [← rot]
    unfold zillerLower
    linarith [mul_nonneg (by positivity : 0 ≤ t^3/4) (sqLength_nonneg (moment p q U ⨯₃ moment p q V))]
  have tan : (p ⬝ᵥ U.1 = 0 ∧ q ⬝ᵥ V.2 = 0) ∧ (p ⬝ᵥ V.1 = 0 ∧ q ⬝ᵥ U.2 = 0) := by
    simp [U,V,rotatePair,dotProduct_add,dotProduct_smul,hpx,hpy,hqx,hqy]
  rcases min_le_iff.mp hm with h | h
  · exact ⟨θ,U,V,Or.inl rfl,h₁,h₂,hu,hv,tan.1.1,tan.2.1,tan.2.2,tan.1.2,rot,h⟩
  · have swap (a b : R3) : sqLength (b ⨯₃ a) = sqLength (a ⨯₃ b) := by
      rw [← cross_anticomm a b,sqLength_neg]
    have eq : zillerLower p q t V U = zillerLower p q t X Y := by
      rw [← rot]
      simp only [zillerLower,swap U.1 V.1,swap U.2 V.2,swap (moment p q U) (moment p q V)]
    exact ⟨θ,V,U,Or.inr rfl,(dotProduct_comm _ _).trans h₁,(dotProduct_comm _ _).trans h₂,
      hv,hu,tan.2.1,tan.1.1,tan.1.2,tan.2.2,eq,by rwa [add_comm]⟩

/-- The algebraic lower side of (Z) bounds the squared displacement to a
common-normal mixed frame, including over the coincident and antipodal pairs.
The two generators can be rotated, interchanged and oriented within their plane. -/
theorem exists_flat_frame (p q : R3) (t : ℝ) (ht : 0 < t) (X Y : R3 × R3)
    (hp : sqLength p = 1) (hq : sqLength q = 1) (hx : gprod X X = 1) (hy : gprod Y Y = 1)
    (hxy : gprod X Y = 0) (hpx : p ⬝ᵥ X.1 = 0) (hpy : p ⬝ᵥ Y.1 = 0)
    (hqx : q ⬝ᵥ X.2 = 0) (hqy : q ⬝ᵥ Y.2 = 0) (hsmall : zillerLower p q t X Y ≤ 1/4) :
    ∃ (θ : ℝ) (U V : R3 × R3), ((U,V) = rotatePair X Y θ ∨ (V,U) = rotatePair X Y θ) ∧
      ∃ (b q' : R3) (e : ℝ), sqLength b = 1 ∧ b ⬝ᵥ p = 0 ∧ sqLength q' = 1 ∧ b ⬝ᵥ q' = 0 ∧
        e^2 = 1 ∧ sqLength (q'-q) + sqLength (U.1 - b ⨯₃ p) + sqLength U.2 + sqLength V.1 +
          sqLength (e • V.2 - b ⨯₃ q') ≤ (2000+1000/t^3)*zillerLower p q t X Y := by
  obtain ⟨θ,U,V,rot,_,_,hU,hV,pU,_,_,qV,eq,small⟩ :=
    ordered_adapted p q t ht.le X Y hx hy hxy hpx hpy hqx hqy
  exact ⟨θ,U,V,rot,oriented_estimate p q t ht U V hp hq hU hV pU qV eq hsmall small⟩

end
end LocalHopf.BackgroundGrowth
