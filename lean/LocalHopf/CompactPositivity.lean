import LocalHopf.FarCover
import LocalHopf.FrameRegularity

/-! Regularity of intrinsic curvature on the two concrete pieces of the plane cover. -/
namespace LocalHopf.BackgroundGrowth.Transverse
open SphereProduct JetChart Filter Set Real Matrix Metric
open scoped Topology ContDiff
noncomputable section

/-- The actual numerator is smooth jointly in the core, the four transverse
parameters and the metric parameter throughout one uniform compact disk. -/
theorem compact_curvature_regular (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) :
    ∃ η > 0, ∀ q ∈ UniformTube.disk (E := Tilts) (compactNormalChart t).core (compactNormalChart t).radius η,
      ContDiffAt ℝ ∞ ((compactNormalChart t).curvature (paperCoefficients t ht χ)) q := by
  obtain ⟨δ,hδ,win⟩ := Metric.eventually_nhds_iff.mp (paper_metrics_realize t ht χ)
  refine ⟨δ/2,by positivity,?_⟩
  intro q hq
  obtain ⟨v,hv⟩ := hq.1
  have val : validCore q.1 := hv ▸ (core_fixed v).2
  have bound : ‖q.2.1‖ ≤ 1/2 := by
    have b : dist q.2.1 0 ≤ 1/2 := hq.2.1
    simpa only [dist_zero_right] using b
  have small (i : Fin 4) : |q.2.1 i| < 1 := (norm_le_pi_norm q.2.1 i).trans_lt (lt_of_le_of_lt bound (by norm_num))
  have inside : q.2.2 ∈ ball 0 δ := by
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hq.2.2.1]
    linarith [hq.2.2.2]
  have window : ∀ᶠ s in 𝓝 q.2.2, ∃ g : SmoothMetric, Realizes g s (paperCoefficients t ht χ) := by
    filter_upwards [isOpen_ball.mem_nhds inside] with h hh using win hh
  let f := fun q : CoreParameters × Tilts × ℝ => (q.1,q.2.1)
  have reg : ContDiffAt ℝ ∞ f q := by unfold f; fun_prop
  have cs : ContDiffAt ℝ ∞ ((frameData ∘ (compactNormalChart t).frame) ∘ f) q := (compact_chart_smooth t val small).comp (f := f) q reg
  exact moving_numerator_smooth (w := (compactNormalChart t).frame ∘ f) (h := fun z => z.2.2) window
    cs (contDiffAt_snd.comp q contDiffAt_snd)

/-- Continuous dependence of the prescribed curvature on the complementary
compact family, including the boundary of the far region. -/
theorem far_curvature_continuous (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) (w₀ : ↥(farSet t)) :
    ContinuousAt (fun q : ↥(farSet t) × ℝ => (farPair t q.1).numerator (paperCoefficients t ht χ) q.2) (w₀,0) := by
  have lift : Continuous (fun w : ↥(farSet t) => frameData (farPair t w)) := by
    let P := fun w : ↥(farSet t) => w.val.1.1.val
    let Q := fun w : ↥(farSet t) => w.val.1.2.val
    have pc : Continuous P := by unfold P; fun_prop
    have qc : Continuous Q := by unfold Q; fun_prop
    have cross {f g : ↥(farSet t) → R3} (a : Continuous f) (b : Continuous g) :
        Continuous (fun w => f w ⨯₃ g w) := Cheeger.smooth_cross.continuous.comp (a.prodMk b)
    have inv {Z : ↥(farSet t) → Cheeger.V} (z : Continuous Z) :
        Continuous (fun w => Cheeger.inverseOperator (P w) (Q w) t (Z w)) := by
      have m := (cross pc (continuous_fst.comp z)).add (cross qc (continuous_snd.comp z))
      have tc : Continuous (fun _ : ↥(farSet t) => t) := continuous_const
      exact ((continuous_fst.comp z).add (tc.smul (cross m pc))).prodMk
        ((continuous_snd.comp z).add (tc.smul (cross m qc)))
    have e (w : ↥(farSet t)) : frameData (farPair t w) =
        ((P w,Q w),Cheeger.inverseOperator (P w) (Q w) t w.val.2.1,Cheeger.inverseOperator (P w) (Q w) t w.val.2.2) :=
      congrArg (fun q : FrameCoordinates => (ambientPoint q.1,q.2)) (farPair_ambient t w)
    simp only [e]
    exact (pc.prodMk qc).prodMk ((inv (Z := fun w => w.val.2.1) (by fun_prop)).prodMk
      (inv (Z := fun w => w.val.2.2) (by fun_prop)))
  exact moving_numerator_continuous (w := fun q : ↥(farSet t) × ℝ => farPair t q.1) (h := Prod.snd)
    (paper_metrics_realize t ht χ) (lift.comp continuous_fst).continuousAt continuous_snd.continuousAt

/-- Inequality (Z) on genuine tangent vectors, with the factor two coming from
the paper's convention (g_t=g_{\rm CM,t}/2). -/
def backgroundComparison (t : ℝ) (ht : 0 ≤ t) : Prop :=
  ∀ (w : TangentPair) (P Q : R3) (X Y : Cheeger.V),
    frameData w = ((P,Q),Cheeger.inverseOperator P Q t X,Cheeger.inverseOperator P Q t Y) →
    zillerLower P Q t X Y ≤ 2*curvatureNumerator (backgroundMetric t ht) w.point w.first w.second

theorem background_zero (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) :
    Realizes (backgroundMetric t ht) 0 (paperCoefficients t ht χ) := by
  intro p X Y
  simp only [cubicValue,zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 3 ≠ 0),zero_smul,add_zero]
  rfl

theorem norm_sq_le_sum (z : Tilts) : ‖z‖^2 ≤ z 0^2+z 1^2+z 2^2+z 3^2 := by
  let S := z 0^2+z 1^2+z 2^2+z 3^2
  have hs : 0 ≤ S := by unfold S; positivity
  have b : ‖z‖ ≤ sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (sqrt_nonneg S)).mpr
    intro i
    rw [Real.norm_eq_abs,← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    fin_cases i <;> dsimp [S] <;> nlinarith [sq_nonneg (z 0),sq_nonneg (z 1),sq_nonneg (z 2),sq_nonneg (z 3)]
  exact (pow_le_pow_left₀ (norm_nonneg _) b 2).trans_eq (sq_sqrt hs)

/-- A single intrinsic background comparison gives both the quadratic lower
bound on the entire normal disk and strict positivity on the closed far region. -/
theorem comparison_bounds (t : ℝ) (ht : 0<t) (χ : Scalar) (Z : backgroundComparison t ht.le) :
    (∀ x ∈ (compactNormalChart t).core, ∀ z : Tilts, ‖z‖ ≤ (compactNormalChart t).radius →
      (2*(66+32/t^3))⁻¹*‖z‖^2 ≤ (compactNormalChart t).curvature (paperCoefficients t ht.le χ) (x,z,0)) ∧
    ∀ w : ↥(farSet t), 0 < (farPair t w).numerator (paperCoefficients t ht.le χ) 0 := by
  let C := 66+32/t^3
  have hc : 0<C := by unfold C; positivity
  have bg := background_zero t ht.le χ
  constructor
  · rintro x ⟨v,rfl⟩ z hz
    let n := v.val.1.val
    let P := v.val.2.1.val
    let Q := point n v.val.2.2.val (z 2)
    let M := normal n v.val.2.2.val (z 2) (z 3)
    let F := frame P Q n M (z 0) (z 1)
    let w := (compactNormalChart t).frame (rawCore v,z)
    have half (i : Fin 4) : |z i| ≤ 1/2 := (norm_le_pi_norm z i).trans hz
    have small (i : Fin 4) : |z i| < 1 := (half i).trans_lt (by norm_num)
    have h := Z w P Q F.1 F.2 (core_frame_data t v small)
    have raw := growth v ht (half 0) (half 1) (small 2).le (small 3).le
    change _ ≤ C*zillerLower P Q t F.1 F.2 at raw
    change (2*C)⁻¹*‖z‖^2 ≤ w.numerator _ 0
    rw [w.numerator_eq bg,← div_eq_inv_mul]
    apply (div_le_iff₀ (mul_pos (by norm_num) hc)).mpr
    calc
      _ ≤ C*zillerLower P Q t F.1 F.2 := (norm_sq_le_sum z).trans raw
      _ ≤ C*(2*_) := mul_le_mul_of_nonneg_left h hc.le
      _ = _ := by ring
  · intro w
    have e : frameData (farPair t w) = ((w.val.1.1.val,w.val.1.2.val),
        Cheeger.inverseOperator _ _ t w.val.2.1,Cheeger.inverseOperator _ _ t w.val.2.2) :=
      congrArg (fun q : FrameCoordinates => (ambientPoint q.1,q.2)) (farPair_ambient t w)
    have h := Z _ _ _ _ _ e
    have f : 1/4 ≤ C*zillerLower w.val.1.1.val w.val.1.2.val t w.val.2.1 w.val.2.2 := w.property.2.2.2.2.2
    have pos := pos_of_mul_pos_right (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) f) hc.le
    rw [TangentPair.numerator_eq _ bg]
    linarith


/-- The intrinsic minimum on every transverse disk has one uniform cubic
expansion. Only the intrinsic background comparison is needed at this stage. -/
theorem compact_minimum_expansion (t : ℝ) (ht : 0<t) (χ : Scalar) (Z : backgroundComparison t ht.le) :
    let c := compactNormalChart t
    let F := c.curvature (paperCoefficients t ht.le χ)
    ∃ center : CoreParameters → Tilts, ContinuousOn center c.core ∧
      (∀ x ∈ c.core, ∀ a, UniformTube.coeff F 2 x (center x) +
        ((2*(66+32/t^3))⁻¹/2)*‖a-center x‖^2 ≤ UniformTube.coeff F 2 x a) ∧
      ∃ C ≥ 0, ∃ ε > 0, ∀ x ∈ c.core, ∀ s ∈ Ioo 0 ε,
        let value := s^2*UniformTube.coeff F 2 x (center x) + s^3*UniformTube.coeff F 3 x (center x)
        (∀ z : Tilts, ‖z‖ ≤ c.radius → value-C*s^4 ≤ F (x,z,s)) ∧
        ∃ m ∈ closedBall (0:Tilts) c.radius, IsMinOn (fun z => F (x,z,s)) (closedBall 0 c.radius) m ∧
          |F (x,m,s)-value| ≤ C*s^4 := by
  intro c F
  obtain ⟨η,hη,reg⟩ := compact_curvature_regular t ht.le χ
  exact UniformTube.minimum_expansion F c.compact c.radius_pos hη (by positivity)
    (fun q hq => (reg q hq).of_le (by simp)) (fun _ h => (compact_chart_core_jet t ht.le χ h).1)
    (comparison_bounds t ht χ Z).1 (fun _ h => (compact_chart_core_jet t ht.le χ h).2.deriv)


end
end LocalHopf.BackgroundGrowth.Transverse
