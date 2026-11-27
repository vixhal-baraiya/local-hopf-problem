import LocalHopf.BackgroundContraction
import LocalHopf.FrameCertificate

/-! Reduction of the concrete sphere-product problem using the background
metric calculation and two intrinsic coefficient identities on the regular locus. -/
namespace LocalHopf.BackgroundGrowth.Transverse
open Set Filter Real Matrix Metric SphereProduct JetChart UniformTube Profiles
open scoped Topology ContDiff
noncomputable section

/-- Uniform expansion of the actual minimum on the compact transverse disks for each positive Cheeger parameter. -/
theorem intrinsic_minimum_expansion (t : ℝ) (ht : 0<t) (χ : Scalar) :
    let c := compactNormalChart t
    let F := c.curvature (paperCoefficients t ht.le χ)
    ∃ center : CoreParameters → Tilts, ContinuousOn center c.core ∧
      (∀ x ∈ c.core, ∀ a, UniformTube.coeff F 2 x (center x) +
        ((2*(66+32/t^3))⁻¹/2)*‖a-center x‖^2 ≤ UniformTube.coeff F 2 x a) ∧
      ∃ C ≥ 0, ∃ ε > 0, ∀ x ∈ c.core, ∀ s ∈ Ioo 0 ε,
        let value := s^2*UniformTube.coeff F 2 x (center x) + s^3*UniformTube.coeff F 3 x (center x)
        (∀ z : Tilts, ‖z‖ ≤ c.radius → value-C*s^4 ≤ F (x,z,s)) ∧
        ∃ m ∈ closedBall (0:Tilts) c.radius, IsMinOn (fun z => F (x,z,s)) (closedBall 0 c.radius) m ∧
          |F (x,m,s)-value| ≤ C*s^4 :=
  compact_minimum_expansion t ht χ (intrinsic_background_comparison t ht.le)

/-- The signed quadratic expression in Proposition 5.1, evaluated using the
orientation of the separation chosen by the verifier. -/
def exportedQuadratic (t : ℝ) (v : FlatLocus.Representative) :=
  let x := rangeFactorization FlatLocus.forgetOrientation v
  let f := FlatLocus.data
  let u := f.sep x
  V2form lamC lamD (Certificate.Fx t u) (Certificate.Fy t u) (f.nx x) (f.ny x) (f.nz x)
    (Certificate.vectorA t u) (Certificate.vectorB t u) (f.xp x) (f.zp x)
    (Certificate.matrix₁ t u) (Certificate.matrix₂ t u)

private def coreWeight (x : CoreParameters) := x.1 0^2+x.1 1^2

/-- Identities still required of the actual moving minimum, in the spanning
frame of the transverse disk. The cubic identity is only needed at weight zero. -/
def matches_export (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) : Prop :=
  let F := (compactNormalChart t).curvature (paperCoefficients t ht χ)
  ∀ v : FlatLocus.Representative, rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular →
    ∀ a : Tilts, (∀ z, coeff F 2 (rawCore v) a ≤ coeff F 2 (rawCore v) z) →
      coeff F 2 (rawCore v) a = (hh t)^2/4*exportedQuadratic t v ∧
      (coreWeight (rawCore v) = 0 → coeff F 3 (rawCore v) a = (hh t)^2/4*mu t)

/-- Density includes each separate plane over the diagonal and antidiagonal.
The two regular coefficient identities suffice for the fixed-parameter conclusion. -/
theorem positive_of_regular_identities (t : ℝ) (ht : 0<t) (tmax : t ≤ 1/100) (χ : Scalar)
    (jets : matches_export t ht.le χ) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric, Realizes g s (paperCoefficients t ht.le χ) ∧
      PositiveSectionalCurvature g := by
  let c := compactNormalChart t
  let A := paperCoefficients t ht.le χ
  let F := c.curvature A
  obtain ⟨η,hη,reg⟩ := compact_curvature_regular t ht.le χ
  have sm (x) (hx : x ∈ c.core) : ContDiffAt ℝ 4 F (x,0,0) :=
    (reg _ ⟨hx,by simpa using c.radius_pos.le,le_rfl,hη.le⟩).of_le (by simp)
  have ⟨low,away⟩ := comparison_bounds t ht χ (intrinsic_background_comparison t ht.le)
  let lam := (2*(66+32/t^3))⁻¹
  have hl : 0<lam := by unfold lam; positivity
  obtain ⟨center,con,quad⟩ := exists_center F c.compact c.radius_pos hl
    (fun x hx => (sm x hx).of_le (by norm_num)) (fun _ h => (compact_chart_core_jet t ht.le χ h).1) low
  let m (i : ℕ) (v : FlatLocus.Representative) := coeff F i (rawCore v) (center (rawCore v))
  have core (v : FlatLocus.Representative) : rawCore v ∈ c.core := ⟨v,rfl⟩
  have raw : Continuous rawCore := by unfold rawCore; fun_prop
  have cm : Continuous (center ∘ rawCore) := continuousOn_univ.mp (con.comp raw.continuousOn (fun v _ => core v))
  have mc (i : ℕ) (hi : i ≤ 4) : Continuous (m i) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    exact (smooth_coeff (center (rawCore v)) i 0 (by omega) (sm _ (core v))).continuousAt.comp
      (f := fun v => (rawCore v,center (rawCore v))) (raw.prodMk cm).continuousAt
  have wcont : Continuous coreWeight := by unfold coreWeight; fun_prop
  let k := (hh t)^2/4
  have hk : 0<k := by dsimp [k]; have := hh_pos ht.le; positivity
  let κ := k*min (3/10) (mu t)
  have hκ : 0<κ := mul_pos hk (lt_min (by norm_num) (mu_pos ht.le))
  have wc (v : FlatLocus.Representative) : coreWeight (rawCore v) = FlatLocus.weight (rangeFactorization FlatLocus.forgetOrientation v) :=
    (FlatLocus.frame v).1
  have regsign (v : FlatLocus.Representative) (hv : rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) :
      κ*coreWeight (rawCore v) ≤ m 2 v ∧ (coreWeight (rawCore v)=0 → κ ≤ m 3 v) := by
    obtain ⟨e₂,e₃⟩ := jets v hv (center (rawCore v)) (fun z =>
      (le_add_of_nonneg_right (mul_nonneg (half_pos hl).le (sq_nonneg _))).trans (quad _ (core v) z))
    have wt : 0 ≤ coreWeight (rawCore v) := by unfold coreWeight; positivity
    have cert : 3/10*coreWeight (rawCore v) ≤ exportedQuadratic t v := by
      rw [wc]
      exact Certificate.fitted_V2_on_locus ⟨ht.le,tmax⟩ _
    constructor
    · change κ*_ ≤ coeff F 2 _ _
      rw [e₂]
      calc
        _ ≤ (k*(3/10))*coreWeight (rawCore v) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_left ..) hk.le) wt
        _ = k*((3/10)*coreWeight (rawCore v)) := mul_assoc ..
        _ ≤ _ := mul_le_mul_of_nonneg_left cert hk.le
    · intro e; change κ ≤ coeff F 3 _ _
      rw [e₃ e]
      exact mul_le_mul_of_nonneg_left (min_le_right ..) hk.le
  have closed₂ : IsClosed {v : FlatLocus.Representative | κ*coreWeight (rawCore v) ≤ m 2 v} :=
    isClosed_le (continuous_const.mul (wcont.comp raw)) (mc 2 (by decide))
  have closed₃ : IsClosed {v : FlatLocus.Representative | κ ≤ m 3 v} :=
    isClosed_le continuous_const (mc 3 (by decide))
  apply positive_of_compact_plane_estimates t ht χ _ (far_curvature_continuous t ht.le χ) away
  refine ⟨⟨η,hη,fun q hq => (reg q hq).of_le (by simp)⟩,fun _ h => (compact_chart_core_jet t ht.le χ h).1,
    ⟨lam,hl,low⟩,fun _ h => (compact_chart_core_jet t ht.le χ h).2.deriv,coreWeight,κ,hκ,wcont.continuousOn,?_,?_⟩
  · intro x _; unfold coreWeight; positivity
  · rintro _ ⟨v,rfl⟩ a min
    have same : a = center (rawCore v) := by
      have b := quad _ (core v) a
      have l := min (center (rawCore v))
      by_contra ne
      have pos := mul_pos (half_pos hl) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr ne)))
      linarith only [b,l,pos]
    subst a
    have dense := FlatLocus.regular_representative_dense v
    let S := {w : FlatLocus.Representative | rangeFactorization FlatLocus.forgetOrientation w ∈ FlatLocus.regular ∧ w.val.1=v.val.1}
    have inc : S ⊆ {w | κ*coreWeight (rawCore w) ≤ m 2 w} := fun w hw => (regsign w hw.1).1
    refine ⟨closed₂.closure_subset_iff.mpr inc dense,?_⟩
    intro zero
    have inc₃ : S ⊆ {w | κ ≤ m 3 w} := by
      intro w hw
      apply (regsign w hw.1).2
      change w.val.1.val 0^2+w.val.1.val 1^2=0
      rwa [hw.2]
    exact closed₃.closure_subset_iff.mpr inc₃ dense

/-- The concrete convergence theorem after the remaining geometric identities
are supplied for a sequence of positive Cheeger parameters tending to zero. -/
theorem localHopfProblem_of_regular_identities (t : ℕ → ℝ) (ht : ∀ n, 0<t n)
    (tmax : ∀ n, t n ≤ 1/100) (lim : Tendsto t atTop (𝓝 0)) (χ : ℕ → Scalar)
    (jets : ∀ n, matches_export (t n) (ht n).le (χ n)) :
    LocalHopfProblem :=
  localHopfProblem_of_positive_windows t (fun n => (ht n).le) lim χ
    (fun n => positive_of_regular_identities (t n) (ht n) (tmax n) (χ n) (jets n))

end
end LocalHopf.BackgroundGrowth.Transverse
