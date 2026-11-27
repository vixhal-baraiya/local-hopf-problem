import LocalHopf.CurvatureBasis
import LocalHopf.NormalMinimum
import LocalHopf.SectionalCoefficients
import LocalHopf.Perturbation

/-! # Positivity on moving tangent planes

The scalar function in a chart is the rational expression for the Levi-Civita
numerator of the prescribed tensor. Chart coverage concerns actual tangent
frames. The hypotheses on derivatives are (H0), (H1) and (H2) on these charts.
-/
namespace LocalHopf.SphereProduct

open Set Filter Metric UniformTube
open scoped Topology ContDiff
noncomputable section

/-- A point and two tangent vectors, with no choice of metric. -/
structure TangentPair where
  point : Base
  first : Tangent point
  second : Tangent point

/-- Exact curvature expression as a scalar function of the parameter. The
denominator is nonzero whenever a positive metric realizes the tensors. -/
def TangentPair.numerator (w : TangentPair) (A : Fin 4 → AmbientTensor) (s : ℝ) : ℝ :=
  let b := coordinateFrame w.point
  (numeratorPolynomial A b w.first w.second).eval s / (metricPolynomial A b).det.eval s

theorem TangentPair.numerator_eq (w : TangentPair) {A : Fin 4 → AmbientTensor}
    {s : ℝ} {g : SmoothMetric} (hg : Realizes g s A) :
    w.numerator A s = curvatureNumerator g w.point w.first w.second :=
  (curvature_rational hg _ _ _).symm

/-- A frame obtained by changing the spanning vectors at the same point. -/
def TangentPair.Represents (w v : TangentPair) : Prop :=
  ∃ a b c d : ℝ, a*d-b*c ≠ 0 ∧ w = ⟨v.point,a • v.first+b • v.second,c • v.first+d • v.second⟩

theorem TangentPair.represents_self (w : TangentPair) : w.Represents w :=
  ⟨1,0,0,1,by norm_num,by simp⟩

theorem TangentPair.positive_of_represents {w v : TangentPair} (h : w.Represents v) (g : SmoothMetric)
    (hw : 0 < curvatureNumerator g w.point w.first w.second) :
    0 < curvatureNumerator g v.point v.first v.second := by
  obtain ⟨a,b,c,d,det,rfl⟩ := h
  rw [show curvatureNumerator g _ _ _ = _ from curvatureNumerator_basis_change g v.point v.first v.second a b c d] at hw
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero det)).mp hw

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- A compact piece of a parametrization by core point and normal coordinates. -/
structure NormalChart (P E : Type*) [NormedAddCommGroup P] where
  frame : P × E → TangentPair
  core : Set P
  compact : IsCompact core
  radius : ℝ
  radius_pos : 0 < radius

def NormalChart.curvature (c : NormalChart P E) (A : Fin 4 → AmbientTensor) (q : P × E × ℝ) :=
  (c.frame (q.1,q.2.1)).numerator A q.2.2

/-- The input to the scalar chart test consists entirely of background and
derivative data. The quadratic and cubic coefficients are calculated along the
same minimizing tilt. -/
structure NormalChart.Estimates (c : NormalChart P E) (A : Fin 4 → AmbientTensor) : Prop where
  regular : ∃ η > 0, ∀ q ∈ disk (E := E) c.core c.radius η, ContDiffAt ℝ 4 (c.curvature A) q
  flat : ∀ x ∈ c.core, c.curvature A (x,0,0) = 0
  growth : ∃ lam > 0, ∀ x ∈ c.core, ∀ z : E, ‖z‖ ≤ c.radius →
    lam*‖z‖^2 ≤ c.curvature A (x,z,0)
  first : ∀ x ∈ c.core, deriv (fun s => c.curvature A (x,0,s)) 0 = 0
  signs : ∃ (ρ : P → ℝ) (κ : ℝ), 0 < κ ∧ ContinuousOn ρ c.core ∧
    (∀ x ∈ c.core, 0 ≤ ρ x) ∧ ∀ x ∈ c.core, ∀ a : E,
      (∀ z, coeff (c.curvature A) 2 x a ≤ coeff (c.curvature A) 2 x z) →
        κ*ρ x ≤ coeff (c.curvature A) 2 x a ∧ (ρ x = 0 → κ ≤ coeff (c.curvature A) 3 x a)

/-- The uniform near-region sign on an entire compact chart of moving frames. -/
theorem NormalChart.positive (c : NormalChart P E) (A : Fin 4 → AmbientTensor) (h : c.Estimates A) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ x ∈ c.core, ∀ z : E, ‖z‖ ≤ c.radius →
      0 < (c.frame (x,z)).numerator A s := by
  obtain ⟨η,hη,reg⟩ := h.regular
  obtain ⟨lam,hlam,growth⟩ := h.growth
  obtain ⟨ρ,κ,hκ,hρ,hρ0,signs⟩ := h.signs
  let F := c.curvature A
  obtain ⟨a,ha,hq,C,_,ε,hε,hlow⟩ := minimum_expansion F c.compact c.radius_pos hη hlam
    reg h.flat growth h.first
  let U (n : ℕ) (x : c.core) := coeff F n x.val (a x.val)
  have hsign (x : c.core) := signs x.val x.property (a x.val) fun z =>
    (le_add_of_nonneg_right (mul_nonneg (half_pos hlam).le (sq_nonneg _))).trans (hq _ x.property z)
  let : CompactSpace c.core := isCompact_iff_compactSpace.mp c.compact
  have hU : Continuous (U 3) := by
    apply (continuousOn_iff_continuous_domRestrict (s := c.core) (f := fun x => coeff F 3 x (a x))).mp
    intro x hx
    have hf := reg (x,0,0) (show (x,(0:E),(0:ℝ)) ∈ disk c.core c.radius η from
      ⟨hx,by simpa using c.radius_pos.le,le_rfl,hη.le⟩)
    exact (smooth_coeff (a x) 3 0 (by decide) hf).continuousAt.comp_continuousWithinAt
      (f := fun w => (w,a w)) (continuousWithinAt_id.prodMk (ha x hx))
  let N := c.core × (closedBall (0:E) c.radius)
  obtain ⟨d,hd,hp⟩ := eventually_positive (fun (p : N) s => F (p.1.val,p.2.val,s)) (U 2) (U 3)
    (fun x => ρ x.val) hU (continuousOn_iff_continuous_domRestrict.mp hρ) κ hκ
    (fun x => hρ0 _ x.property) (fun x => (hsign x).1) (fun x => (hsign x).2)
    (fun _ => False) Prod.fst 1 C (ε/2) one_pos (half_pos hε) (fun _ _ _ _ h => h.elim)
    (fun p s hs he _ => (hlow p.1.val p.1.property s ⟨hs,he.trans_lt (half_lt_self hε)⟩).1 p.2.val
      (by simpa only [mem_closedBall,dist_zero_right] using p.2.property))
  filter_upwards [Ioo_mem_nhdsGT hd] with s hs
  intro x hx z hz
  exact hp (⟨x,hx⟩,⟨z,by simpa using hz⟩) s hs.1 hs.2

private theorem compact_positive {D : Type*} [TopologicalSpace D] {S : Set D} (hS : IsCompact S)
    (f : D × ℝ → ℝ) (hc : ∀ x ∈ S, ContinuousAt f (x,0)) (hp : ∀ x ∈ S, 0 < f (x,0)) :
    ∀ᶠ s in 𝓝 (0:ℝ), ∀ x ∈ S, 0 < f (x,s) := by
  have h := hS.mem_nhdsSet_prod_of_forall (s := {q | 0 < f q}) (l := 𝓝 (0:ℝ))
    (fun x hx => by rw [← nhds_prod_eq]; exact (hc x hx).eventually (lt_mem_nhds (hp x hx)))
  obtain ⟨V,hV,T,hT,inc⟩ := mem_prod_iff.mp h
  filter_upwards [hT] with s hs
  exact fun x hx => inc ⟨subset_of_mem_nhdsSet hV hx,hs⟩

/-- A finite near/far cover up to invertible changes of spanning vectors suffices for positivity. -/
theorem positive_metrics_of_plane_charts {ι D : Type*} [Finite ι] [TopologicalSpace D]
    (t : ℝ) (ht : 0 ≤ t) (χ : Scalar)
    (c : ι → NormalChart P E) (near : ∀ i, (c i).Estimates (paperCoefficients t ht χ))
    (far : D → TangentPair) (S : Set D) (hS : IsCompact S)
    (farCont : ∀ w ∈ S, ContinuousAt (fun q : D × ℝ => (far q.1).numerator (paperCoefficients t ht χ) q.2) (w,0))
    (farPos : ∀ w ∈ S, 0 < (far w).numerator (paperCoefficients t ht χ) 0)
    (cover : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ g : SmoothMetric, Realizes g s (paperCoefficients t ht χ) →
      ∀ (p : Base) (X Y : Tangent p), g.inner p X X = 1 → g.inner p Y Y = 1 → g.inner p X Y = 0 →
        (∃ w ∈ S, (far w).Represents ⟨p,X,Y⟩) ∨
        ∃ i, ∃ x ∈ (c i).core, ∃ z : E, ‖z‖ ≤ (c i).radius ∧ ((c i).frame (x,z)).Represents ⟨p,X,Y⟩) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric, Realizes g s (paperCoefficients t ht χ) ∧
      PositiveSectionalCurvature g := by
  let A := paperCoefficients t ht χ
  have regions := Filter.eventually_all.mpr (fun i => (c i).positive A (near i))
  have away := compact_positive hS _ farCont farPos
  filter_upwards [(paper_metrics_realize t ht χ).filter_mono nhdsWithin_le_nhds,
    cover,regions,away.filter_mono nhdsWithin_le_nhds] with s hg hcov hn hf
  obtain ⟨g,hg⟩ := hg
  refine ⟨g,hg,fun p X Y hx hy hxy => ?_⟩
  rcases hcov g hg p X Y hx hy hxy with ⟨w,hw,he⟩ | ⟨i,x,hx,z,hz,he⟩
  · apply TangentPair.positive_of_represents (w := far w) (v := ⟨p,X,Y⟩) he g
    rw [← TangentPair.numerator_eq _ hg]
    exact hf w hw
  · apply TangentPair.positive_of_represents (w := (c i).frame (x,z)) (v := ⟨p,X,Y⟩) he g
    rw [← TangentPair.numerator_eq _ hg]
    exact hn i x hx z hz

/-- A finite cover by compact near charts and a compact far part. If these
frames cover the orthonormal pairs of the prescribed metrics, (H0)–(H2)
imply actual positive sectional curvature at all sufficiently small positive
parameters. There is no uniform curvature lower bound among the premises. -/
theorem positive_metrics_of_charts {ι D : Type*} [Finite ι] [TopologicalSpace D]
    (t : ℝ) (ht : 0 ≤ t) (χ : Scalar)
    (c : ι → NormalChart P E) (near : ∀ i, (c i).Estimates (paperCoefficients t ht χ))
    (far : D → TangentPair) (S : Set D) (hS : IsCompact S)
    (farCont : ∀ w ∈ S, ContinuousAt (fun q : D × ℝ => (far q.1).numerator (paperCoefficients t ht χ) q.2) (w,0))
    (farPos : ∀ w ∈ S, 0 < (far w).numerator (paperCoefficients t ht χ) 0)
    (cover : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ g : SmoothMetric, Realizes g s (paperCoefficients t ht χ) →
      ∀ (p : Base) (X Y : Tangent p), g.inner p X X = 1 → g.inner p Y Y = 1 → g.inner p X Y = 0 →
        (∃ w ∈ S, far w = ⟨p,X,Y⟩) ∨
        ∃ i, ∃ x ∈ (c i).core, ∃ z : E, ‖z‖ ≤ (c i).radius ∧ (c i).frame (x,z) = ⟨p,X,Y⟩) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric, Realizes g s (paperCoefficients t ht χ) ∧
      PositiveSectionalCurvature g := by
  apply positive_metrics_of_plane_charts t ht χ c near far S hS farCont farPos
  filter_upwards [cover] with s hs
  intro g hg p X Y hx hy hxy
  rcases hs g hg p X Y hx hy hxy with ⟨w,hw,eq⟩ | ⟨i,x,hx,z,hz,eq⟩
  · exact Or.inl ⟨w,hw,eq ▸ TangentPair.represents_self _⟩
  · exact Or.inr ⟨i,x,hx,z,hz,eq ▸ TangentPair.represents_self _⟩

end
end LocalHopf.SphereProduct
