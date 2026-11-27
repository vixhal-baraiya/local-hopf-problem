import LocalHopf.MovingPlanes

/-! # Smoothness of the curvature numerator under plane tilts

At a fixed sphere pair, arbitrary tangent vectors are linear combinations of
four coordinate extensions. Spatial differentiation acts on their coefficient
functions on the manifold, leaving the tilt parameters constant.
-/
namespace LocalHopf.SphereProduct
open Bundle FiberBundle Filter Set Matrix Metric
open scoped Topology Manifold ContDiff
noncomputable section

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
-- Use the norm of the product chart model on a single tangent fiber.
local instance (p : Base) : NormedAddCommGroup (Tangent p) :=
  inferInstanceAs (NormedAddCommGroup Coordinates)
local instance (p : Base) : NormedSpace ℝ (Tangent p) :=
  inferInstanceAs (NormedSpace ℝ Coordinates)

private abbrev smoothNear (p : Base) (f : Base → ℝ) :=
  ∀ᶠ q in 𝓝 p, ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ f q

/-- Local finite sums of spatial functions with smooth parameter coefficients. -/
private inductive Separated (p : Base) : (T → Base → ℝ) → Prop
  | fixed (f : Base → ℝ) (h : smoothNear p f) : Separated p (fun _ => f)
  | add {f g} : Separated p f → Separated p g → Separated p (fun a q => f a q + g a q)
  | scale (c : T → ℝ) (h : ContDiff ℝ ∞ c) {f} : Separated p f → Separated p (fun a q => c a * f a q)
  | germ {f g} : Separated p f → (∀ a, g a =ᶠ[𝓝 p] f a) → Separated p g

private theorem Separated.spatial {p : Base} {f : T → Base → ℝ} (hf : Separated p f) (a : T) :
    smoothNear p (f a) := by
  induction hf with
  | fixed _ h => exact h
  | add _ _ ih ik => filter_upwards [ih,ik] with q h k using h.add k
  | scale c _ _ ih => filter_upwards [ih] with q h using (contMDiffAt_const (c := c a)).mul h
  | germ _ e ih => filter_upwards [ih,(e a).eventuallyEq_nhds] with q h eq using h.congr_of_eventuallyEq eq

private theorem Separated.parameter {p : Base} {f : T → Base → ℝ} (hf : Separated p f) :
    ContDiff ℝ ∞ (fun a => f a p) := by
  induction hf with
  | fixed => exact contDiff_const
  | add _ _ ih ik => exact ih.add ik
  | scale _ h _ ih => exact h.mul ih
  | germ _ e ih => exact (funext fun a => (e a).self_of_nhds) ▸ ih

private theorem Separated.sum {p : Base} {ι : Type*} [Fintype ι] (f : ι → T → Base → ℝ)
    (hf : ∀ i, Separated p (f i)) : Separated p (fun a q => ∑ i, f i a q) := by
  classical
  suffices ∀ s : Finset ι, Separated p (fun a q => ∑ i ∈ s, f i a q) from this _
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using Separated.fixed (T := T) (p := p) (fun _ => 0) (by exact Eventually.of_forall fun _ => contMDiffAt_const)
  | insert i s hi ih => simpa [Finset.sum_insert,hi] using (hf i).add ih

private theorem Separated.dir_fixed {p : Base} {f : T → Base → ℝ} (hf : Separated p f)
    (V : Field) (hv : ∀ᶠ q in 𝓝 p, FieldSmoothAt V q) :
    Separated p (fun a => directional V (f a)) := by
  induction hf with
  | fixed f h =>
    apply Separated.fixed
    filter_upwards [h,hv] with q hs hV using directional_smoothAt hV hs
  | @add f g hf hg ih ik =>
    refine (ih.add ik).germ fun a => ?_
    filter_upwards [hf.spatial a,hg.spatial a] with q hu hw
    exact directional_add V (hu.mdifferentiableAt (by simp)) (hw.mdifferentiableAt (by simp))
  | @scale c hc f hf ih =>
    refine (ih.scale c hc).germ fun a => ?_
    filter_upwards [hf.spatial a] with q h
    exact directional_mul_const V (c a) (h.mdifferentiableAt (by simp))
  | germ _ eq ih =>
    refine ih.germ fun a => ?_
    filter_upwards [(eq a).eventuallyEq_nhds] with q h using directional_congr h

private theorem extend_frame {p : Base} (b : Frame p) : ∀ᶠ q in 𝓝 p, ∀ v : Tangent p,
    extend Coordinates v q = ∑ i, (b.equivFun v i) • extend Coordinates (b i) q := by
  let e := trivializationAt Coordinates (TangentSpace productModel : Base → Type) p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt' p
  filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
  let L := (e.symmL ℝ q).comp (e.continuousLinearMapAt ℝ p)
  have hl (v : Tangent p) : L v = extend Coordinates v q := by
    simp [L, e.continuousLinearMapAt_apply_of_mem ℝ hp,e.symmL_apply hq,extend,e]
  intro v
  simp_rw [← hl]
  simp_rw [← L.map_smul]
  rw [← map_sum]
  congr 1
  exact (b.sum_repr v).symm

private def coordinates {p : Base} (b : Frame p) (i : Fin 4) : Tangent p →L[ℝ] ℝ :=
  letI : FiniteDimensional ℝ (Tangent p) := inferInstanceAs (FiniteDimensional ℝ Coordinates)
  (b.coord i).toContinuousLinearMap

private theorem separated_pair {p : Base} (b : Frame p) (A : AmbientTensor)
    {X Y : T → Tangent p} (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    Separated p (fun a => ambientPair A (extend Coordinates (X a)) (extend Coordinates (Y a))) := by
  let U (i : Fin 4) := extend (E := Tangent) Coordinates (b i)
  let cx (i : Fin 4) (a : T) := coordinates b i (X a)
  let cy (i : Fin 4) (a : T) := coordinates b i (Y a)
  have basis (i j : Fin 4) : Separated (T := T) p (fun _ => ambientPair A (U i) (U j)) := by
    apply Separated.fixed
    filter_upwards [extend_smooth_near (b i),extend_smooth_near (b j)] with q hi hj using ambientPair_smooth A hi hj
  refine (Separated.sum _ fun i => (Separated.sum _ fun j =>
    (basis i j).scale (cy j) ((coordinates b j).contDiff.comp hY)).scale (cx i) ((coordinates b i).contDiff.comp hX)).germ ?_
  intro a
  filter_upwards [extend_frame b] with q he
  unfold ambientPair
  rw [he (X a),he (Y a)]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change cy j a * (cx i a * _) = cx i a * (cy j a * _)
  ring

private theorem Separated.dir {p : Base} {f : T → Base → ℝ} (hf : Separated p f)
    (b : Frame p) {X : T → Tangent p} (hX : ContDiff ℝ ∞ X) :
    Separated p (fun a => directional (extend Coordinates (X a)) (f a)) := by
  let U (i : Fin 4) := extend (E := Tangent) Coordinates (b i)
  refine (Separated.sum _ fun i => (hf.dir_fixed (U i) (extend_smooth_near (b i))).scale
    (fun a => coordinates b i (X a)) ((coordinates b i).contDiff.comp hX)).germ ?_
  intro a
  filter_upwards [extend_frame b] with q he
  unfold directional
  rw [he (X a),map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

theorem smooth_ambientGamma {p : Base} (A : AmbientTensor) {X Y Z : T → Tangent p}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) :
    ContDiff ℝ ∞ (fun a => ambientGamma A (X a) (Y a) (Z a)) := by
  let b := coordinateFrame p
  exact ((((separated_pair b A hY hZ).dir b hX).parameter.add
    ((separated_pair b A hX hZ).dir b hY).parameter).sub
    ((separated_pair b A hX hY).dir b hZ).parameter).div_const 2

theorem smooth_ambientSecond {p : Base} (A : AmbientTensor) {X Y : T → Tangent p}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (fun a => ambientSecond A (X a) (Y a)) := by
  let b := coordinateFrame p
  have f := (separated_pair b A hY hX).dir b hY
  have g := ((separated_pair b A hY hY).dir b hX).scale (fun _ => -(1/2 : ℝ)) contDiff_const
  have k := ((separated_pair b A hX hX).dir b hY).scale (fun _ => (1/2 : ℝ)) contDiff_const
  have e := (((f.add g).dir b hX).parameter).sub ((k.dir b hY).parameter)
  convert e using 1
  funext a
  dsimp [ambientSecond]
  congr 2 <;> funext q <;> ring

private theorem smooth_cubic {s : T → ℝ} (hs : ContDiff ℝ ∞ s) (u : Fin 4 → T → ℝ)
    (hu : ∀ i, ContDiff ℝ ∞ (u i)) :
    ContDiff ℝ ∞ (fun a => cubicValue (s a) (fun i => u i a)) :=
  (((hu 0).add (hs.mul (hu 1))).add ((hs.pow 2).mul (hu 2))).add ((hs.pow 3).mul (hu 3))

/-- The numerator on moving vectors of a fixed tangent space is smooth jointly
in the vectors and the metric parameter wherever the Gram determinant is nonzero. -/
theorem smooth_tilted_numerator {p : Base} (A : Fin 4 → AmbientTensor) {X Y : T → Tangent p}
    {s : T → ℝ} (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) (hs : ContDiff ℝ ∞ s) {a : T}
    (hd : (metricPolynomial A (coordinateFrame p)).det.eval (s a) ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => (TangentPair.mk p (X z) (Y z)).numerator A (s z)) a := by
  let b := coordinateFrame p
  let G := metricPolynomial A b
  have ev (D : Polynomial ℝ) : ContDiff ℝ ∞ (fun z => D.eval (s z)) := by
    simpa only [Polynomial.coe_aeval_eq_eval, Function.comp_def] using (D.contDiff_aeval ∞).comp hs
  let J (U V : T → Tangent p) (i : Fin 4) (z : T) :=
    cubicValue (s z) (fun k => ambientGamma (A k) (U z) (V z) (b i))
  have symb {U V : T → Tangent p} (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (i : Fin 4) :
      ContDiff ℝ ∞ (J U V i) :=
    smooth_cubic hs _ fun k => smooth_ambientGamma (A k) hU hV contDiff_const
  let pair (u v : Fin 4 → T → ℝ) (z : T) :=
    (fun i => u i z) ⬝ᵥ (G.adjugate.map (Polynomial.evalRingHom (s z))) *ᵥ (fun j => v j z)
  have hp {u v : Fin 4 → T → ℝ} (hu : ∀ i, ContDiff ℝ ∞ (u i)) (hv : ∀ i, ContDiff ℝ ∞ (v i)) :
      ContDiff ℝ ∞ (pair u v) := by
    unfold pair dotProduct mulVec
    exact ContDiff.sum fun i _ => (hu i).mul (ContDiff.sum fun j _ => (ev (G.adjugate i j)).mul (hv j))
  have second := smooth_cubic hs _ (fun k => smooth_ambientSecond (A k) hX hY)
  have result := ((((second.mul (ev G.det)).add (hp (symb hX hY) (symb hX hY))).sub
    (hp (symb hX hX) (symb hY hY))).contDiffAt (x := a)).div (ev G.det).contDiffAt hd
  apply result.congr_of_eventuallyEq
  exact Eventually.of_forall fun z => congrArg (· / G.det.eval (s z))
    (eval_numeratorPolynomial A b (X z) (Y z) (s z))

/-- The paper's four graph coordinates in the normal directions. -/
def tiltedPair {p : Base} (U V N₁ N₂ : Tangent p) (z : Fin 4 → ℝ) : TangentPair :=
  ⟨p,U+z 0 • N₁+z 1 • N₂,V+z 2 • N₁+z 3 • N₂⟩

/-- Curvature of the four-parameter graph frame in the prescribed family. The
first real coordinate is a dummy core coordinate for the singleton chart. -/
def graphNumerator {p : Base} (A : Fin 4 → AmbientTensor) (U V N₁ N₂ : Tangent p)
    (q : ℝ × (Fin 4 → ℝ) × ℝ) : ℝ :=
  (tiltedPair U V N₁ N₂ q.2.1).numerator A q.2.2

/-- At a fixed sphere pair the entire graph is regular on one metric-parameter interval. -/
theorem graph_window (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) (p : Base)
    (U V N₁ N₂ : Tangent p) :
    ∃ η > 0, η ≤ 1 ∧ ∀ q : ℝ × (Fin 4 → ℝ) × ℝ, q.2.2 ∈ Icc 0 η →
      ContDiffAt ℝ 4 (graphNumerator (paperCoefficients t ht χ) U V N₁ N₂) q := by
  let A := paperCoefficients t ht χ
  let b := coordinateFrame p
  let D := (metricPolynomial A b).det
  have he := eval_metricPolynomial_zero A b
  have hd : D.eval 0 ≠ 0 := by
    have h₀ : ambientGram (A 0) b = gramMatrix (backgroundMetric t ht) b := rfl
    exact (((Polynomial.evalRingHom (0:ℝ)).map_det (metricPolynomial A b)).trans
      (congrArg Matrix.det (he.trans h₀))).trans_ne (gram_isUnit _ b).ne_zero
  obtain ⟨ε,hε,win⟩ := Metric.mem_nhds_iff.mp (D.continuous.continuousAt.eventually_ne hd)
  let η := min (ε/2) 1
  have hη : 0 < η := lt_min (half_pos hε) one_pos
  refine ⟨η,hη,min_le_right ..,?_⟩
  intro q hq
  apply ContDiffAt.of_le (n := ∞) _ (by simp)
  apply smooth_tilted_numerator A (X := fun w : ℝ × (Fin 4 → ℝ) × ℝ =>
    U+w.2.1 0 • N₁+w.2.1 1 • N₂) (Y := fun w => V+w.2.1 2 • N₁+w.2.1 3 • N₂)
    (s := fun w => w.2.2) (by fun_prop) (by fun_prop) (by fun_prop)
  apply win
  rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hq.1]
  exact (hq.2.trans (min_le_left ..)).trans_lt (half_lt_self hε)

/-- Uniform two-sided Taylor remainder on all graph tilts `s • ζ` of bounded
speed. The very same metric works for every tilt in the bound. No assumption
on the curvature, the normal Hessian, or the two vectors is needed. -/
theorem graph_expansion (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) (p : Base)
    (U V N₁ N₂ : Tangent p) (R : ℝ) :
    let A := paperCoefficients t ht χ
    let F := graphNumerator A U V N₁ N₂
    ∃ C ≥ 0, ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric, Realizes g s A ∧
      ∀ ζ : Fin 4 → ℝ, ‖ζ‖ ≤ R →
        let w := tiltedPair U V N₁ N₂ (s • ζ)
        |curvatureNumerator g w.point w.first w.second -
          cubicValue s (fun i => UniformTube.coeff F i.val 0 ζ)| ≤ C*s^4 := by
  intro A F
  obtain ⟨η,hη,hη1,reg⟩ := graph_window t ht χ p U V N₁ N₂
  have regular (q : ℝ × (Fin 4 → ℝ) × ℝ) (hq : q ∈ UniformTube.disk ({0} : Set ℝ) R η) :
      ContDiffAt ℝ 4 F q := reg q hq.2.2
  obtain ⟨C,hC,hbound⟩ := UniformTube.rescaled_expansion F (isCompact_singleton (x := (0:ℝ))) R regular
  refine ⟨C,hC,?_⟩
  filter_upwards [(paper_metrics_realize t ht χ).filter_mono nhdsWithin_le_nhds, Ioo_mem_nhdsGT hη] with s hg hs
  obtain ⟨g,hg⟩ := hg
  refine ⟨g,hg,?_⟩
  intro ζ hz w
  rw [← w.numerator_eq hg]
  have hscaled : ‖s • ζ‖ ≤ R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hs.2.le.trans hη1)).trans hz
  exact hbound 0 (by simp) ζ s hz hscaled hs.1 hs.2.le

/-- Two-sided expansion of the least actual curvature numerator over the
whole graph disk at a fixed base point. The minimizing tilt may depend on
the parameter. Background growth and the first variation are tested directly
on the specified tensor polynomial. -/
theorem graph_minimum (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) (p : Base)
    (U V N₁ N₂ : Tangent p) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 < lam) :
    let A := paperCoefficients t ht χ
    let F := graphNumerator A U V N₁ N₂
    F (0,0,0) = 0 → (∀ z, ‖z‖ ≤ δ → lam*‖z‖^2 ≤ F (0,z,0)) →
    deriv (fun s => F (0,0,s)) 0 = 0 →
    ∃ a : Fin 4 → ℝ, (∀ ζ, UniformTube.coeff F 2 0 a + (lam/2)*‖ζ-a‖^2 ≤ UniformTube.coeff F 2 0 ζ) ∧
      ∃ C ≥ 0, ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric, Realizes g s A ∧
        let u := fun z => curvatureNumerator g p (tiltedPair U V N₁ N₂ z).first (tiltedPair U V N₁ N₂ z).second
        ∃ m ∈ closedBall 0 δ, IsMinOn u (closedBall 0 δ) m ∧
          |u m - (s^2*UniformTube.coeff F 2 0 a + s^3*UniformTube.coeff F 3 0 a)| ≤ C*s^4 := by
  intro A F hflat hgrowth hfirst
  obtain ⟨η,hη,_,regular⟩ := graph_window t ht χ p U V N₁ N₂
  obtain ⟨a,_,hq,C,hC,ε,hε,expan⟩ := UniformTube.minimum_expansion F (isCompact_singleton (x := (0:ℝ)))
    hδ hη hlam (fun q hq => regular q hq.2.2) (by simpa using hflat)
    (by simpa using hgrowth) (by simpa using hfirst)
  refine ⟨a 0,hq 0 (by simp),C,hC,?_⟩
  filter_upwards [(paper_metrics_realize t ht χ).filter_mono nhdsWithin_le_nhds, Ioo_mem_nhdsGT hε] with s hg hs
  obtain ⟨g,hg⟩ := hg
  refine ⟨g,hg,?_⟩
  have eq (z : Fin 4 → ℝ) : F (0,z,s) =
      curvatureNumerator g p (tiltedPair U V N₁ N₂ z).first (tiltedPair U V N₁ N₂ z).second :=
    (tiltedPair U V N₁ N₂ z).numerator_eq hg
  simpa only [← eq] using (expan 0 (by simp) s hs).2

end
end LocalHopf.SphereProduct
