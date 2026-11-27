import LocalHopf.MetricScaling
import LocalHopf.FrameCompactness
import LocalHopf.EquatorExtension
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # Convergence of the prescribed metrics in product charts -/

namespace LocalHopf.SphereProduct
open Set Filter Metric Function Bundle
open scoped Topology ContDiff Manifold
noncomputable section

private abbrev Icoord := 𝓘(ℝ, Coordinates)

private theorem chart_smooth {p : Base} {z : Coordinates} (hz : z ∈ (extChartAt productModel p).target) :
    ContMDiffAt Icoord productModel ∞ (extChartAt productModel p).symm z :=
  (contMDiffWithinAt_extChartAt_symm_target p hz).contMDiffAt (extChartAt_target_mem_nhds' hz)

private def chartVelocity (p : Base) (a z : Coordinates) :=
  let e := (extChartAt productModel p).symm
  ambientVelocityL (e z) (mfderiv Icoord productModel e z a)

private theorem velocity_smooth {p : Base} {z : Coordinates} (a : Coordinates)
    (hz : z ∈ (extChartAt productModel p).target) : ContDiffAt ℝ ∞ (chartVelocity p a) z := by
  have sec : ContMDiffAt Icoord Icoord.tangent ∞
      (fun w : Coordinates => (⟨w,a⟩ : TangentBundle Icoord Coordinates)) z :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  have jet := (chart_smooth hz).contMDiffAt_tangentMap
    (X := (⟨z,a⟩ : TangentBundle Icoord Coordinates)) (m := ∞) (by simp)
  let e := (extChartAt productModel p).symm
  let lift := fun w : Coordinates => (⟨w,a⟩ : TangentBundle Icoord Coordinates)
  have comp : ContMDiffAt Icoord productModel.tangent ∞ ((tangentMap Icoord productModel e) ∘ lift) z :=
    jet.comp (f := lift) z sec
  exact (ambientVelocity_smooth.contMDiffAt.comp (f := (tangentMap Icoord productModel e) ∘ lift) z comp).contDiffAt

private theorem spatialJet_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × E → ℝ} {q : ℝ × E} (hF : ContDiffAt ℝ ∞ F q) (j : ℕ) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => iteratedFDeriv ℝ j (fun x => F (z.1,x)) z.2) q := by
  induction j with
  | zero => exact (continuousMultilinearCurryFin0 ℝ E ℝ).symm.contDiff.contDiffAt.comp q hF
  | succ j ih =>
    let u := fun (z : ℝ × E) (x : E) => iteratedFDeriv ℝ j (fun y => F (z.1,y)) x
    have hh : ContDiffAt ℝ ∞ (uncurry u) (q,q.2) :=
      ih.comp (q,q.2) ((contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd)
    have hd := hh.fderiv (f := u) (contDiffAt_snd (p := q) (n := ∞)) (by simp)
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) ℝ).symm.contDiff.contDiffAt.comp q hd

private theorem compact_jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × E → ℝ) {K : Set E} (hK : IsCompact K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ F (0,x)) (j : ℕ) :
    TendstoUniformlyOn (fun t => iteratedFDeriv ℝ j (fun z => F (t,z)))
      (iteratedFDeriv ℝ j (fun z => F (0,z))) (𝓝 0) K := by
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK,
    tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  let J := fun q : ℝ × E => iteratedFDeriv ℝ j (fun z => F (q.1,z)) q.2
  have hJ : ContinuousAt J (0,x) := (spatialJet_smooth (hf x hx) j).continuousAt
  have h₀ : ContinuousAt (fun q : ℝ × E => J (0,q.2)) (0,x) :=
    hJ.comp (x := ((0:ℝ),x)) (f := fun q : ℝ × E => (0,q.2)) (continuousAt_const.prodMk continuousAt_snd)
  exact ((h₀.prodMk hJ).tendsto.mono_right (nhds_le_uniformity _)).mono_left (by
    rw [nhds_prod_eq]; exact Filter.prod_mono le_rfl nhdsWithin_le_nhds)

private def backgroundChart (p : Base) (a b : Coordinates) (q : ℝ × Coordinates) := chartCoefficient (fun x X Y =>
    2 * ambientBackground q.1 x (ambientVelocityL x X) (ambientVelocityL x Y)) p a b q.2

private theorem smooth_backgroundChart (p : Base) (a b : Coordinates) {t : ℝ} (ht : 0 ≤ t) {x : Coordinates}
  (hx : x ∈ (extChartAt productModel p).target) : ContDiffAt ℝ ∞ (backgroundChart p a b) (t,x) := by
  have reg := chart_smooth hx
  have pos := (ambientPoint_smooth.contMDiffAt.comp x reg).contDiffAt
  let z := ambientPoint ((extChartAt productModel p).symm x)
  have oper := (Cheeger.smooth_ambientOperator (p := z.1) (q := z.2) (t := t) ht).comp
    (t,x) ((pos.comp (f := (Prod.snd : ℝ × Coordinates → Coordinates)) (t,x) contDiffAt_snd).prodMk contDiffAt_fst)
  have A := (velocity_smooth a hx).comp (f := (Prod.snd : ℝ × Coordinates → Coordinates)) (t,x) contDiffAt_snd
  have B := (velocity_smooth b hx).comp (f := (Prod.snd : ℝ × Coordinates → Coordinates)) (t,x) contDiffAt_snd
  exact contDiffAt_const.mul (contDiffAt_const.mul
    ((ambientRoundForm.contDiff.contDiffAt.comp _ (oper.clm_apply A)).clm_apply B))

/-- Twice the Cheeger background tends to the round product in every derivative
on every compact subset of every product chart. -/
theorem background_chart_convergence (p : Base) (a b : Coordinates) (j : ℕ) (K : Set Coordinates)
    (hK : IsCompact K) (hs : K ⊆ (extChartAt productModel p).target) :
    TendstoUniformlyOn
      (fun t : ℝ => iteratedFDeriv ℝ j (chartCoefficient (fun q X Y =>
        2 * ambientBackground t q (ambientVelocityL q X) (ambientVelocityL q Y)) p a b))
      (iteratedFDeriv ℝ j (chartCoefficient (fun q X Y => roundPair q (X.1,X.2) (Y.1,Y.2)) p a b))
      (𝓝 0) K := by
  let F := backgroundChart p a b
  have atzero : (fun z => F (0,z)) =
      chartCoefficient (fun q X Y => roundPair q (X.1,X.2) (Y.1,Y.2)) p a b := by
    funext z
    exact twice_backgroundMetric_zero ..
  rw [← atzero]
  exact compact_jets F hK (fun _ hx => smooth_backgroundChart p a b le_rfl (hs hx)) j

/-- Scaling by two undoes the normalization of the Cheeger background. -/
def twiceMetric (g : SmoothMetric) : SmoothMetric where
  inner p := g.inner p + g.inner p
  symm p X Y := by simp [g.symm p X Y]
  pos p X hX := add_pos (g.pos p X hX) (g.pos p X hX)
  isVonNBounded p := (g.isVonNBounded p).subset (by
    intro v hv
    change g.inner p v v + g.inner p v v < 1 at hv
    change g.inner p v v < 1
    linarith)
  contMDiff := g.contMDiff.add_section g.contMDiff

theorem twiceMetric_inner (g : SmoothMetric) (p : Base) (X Y : Tangent p) :
    (twiceMetric g).inner p X Y = 2 * g.inner p X Y := (two_mul ..).symm

private def sphereRetract (z : E3) : Sphere :=
  if hz : z = 0 then equatorPoint 0 else
    ⟨NormedSpace.normalize z,mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hz)⟩

private theorem retract_smooth {z : E3} (hz : z ≠ 0) :
    ContMDiffAt 𝓘(ℝ,E3) (𝓡 2) ∞ sphereRetract z := by
  let O : TopologicalSpace.Opens E3 := ⟨{x | x ≠ 0},isOpen_ne_fun continuous_id continuous_const⟩
  let incl := (Subtype.val : O → E3)
  have si : ContMDiff 𝓘(ℝ,E3) 𝓘(ℝ,E3) ∞ incl := contMDiff_subtype_val
  have h (x : O) : incl x ≠ 0 := x.property
  have smooth : ContMDiff 𝓘(ℝ,E3) 𝓘(ℝ,E3) ∞ (fun x : O => NormedSpace.normalize (incl x)) := by
    intro x
    exact (((contDiffAt_norm ℝ (h x)).contMDiffAt.comp x si.contMDiffAt).inv₀ (norm_ne_zero_iff.mpr (h x))).smul
      si.contMDiffAt
  have mem (x : O) := mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (h x))
  apply (contMDiffAt_subtype_iff (U := O) (x := ⟨z,hz⟩)).mp
  convert (smooth.codRestrict_sphere mem).contMDiffAt (x := (⟨z,hz⟩ : O)) using 1
  funext x; simp [sphereRetract,h x,Set.codRestrict,incl]

private def asEuclidean : R3 →L[ℝ] E3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap

def ambientRetract (v : Cheeger.V) : Base :=
  (sphereRetract (asEuclidean v.1),sphereRetract (asEuclidean v.2))

theorem ambientRetract_point (p : Base) : ambientRetract (ambientPoint p) = p := by
  have one (x : Sphere) : sphereRetract x.val = x := by
    have hx := mem_sphere_zero_iff_norm.mp x.property
    have ne : x.val ≠ 0 := by intro e; simp [e] at hx
    exact Subtype.ext (by simp [sphereRetract,ne,NormedSpace.normalize_eq_self_of_norm_eq_one hx])
  exact Prod.ext (one p.1) (one p.2)

/-- Radial retraction in the two ambient Euclidean factors is smooth near the sphere product. -/
theorem ambientRetract_smooth (p : Base) :
    ContMDiffAt 𝓘(ℝ,Cheeger.V) productModel ∞ ambientRetract (ambientPoint p) := by
  have nonzero (q : Sphere) : q.val ≠ 0 := by
    intro eq
    have h := mem_sphere_zero_iff_norm.mp q.property
    simp [eq] at h
  have f : ContDiff ℝ ∞ (fun v : Cheeger.V => asEuclidean v.1) := asEuclidean.contDiff.comp contDiff_fst
  have g : ContDiff ℝ ∞ (fun v : Cheeger.V => asEuclidean v.2) := asEuclidean.contDiff.comp contDiff_snd
  have a := (retract_smooth (z := asEuclidean (ambientPoint p).1) (nonzero p.1)).comp
    (f := fun v : Cheeger.V => asEuclidean v.1) (ambientPoint p) f.contMDiff.contMDiffAt
  have b := (retract_smooth (z := asEuclidean (ambientPoint p).2) (nonzero p.2)).comp
    (f := fun v : Cheeger.V => asEuclidean v.2) (ambientPoint p) g.contMDiff.contMDiffAt
  exact a.prodMk b

private abbrev Inputs := Cheeger.V × Cheeger.V × Cheeger.V

private def regularInputs : Set Inputs :=
  {q | asEuclidean q.1.1 ≠ 0 ∧ asEuclidean q.1.2 ≠ 0}

private theorem open_regular : IsOpen regularInputs :=
  (isOpen_ne_fun (asEuclidean.continuous.comp (continuous_fst.comp continuous_fst)) continuous_const).inter
    (isOpen_ne_fun (asEuclidean.continuous.comp (continuous_snd.comp continuous_fst)) continuous_const)

private def evaluate (H : AmbientTensor) (z : Inputs) := H.form (ambientRetract z.1) z.2.1 z.2.2

private theorem evaluate_smooth (H : AmbientTensor) {z : Inputs} (hz : z ∈ regularInputs) :
    ContDiffAt ℝ ∞ (evaluate H) z := by
  have f : ContDiff ℝ ∞ (fun q : Inputs => asEuclidean q.1.1) :=
    asEuclidean.contDiff.comp (contDiff_fst.comp contDiff_fst)
  have g : ContDiff ℝ ∞ (fun q : Inputs => asEuclidean q.1.2) :=
    asEuclidean.contDiff.comp (contDiff_snd.comp contDiff_fst)
  have r : ContMDiffAt 𝓘(ℝ,Inputs) productModel ∞ (fun q : Inputs => ambientRetract q.1) z :=
    ((retract_smooth hz.1).comp z f.contDiffAt.contMDiffAt).prodMk
      ((retract_smooth hz.2).comp z g.contDiffAt.contMDiffAt)
  exact (((H.smooth.contMDiffAt.comp z r).contDiffAt.clm_apply
    (contDiffAt_fst.comp z contDiffAt_snd)).clm_apply (contDiffAt_snd.comp z contDiffAt_snd))

private def chartInputs (p : Base) (a b x : Coordinates) : Inputs :=
  (ambientPoint ((extChartAt productModel p).symm x),chartVelocity p a x,chartVelocity p b x)

private theorem input_smooth {p : Base} (a b : Coordinates) {x : Coordinates}
    (hx : x ∈ (extChartAt productModel p).target) : ContDiffAt ℝ ∞ (chartInputs p a b) x :=
  ((ambientPoint_smooth.contMDiffAt.comp x (chart_smooth hx)).contDiffAt).prodMk
    ((velocity_smooth a hx).prodMk (velocity_smooth b hx))

private theorem input_regular (p : Base) (a b x : Coordinates) : chartInputs p a b x ∈ regularInputs := by
  have ne (v : Sphere) : v.val ≠ 0 := by
    have h := mem_sphere_zero_iff_norm.mp v.property
    intro e; simp [e] at h
  let v := (extChartAt productModel p).symm x
  exact ⟨ne v.1,ne v.2⟩

private def inputBox (n : ℕ) : Set Inputs :=
  range ambientPoint ×ˢ closedBall 0 (n:ℝ) ×ˢ closedBall 0 (n:ℝ)

private theorem compact_box (n : ℕ) : IsCompact (inputBox n) :=
  (isCompact_range ambientPoint_smooth.continuous).prod ((isCompact_closedBall ..).prod (isCompact_closedBall ..))

private theorem box_regular {n : ℕ} {q : Inputs} (hq : q ∈ inputBox n) : q ∈ regularInputs := by
  obtain ⟨p,hp⟩ := hq.1
  have ne (v : Sphere) : v.val ≠ 0 := by
    have h := mem_sphere_zero_iff_norm.mp v.property
    intro e; simp [e] at h
  change _ ≠ 0 ∧ _ ≠ 0
  rw [← hp]
  exact ⟨ne p.1,ne p.2⟩

private def perturbationError (A : Fin 4 → AmbientTensor) (s : ℝ) (q : Inputs) :=
  2*(s*evaluate (A 1) q + s^2*evaluate (A 2) q + s^3*evaluate (A 3) q)

private theorem error_smooth (A : Fin 4 → AmbientTensor) {s : ℝ} {q : Inputs} (hq : q ∈ regularInputs) :
    ContDiffAt ℝ ∞ (uncurry (perturbationError A)) (s,q) := by
  have h (i : Fin 4) : ContDiffAt ℝ ∞ (fun z : ℝ × Inputs => evaluate (A i) z.2) (s,q) :=
    (evaluate_smooth (A i) hq).comp (s,q) contDiffAt_snd
  exact contDiffAt_const.mul (((contDiffAt_fst.mul (h 1)).add ((contDiffAt_fst.pow 2).mul (h 2))).add
    ((contDiffAt_fst.pow 3).mul (h 3)))

private theorem small_error (A : Fin 4 → AmbientTensor) (n : ℕ) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ i ≤ n, ∀ q ∈ inputBox n,
      ‖iteratedFDeriv ℝ i (perturbationError A s) q‖ ≤ 1/((n:ℝ)+1) := by
  have zero : perturbationError A 0 = 0 := by funext q; simp [perturbationError]
  have each (i : Fin (n+1)) : ∀ᶠ s in 𝓝 (0:ℝ), ∀ q ∈ inputBox n,
      ‖iteratedFDeriv ℝ i.val (perturbationError A s) q‖ ≤ 1/((n:ℝ)+1) := by
    have h := compact_jets (uncurry (perturbationError A)) (compact_box n)
      (fun q hq => error_smooth A (box_regular hq)) i.val
    have v := (Metric.tendstoUniformlyOn_iff.mp h (1/((n:ℝ)+1)) (by positivity))
    filter_upwards [v] with s hs q hq
    simpa [uncurry,zero] using (hs q hq).le
  filter_upwards [(Filter.eventually_all.mpr each).filter_mono nhdsWithin_le_nhds] with s hs i hi
  exact hs ⟨i,Nat.lt_succ_of_le hi⟩

private theorem derivative_bounds {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {S : Set E} (hS : IsCompact S)
    (hf : ∀ x ∈ S, ContDiffAt ℝ ∞ f x) (j : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ j, ∀ x ∈ S, ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
  have bounded (i : ℕ) := hS.exists_bound_of_continuousOn
    (fun x hx => ((hf x hx).continuousAt_iteratedFDeriv (by simp : (i:ℕ∞ω) ≤ ∞)).continuousWithinAt)
  choose C hC using bounded
  obtain ⟨R,hR⟩ := (finite_range (fun i : Fin (j+1) => C i)).bddAbove
  exact ⟨max 1 R,le_max_left ..,fun i hi x hx => (hC i x hx).trans
    ((hR (mem_range_self (⟨i,Nat.lt_succ_of_le hi⟩ : Fin (j+1)))).trans (le_max_right ..))⟩

/-- The diagonal estimates on ambient inputs control the derivatives in an
arbitrary product chart, including its two coordinate vector fields. -/
private theorem error_chart_bound (A : ℕ → Fin 4 → AmbientTensor) (s : ℕ → ℝ)
    (h : ∀ n i, i ≤ n → ∀ q ∈ inputBox n, ‖iteratedFDeriv ℝ i (perturbationError (A n) (s n)) q‖ ≤ 1/((n:ℝ)+1))
    (p : Base) (a b : Coordinates) (j : ℕ) {K : Set Coordinates} (hK : IsCompact K)
    (hs : K ⊆ (extChartAt productModel p).target) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (perturbationError (A n) (s n) ∘ chartInputs p a b) x‖ < ε := by
  let f := chartInputs p a b
  let S := (extChartAt productModel p).target
  have os : IsOpen S := isOpen_extChartAt_target p
  have sm : ContDiffOn ℝ ∞ f S := fun _ hx => (input_smooth a b hx).contDiffWithinAt
  obtain ⟨D,hD,bound⟩ := derivative_bounds hK (fun _ hx => input_smooth a b (hs hx)) j
  obtain ⟨N,hN⟩ := exists_nat_ge D
  intro ε hε
  have lim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((j.factorial:ℝ)*D^j)
  rw [mul_zero] at lim
  filter_upwards [lim.eventually (gt_mem_nhds hε),eventually_ge_atTop j,eventually_ge_atTop N] with n small hj hn x hx
  have nf : ‖f x‖ ≤ (n:ℝ) :=
    (by simpa only [norm_iteratedFDeriv_zero] using bound 0 (Nat.zero_le j) x hx : ‖f x‖ ≤ D).trans
      (hN.trans (by exact_mod_cast hn))
  have loc : f x ∈ inputBox n := by
    refine ⟨mem_range_self _,?_,?_⟩ <;> rw [mem_closedBall,dist_zero_right]
    · exact (norm_fst_le (f x).2).trans ((norm_snd_le (f x)).trans nf)
    · exact (norm_snd_le (f x).2).trans ((norm_snd_le (f x)).trans nf)
  let g := perturbationError (A n) (s n)
  have sg : ContDiffOn ℝ ∞ g regularInputs := fun q hq =>
    ((error_smooth (A n) (s := s n) hq).comp (f := fun v : Inputs => (s n,v)) q
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  have comp := norm_iteratedFDerivWithin_comp_le sg sm (by simp : (j:ℕ∞ω) ≤ ∞)
    open_regular.uniqueDiffOn os.uniqueDiffOn (fun z _ => input_regular p a b z) (hs hx)
    (C := 1/((n:ℝ)+1)) (D := D)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i open_regular (input_regular p a b x)]
      exact h n i (hi.trans hj) (f x) loc)
    (fun i hi hij => by rw [iteratedFDerivWithin_of_isOpen i os (hs hx)]
                        exact (bound i hij x hx).trans (by simpa using pow_le_pow_right₀ hD hi))
  rw [iteratedFDerivWithin_of_isOpen j os (hs hx)] at comp
  exact comp.trans_lt (by simpa only [mul_right_comm (j.factorial:ℝ)] using small)

/-- Choose the perturbations small enough for all compact chart tests at once.
The potentials may vary arbitrarily with the background parameter. Any extra
property available for all sufficiently small positive parameters is preserved. -/
theorem diagonal_paper_metrics (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (ht₀ : Tendsto t atTop (𝓝 0))
    (χ : ℕ → Scalar) (P : ℕ → ℝ → SmoothMetric → Prop)
    (avail : ∀ n, ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric,
      Realizes g s (paperCoefficients (t n) (ht n) (χ n)) ∧ P n s g) :
    ∃ (s : ℕ → ℝ) (g : ℕ → SmoothMetric), (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝[>] 0) ∧
      (∀ n, Realizes (g n) (s n) (paperCoefficients (t n) (ht n) (χ n)) ∧ P n (s n) (g n)) ∧
      ConvergesToRound (fun n => twiceMetric (g n)) := by
  let A := fun n => paperCoefficients (t n) (ht n) (χ n)
  have pick (n : ℕ) : ∃ s : ℝ, ∃ g : SmoothMetric, (0 < s ∧ s < 1/((n:ℝ)+1)) ∧
      (Realizes g s (A n) ∧ P n s g) ∧ ∀ i ≤ n, ∀ q ∈ inputBox n,
        ‖iteratedFDeriv ℝ i (perturbationError (A n) s) q‖ ≤ 1/((n:ℝ)+1) := by
    have win₀ : ∀ᶠ s in 𝓝[>] (0:ℝ), s ∈ Ioo 0 (1/((n:ℝ)+1)) := Ioo_mem_nhdsGT (by positivity)
    obtain ⟨s,win,⟨g,real,prop⟩,bound⟩ := (win₀.and ((avail n).and (small_error (A n) n))).exists
    exact ⟨s,g,win,⟨real,prop⟩,bound⟩
  choose s g win good bound using pick
  have s₀ : Tendsto s atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨squeeze_zero (fun n => (win n).1.le) (fun n => (win n).2.le) tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => (win n).1⟩
  refine ⟨s,g,fun n => (win n).1,s₀,good,?_⟩
  intro p a b j K hK hs
  let F := backgroundChart p a b
  let f := chartInputs p a b
  let err := fun n => perturbationError (A n) (s n) ∘ f
  have metric (n : ℕ) : chartCoefficient (fun q X Y => (twiceMetric (g n)).inner q X Y) p a b =
      (fun z => F (t n,z)) + err n := by
    funext z
    dsimp only [err,f,F,backgroundChart,perturbationError,chartInputs,evaluate,chartVelocity,chartCoefficient,
      Function.comp_apply,Pi.add_apply]
    rw [twiceMetric_inner,(good n).1,ambientRetract_point]
    simp only [cubicValue,smul_eq_mul]
    rw [show (A n 0).form = ambientBackground (t n) from rfl]
    ring
  have bg := background_chart_convergence p a b j K hK hs
  rw [Metric.tendstoUniformlyOn_iff] at bg ⊢
  intro ε hε
  have he := half_pos hε
  filter_upwards [ht₀.eventually (bg (ε/2) he),error_chart_bound A s bound p a b j hK hs (ε/2) he] with n hb hr z hz
  have breg : ContDiffAt ℝ ∞ (fun x => F (t n,x)) z := (smooth_backgroundChart p a b (ht n) (hs hz)).comp
    (f := fun x : Coordinates => (t n,x)) z (contDiffAt_const.prodMk contDiffAt_id)
  have ereg : ContDiffAt ℝ ∞ (err n) z := (error_smooth (A n) (s := s n) (input_regular p a b z)).comp
    (f := fun x => (s n,f x)) z (contDiffAt_const.prodMk (input_smooth a b (hs hz)))
  rw [metric n,iteratedFDeriv_add_apply (breg.of_le (by simp)) (ereg.of_le (by simp))]
  refine (dist_triangle _ (iteratedFDeriv ℝ j (fun x => F (t n,x)) z) _).trans_lt ?_
  exact (add_lt_add (hb z hz) (show dist _ _ < ε / 2 by simpa [dist_eq_norm] using hr z hz)).trans_eq (add_halves ε)

/-- Passing from the unscaled perturbations to the normalization in §7 preserves positivity. -/
theorem twiceMetric_positive {g : SmoothMetric} (hg : PositiveSectionalCurvature g) :
    PositiveSectionalCurvature (twiceMetric g) := by
  intro p X Y hX hY hXY
  let c := Real.sqrt 2
  have sq : c^2 = 2 := Real.sq_sqrt (by norm_num)
  have pair (A B : Tangent p) : g.inner p (c • A) (c • B) = (twiceMetric g).inner p A B := by
    simp only [map_smul,smul_apply,smul_eq_mul,twiceMetric_inner]
    rw [← mul_assoc,← sq,pow_two]
  have pos := hg p (c • X) (c • Y) ((pair X X).trans hX) ((pair Y Y).trans hY) ((pair X Y).trans hXY)
  have scale (q : Base) (A B : Tangent q) : g.inner q A B = (1/2:ℝ) * (twiceMetric g).inner q A B := by
    rw [twiceMetric_inner]; ring
  rw [curvatureNumerator_homothety (by norm_num : (1/2:ℝ) ≠ 0) scale,
    show c^4 = 4 by rw [show 4 = 2*2 by decide,pow_mul,sq]; norm_num] at pos
  linarith

/-- Positive curvature on small parameter windows along one sequence of backgrounds
implies the concrete Local Hopf proposition on the product of unit spheres. -/
theorem localHopfProblem_of_positive_windows (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (ht₀ : Tendsto t atTop (𝓝 0)) (χ : ℕ → Scalar)
    (windows : ∀ n, ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric,
      Realizes g s (paperCoefficients (t n) (ht n) (χ n)) ∧ PositiveSectionalCurvature g) :
    LocalHopfProblem := by
  obtain ⟨s,g,_,_,good,lim⟩ := diagonal_paper_metrics t ht ht₀ χ
    (fun _ _ g => PositiveSectionalCurvature g) windows
  exact ⟨fun n => twiceMetric (g n),fun n => twiceMetric_positive (good n).2,lim⟩

/-- The finite frame covers of Theorem 3.4 imply the concrete sphere-product
conclusion. Their index sets, neighborhoods and constants may depend on n. -/
theorem localHopfProblem_of_background_covers {ι : ℕ → Type*} [∀ n, Finite (ι n)]
    {D P E : Type*} [TopologicalSpace D] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (ht₀ : Tendsto t atTop (𝓝 0)) (χ : ℕ → Scalar)
    (c : (n : ℕ) → ι n → NormalChart P E)
    (near : ∀ n i, (c n i).Estimates (paperCoefficients (t n) (ht n) (χ n)))
    (far : ℕ → D → TangentPair) (S : ℕ → Set D) (compact : ∀ n, IsCompact (S n))
    (farCont : ∀ n w, w ∈ S n → ContinuousAt (fun q : D × ℝ =>
      (far n q.1).numerator (paperCoefficients (t n) (ht n) (χ n)) q.2) (w,0))
    (farPos : ∀ n w, w ∈ S n → 0 < (far n w).numerator (paperCoefficients (t n) (ht n) (χ n)) 0)
    (U : ℕ → Set FrameCoordinates) (hopen : ∀ n, IsOpen (U n))
    (hbg : ∀ n, backgroundFrames (t n) (ht n) ⊆ U n)
    (cover : ∀ n (w : TangentPair), w.toAmbient ∈ U n → (∃ d ∈ S n, far n d = w) ∨
      ∃ i : ι n, ∃ x ∈ (c n i).core, ∃ z : E, ‖z‖ ≤ (c n i).radius ∧ (c n i).frame (x,z) = w) :
    LocalHopfProblem :=
  localHopfProblem_of_positive_windows t ht ht₀ χ fun n =>
    positive_metrics_of_background_cover (t n) (ht n) (χ n) (c n) (near n)
      (far n) (S n) (compact n) (farCont n) (farPos n) (U n) (hopen n) (hbg n) (cover n)


end
end LocalHopf.SphereProduct
