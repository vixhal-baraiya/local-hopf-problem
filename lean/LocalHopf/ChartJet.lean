import LocalHopf.JetChart
import LocalHopf.BackgroundFormula
import LocalHopf.SectionalCoefficients

/-! The intrinsic numerator in the verifier's chart from ordinary spatial
derivatives of the Gram entries and one inverse Gram matrix. -/
namespace LocalHopf.SphereProduct.JetChart
open Bundle Filter Set VectorField Matrix
open scoped Manifold ContDiff Topology
noncomputable section
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
variable (r₁ r₂ : E3 ≃ₗᵢ[ℝ] E3)
local notation "φ" => chart r₁ r₂
local notation "X" => field r₁ r₂

def D (a : Params) (f : Params → ℝ) (q : Params) := fderiv ℝ f q a

def coefficient (g : SmoothMetric) (a b : Params) : Params → ℝ :=
  metricPair g (X a) (X b) ∘ (chart r₁ r₂).symm

private theorem pair_reg (g : SmoothMetric) {p : Base} (hp : p ∈ (chart r₁ r₂).source) (a b : Params) :
    ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ (metricPair g (X a) (X b)) p := by
  let : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  exact (field_smooth r₁ r₂ hp a).inner_bundle (field_smooth r₁ r₂ hp b)

private theorem deriv_chart {f : Base → ℝ} {p : Base} (hp : p ∈ (chart r₁ r₂).source)
    (hf : ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ f p) (a : Params) :
    directional (X a) f p = D a (f ∘ (chart r₁ r₂).symm) (φ p) := by
  apply directional_apply r₁ r₂ hp
  have h : ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ f ((chart r₁ r₂).symm (φ p)) := by rwa [(chart r₁ r₂).left_inv hp]
  exact (contMDiffAt_iff_contDiffAt.mp (h.comp _ (inv_smooth r₁ r₂ ((chart r₁ r₂).map_source hp)))).differentiableAt (by simp)

def christoffel (g : SmoothMetric) (a b c : Params) (q : Params) :=
  let C := coefficient r₁ r₂ g
  (D a (C b c) q + D b (C c a) q - D c (C a b) q)/2

private theorem gamma_chart {p : Base} (hp : p ∈ (chart r₁ r₂).source) (g : SmoothMetric) (a b c : Params) :
    firstKind g (X a) (X b) (X c) p = christoffel r₁ r₂ g a b c (φ p) := by
  have sm (u : Params) := (field_smooth r₁ r₂ hp u).mdifferentiableAt (by simp)
  rw [firstKind_koszul g _ _ _ p (sm _) (sm _) (sm _)]
  simp only [metricPair,fields_commute r₁ r₂ hp,map_zero,sub_zero,add_zero]
  rw [deriv_chart r₁ r₂ hp (pair_reg r₁ r₂ g hp b c), deriv_chart r₁ r₂ hp (pair_reg r₁ r₂ g hp c a),
    deriv_chart r₁ r₂ hp (pair_reg r₁ r₂ g hp a b)]
  rfl

private theorem second_chart {p : Base} (hp : p ∈ (chart r₁ r₂).source) (g : SmoothMetric) (a b : Params) :
    let U := X a
    let V := X b
    let C := coefficient r₁ r₂ g
    directional U (fun y => directional V (metricPair g V U) y - directional U (metricPair g V V) y/2) p -
      directional V (fun y => directional V (metricPair g U U) y/2) p =
    D a (fun q => D b (C b a) q - D a (C b b) q/2) (φ p) -
      D b (fun q => D b (C a a) q/2) (φ p) := by
  dsimp only
  have d (u v w : Params) := directional_smoothAt (field_smooth r₁ r₂ hp u) (pair_reg r₁ r₂ g hp v w)
  rw [deriv_chart r₁ r₂ hp ((d b b a).sub ((d a b b).div_const 2)) a,
    deriv_chart r₁ r₂ hp ((d b a a).div_const 2) b]
  have h (u v w : Params) : (directional (X u) (metricPair g (X v) (X w)) ∘ (chart r₁ r₂).symm)
      =ᶠ[𝓝 (φ p)] D u (coefficient r₁ r₂ g v w) := by
    filter_upwards [(chart r₁ r₂).open_target.mem_nhds ((chart r₁ r₂).map_source hp)] with y hy
    have hc := (chart r₁ r₂).map_target hy
    simpa only [Function.comp_apply,(chart r₁ r₂).right_inv hy,coefficient] using
      deriv_chart r₁ r₂ hc (pair_reg r₁ r₂ g hc v w) u
  have eq₁ := ((h b b a).sub ((h a b b).div (Filter.EventuallyEq.rfl (f := fun _ => (2 : ℝ))))).fderiv_eq (𝕜 := ℝ)
  have eq₂ := ((h b a a).div (Filter.EventuallyEq.rfl (f := fun _ => (2 : ℝ)))).fderiv_eq (𝕜 := ℝ)
  exact congrArg₂ (· - ·) (congrArg (fun L : Params →L[ℝ] ℝ => L a) eq₁)
    (congrArg (fun L : Params →L[ℝ] ℝ => L b) eq₂)


/-- The coordinate two-jet formula on the actual sphere product. Taking
`a = (1,0,z₁,z₂)` and `b = (0,1,z₃,z₄)` includes every graph tilt. -/
theorem curvature_from_chart_jet {p : Base} (hp : p ∈ (chart r₁ r₂).source)
    (g : SmoothMetric) (basis : Module.Basis (Fin 4) ℝ Params) (a b : Params) :
    let q := φ p
    let C := coefficient r₁ r₂ g
    let G : Matrix (Fin 4) (Fin 4) ℝ := fun i j => C (basis i) (basis j) q
    let Γ (v w : Params) := fun i => christoffel r₁ r₂ g v w (basis i) q
    curvatureNumerator g p (X a p) (X b p) =
      D a (fun y => D b (C b a) y - D a (C b b) y / 2) q - D b (fun y => D b (C a a) y / 2) q +
      Γ a b ⬝ᵥ G⁻¹ *ᵥ Γ a b - Γ a a ⬝ᵥ G⁻¹ *ᵥ Γ b b := by
  obtain ⟨L, hL⟩ := field_equiv r₁ r₂ hp
  let B : Frame p := basis.map L.toLinearEquiv
  have hB (i) : B i = X (basis i) p := by simpa [B] using hL (basis i)
  have gram : gramMatrix g B = fun i j => coefficient r₁ r₂ g (basis i) (basis j) (φ p) := by
    ext i j
    change _ = metricPair g _ _ ((chart r₁ r₂).symm (φ p))
    rw [(chart r₁ r₂).left_inv hp]
    simp only [gramMatrix,metricPair,hB]
  have gam (u v : Params) : frameCovector g B (nabla g (X u) (X v) p) =
      fun i => christoffel r₁ r₂ g u v (basis i) (φ p) := by
    funext i
    rw [frameCovector,hB,g.symm]
    exact gamma_chart r₁ r₂ hp g u v (basis i)
  dsimp only
  rw [numerator r₁ r₂ hp g,second_chart r₁ r₂ hp g]
  unfold metricPair
  rw [metric_inverse_pair g B,metric_inverse_pair g B,gram,gam,gam,gam]



/-- The differential of the pair of sphere inclusions is the ambient velocity
used in each of the paper's tensors. -/
theorem ambient_derivative (p : Base) : mvfderiv productModel ambientPoint p = ambientVelocityL p := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
  let f (q : Sphere) : R3 := q.val.ofLp
  have incl : MDifferentiable (𝓡 2) 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) :=
    (show ContMDiff (𝓡 2) 𝓘(ℝ,E3) ∞ (Subtype.val : Sphere → E3) from contMDiff_coe_sphere).mdifferentiable (by simp)
  have df (q : Sphere) : MDifferentiableAt (𝓡 2) 𝓘(ℝ,R3) f q :=
    L.differentiableAt.mdifferentiableAt.comp q (incl q)
  have deriv (q : Sphere) : mvfderiv (𝓡 2) f q = L.comp (velocity q) := by
    change mvfderiv (𝓡 2) (L ∘ Subtype.val) q = _
    rw [mvfderiv_comp q L.differentiableAt.mdifferentiableAt (incl q),
      mvfderiv_eq_fderiv, L.fderiv]
    rfl
  apply ContinuousLinearMap.ext
  intro x
  have proj (k : Cheeger.V →L[ℝ] R3) :
      k (mvfderiv productModel ambientPoint p x) = mvfderiv productModel (k ∘ ambientPoint) p x := by
    rw [mvfderiv_comp p k.differentiableAt.mdifferentiableAt (ambientPoint_smooth.mdifferentiable (by simp) p),
      mvfderiv_eq_fderiv,k.fderiv]
    rfl
  apply Prod.ext
  · calc _ = mvfderiv productModel (f ∘ Prod.fst) p x := proj (ContinuousLinearMap.fst ℝ R3 R3)
         _ = _ := by
           rw [mvfderiv_comp p (df p.1) mdifferentiableAt_fst, deriv, mfderiv_fst]
           rfl
  · calc _ = mvfderiv productModel (f ∘ Prod.snd) p x := proj (ContinuousLinearMap.snd ℝ R3 R3)
         _ = _ := by
           rw [mvfderiv_comp p (df p.2) mdifferentiableAt_snd, deriv, mfderiv_snd]
           rfl

/-- The velocity of each constant chart direction is the derivative of the
explicit rotated parametrization in the ambient six-dimensional space. -/
theorem ambient_field {p : Base} (hp : p ∈ (chart r₁ r₂).source) (a : Params) :
    ambientVelocityL p (X a p) = fderiv ℝ (ambientPoint ∘ (chart r₁ r₂).symm) (φ p) a := by
  rw [← ambient_derivative]
  apply derivative_field r₁ r₂ hp
  exact (contMDiffAt_iff_contDiffAt.mp (ambientPoint_smooth.contMDiffAt.comp _ (inv_smooth r₁ r₂
    ((chart r₁ r₂).map_source hp)))).differentiableAt (by simp)



/-- On the open chart, the scalar Gram coefficients differentiated in the jet
formula are the paper's ambient tensors evaluated on derivatives of the
explicit sphere parametrization. -/
theorem coefficient_realizes {g : SmoothMetric} {s : ℝ} {A : Fin 4 → AmbientTensor}
    (hg : Realizes g s A) {q : Params} (hq : q ∈ (chart r₁ r₂).target) (a b : Params) :
    let p := (chart r₁ r₂).symm q
    let v := fderiv ℝ (ambientPoint ∘ (chart r₁ r₂).symm) q
    coefficient r₁ r₂ g a b q = cubicValue s (fun i => (A i).form p (v a) (v b)) := by
  dsimp only
  change g.inner _ _ _ = _
  rw [hg,ambient_field r₁ r₂ ((chart r₁ r₂).map_target hq),ambient_field r₁ r₂ ((chart r₁ r₂).map_target hq),
      (chart r₁ r₂).right_inv hq]

/-- A closed expression for each intrinsic background Gram entry throughout
the open chart, including displacements in both heights. -/
theorem background_coefficient (r₁ r₂ : E3 ≃ₗᵢ[ℝ] E3) {q : Params} (hq : q ∈ (chart r₁ r₂).target)
    (t : ℝ) (ht : 0 ≤ t) (a b : Params) :
    let p := (chart r₁ r₂).symm q
    let P := (ambientPoint p).1
    let Q := (ambientPoint p).2
    let v := fderiv ℝ (ambientPoint ∘ (chart r₁ r₂).symm) q
    coefficient r₁ r₂ (backgroundMetric t ht) a b q =
      (gprod (v a) (v b)-t*(moment P Q (v b) ⬝ᵥ Cheeger.orbitSolve P Q t (moment P Q (v a))))/2 := by
  dsimp only
  let p := (chart r₁ r₂).symm q
  change ambientBackground t p (ambientVelocityL p (field r₁ r₂ a p))
    (ambientVelocityL p (field r₁ r₂ b p)) = _
  rw [ambientBackground_apply p ht,Cheeger.pairing_formula (ambientPoint p).1 (ambientPoint p).2 ht
    (unitSphere.symm p.1).property (unitSphere.symm p.2).property,
    ambient_field r₁ r₂ ((chart r₁ r₂).map_target hq),ambient_field r₁ r₂ ((chart r₁ r₂).map_target hq)]
  simp only [p,(chart r₁ r₂).right_inv hq]

end
end LocalHopf.SphereProduct.JetChart
