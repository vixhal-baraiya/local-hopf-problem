import LocalHopf.PerturbationEntries
import LocalHopf.GraphMinimum

/-! The full uncorrected curvature used by the quadratic and equatorial cubic calculations. -/
namespace LocalHopf.SphereProduct.JetChart
open Real Matrix Filter Set LongitudeHeight
open scoped Topology ContDiff
noncomputable section

private abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Covariant spatial matrix jet of the uncorrected family at any amplitude. -/
def uncorrectedTaylor (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (h : ℝ) (d : Params)
    (m : Fin 3) : M4 :=
  let G := metricTaylor t (v.val.2.1.val ⬝ᵥ v.val.2.2.val) ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val) d
  fun i j => G m i j + h*firstTensorTaylor v t ht d i j m + h^2*secondTensorTaylor v t ht d i j m

set_option maxHeartbeats 900000 in
theorem uncorrected_jet (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) {h : ℝ} {g : SmoothMetric}
    (hg : Realizes g h (paperCoefficients t ht 0)) (d : Params) (i j : Fin 4) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let T := uncorrectedTaylor v t ht h d
    SpatialJet (fun z : ℝ => coefficient r s g (parameterBasis i) (parameterBasis j) (z • d))
      (T 0 i j) (T 1 i j) (T 2 i j) := by
  intro r s T
  have J := jet_add (jet_add (coordinate_gram_jet v t ht d i j) (jet_scale h (firstTensor_jet v t ht d i j)))
    (jet_scale (h^2) (secondTensor_jet v t ht d i j))
  refine J.congr ?_
  filter_upwards with z
  let p := (coreChart v).symm (z • d)
  let V (k : Fin 4) := field r s (parameterBasis k) p
  change g.inner p (V i) (V j) = _
  rw [hg]
  let U := ambientVelocityL p (V i)
  let W := ambientVelocityL p (V j)
  have e : (thirdOrderTensor t ht 0).form p U W = 0 := by
    change (2*Profiles.hh t*0) * ambientBackground t p U W=0
    ring
  change _ + h^3 * (thirdOrderTensor t ht 0).form p U W = _
  rw [e,mul_zero,add_zero]
  rfl

/-- Ordinary finite matrix expression for the uncorrected curvature in the verifier's frame. -/
def uncorrectedNumerator (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (h : ℝ) (a b : Params) :=
  let T := uncorrectedTaylor v t ht h
  contractSpatial T (T 0 0)⁻¹ a b

theorem curvature_eq_uncorrectedNumerator (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) {h : ℝ}
    {g : SmoothMetric} (hg : Realizes g h (paperCoefficients t ht 0)) (a b : Params) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    curvatureNumerator g p (field r s a p) (field r s b p) = uncorrectedNumerator v t ht h a b := by
  apply curvature_from_spatial_terms v g (uncorrectedTaylor v t ht h)
  · exact uncorrected_jet v t ht hg
  · congr 1
    ext i j
    simpa only [zero_smul] using (uncorrected_jet v t ht hg 0 i j).value

/-- Normalized derivatives on an arbitrary tilt ray in the verifier's frame.
The amplitude-dependent two-plane and the base metric use the same parameter. -/
theorem graphCoefficient_eq_uncorrected (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t)
    (z : Fin 4 → ℝ) (n : ℕ) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    let e (i : Fin 4) := field r s (parameterBasis i) p
    let A := paperCoefficients t ht 0
    let f (h : ℝ) := uncorrectedNumerator v t ht h ((1,0),h*z 0,h*z 1) ((0,1),h*z 2,h*z 3)
    graphCoefficient A (e 0) (e 1) (e 2) (e 3) n z = iteratedDeriv n f 0 / n.factorial := by
  intro r s p e A f
  let F := graphNumerator A (e 0) (e 1) (e 2) (e 3)
  have hx : (0:Params) ∈ (chart r s).target := (center v).1
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target hx)
  have field_eq (a b : ℝ) (i : Fin 4) (q : Params) (hq : parameterBasis i+a • parameterBasis 2+b • parameterBasis 3=q) :
      e i+a • e 2+b • e 3=field r s q p := by
    have eq := congrArg L hq
    simp only [map_add,map_smul] at eq
    simpa only [hL] using eq
  have eq : (fun h : ℝ => F (0,h • z,h)) =ᶠ[𝓝 0] f := by
    filter_upwards [paper_metrics_realize t ht (0:Scalar)] with h real
    obtain ⟨g,hg⟩ := real
    let a : Params := ((1,0),h*z 0,h*z 1)
    let b : Params := ((0,1),h*z 2,h*z 3)
    have left := field_eq (h*z 0) (h*z 1) 0 a (by ext <;> simp [parameterBasis_apply,a])
    have right := field_eq (h*z 2) (h*z 3) 1 b (by ext <;> simp [parameterBasis_apply,b])
    change (tiltedPair (e 0) (e 1) (e 2) (e 3) (h • z)).numerator A h = _
    rw [TangentPair.numerator_eq _ hg]
    change curvatureNumerator g p (e 0 + (h*z 0) • e 2 + (h*z 1) • e 3)
      (e 1 + (h*z 2) • e 2 + (h*z 3) • e 3) = _
    rw [left,right]
    exact curvature_eq_uncorrectedNumerator v t ht hg a b
  change graphCoefficient A (e 0) (e 1) (e 2) (e 3) n z = _
  calc
    _ = UniformTube.coeff F n 0 z := (graph_coeff_eq_quotient t ht 0 p (e 0) (e 1) (e 2) (e 3) z n).symm
    _ = _ := congrArg (· / (n.factorial : ℝ)) (eq.iteratedDeriv_eq (n := n))

private theorem amplitudeJet (c : Fin 4 → ℝ) : SpatialJet (fun z => cubicValue z c) (c 0) (c 1) (c 2) := by
  have I : SpatialJet (id : ℝ → ℝ) 0 1 0 := ⟨contDiffAt_id,rfl,by simp,by simp [iteratedDeriv_id]⟩
  have J := jet_add (jet_add (jet_add (jet_const (c 0)) (jet_scale (c 1) I))
    (jet_scale (c 2) (jet_mul I I))) (jet_scale (c 3) (jet_mul (jet_mul I I) I))
  simp only [mul_zero,zero_add,add_zero,mul_one] at J
  apply J.congr
  filter_upwards with z; dsimp [cubicValue]; ring

/-- At a flat longitude plane the quadratic metric contribution is linear in the
second tensor. The nonlinear part uses only the first symbols and the background inverse. -/
theorem tensorNumerator_second (r s : E3 ≃ₗᵢ[ℝ] E3) (A : Fin 4 → AmbientTensor)
    (base : Module.Basis (Fin 4) ℝ Params) (y a b : Params)
    (hd : Matrix.det (fun i j : Fin 4 => tensor r s (A 0) (base i) (base j) y) ≠ 0)
    (flat : ∀ d, symbol (tensor r s (A 0)) a a d y = 0 ∧ symbol (tensor r s (A 0)) a b d y = 0 ∧
      symbol (tensor r s (A 0)) b b d y = 0) :
    let G : Matrix (Fin 4) (Fin 4) ℝ := fun i j => tensor r s (A 0) (base i) (base j) y
    let J (u w : Params) (i : Fin 4) := symbol (tensor r s (A 1)) u w (base i) y
    iteratedDeriv 2 (tensorNumerator r s A base y a b) 0 / 2 =
      second (tensor r s (A 2)) a b y + J a b ⬝ᵥ G⁻¹ *ᵥ J a b - J a a ⬝ᵥ G⁻¹ *ᵥ J b b := by
  intro G J
  let M (z : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => cubicValue z (fun k => tensor r s (A k) (base i) (base j) y)
  let S (u w : Params) (i : Fin 4) (z : ℝ) := cubicValue z (fun k => symbol (tensor r s (A k)) u w (base i) y)
  let pair (u w l k : Params) (z : ℝ) := (fun i => S u w i z) ⬝ᵥ (M z)⁻¹ *ᵥ (fun i => S l k i z)
  have val : M 0=G := by ext; simp [M,G,cubicValue]
  have sm (i j : Fin 4) : ContDiff ℝ ∞ (fun z => M z i j) := by dsimp [M,cubicValue]; fun_prop
  have det {n : Type} [Fintype n] [DecidableEq n] (L : ℝ → Matrix n n ℝ)
      (hL : ∀ i j, ContDiff ℝ ∞ (fun q => L q i j)) : ContDiff ℝ ∞ (fun q => (L q).det) := by
    simp only [Matrix.det_apply']
    exact ContDiff.sum fun _ _ => contDiff_const.mul (contDiff_prod fun i _ => hL _ _)
  have inv (i j : Fin 4) : ContDiffAt ℝ ∞ (fun z => (M z)⁻¹ i j) 0 := by
    have adj : ContDiff ℝ ∞ (fun z => (M z).adjugate i j) := by
      simp only [adjugate_fin_succ_eq_det_submatrix]
      exact contDiff_const.mul (det (fun z => (M z).submatrix j.succAbove i.succAbove) (fun _ _ => sm _ _))
    simp only [inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
    exact ((det M sm).contDiffAt.inv (val ▸ hd)).mul adj.contDiffAt
  have pairing (u w l k : Params) (hu : ∀ i, symbol (tensor r s (A 0)) u w (base i) y=0)
      (hl : ∀ i, symbol (tensor r s (A 0)) l k (base i) y=0) :
      SpatialJet (pair u w l k) 0 0 (J u w ⬝ᵥ G⁻¹ *ᵥ J l k) := by
    have term (i j : Fin 4) : SpatialJet (fun z => S u w i z * ((M z)⁻¹ i j * S l k j z))
        0 0 (J u w i * (G⁻¹ i j * J l k j)) := by
      let f (z : ℝ) := (M z)⁻¹ i j
      have m : SpatialJet f (f 0) (deriv f 0) (iteratedDeriv 2 f 0/2) :=
        ⟨inv i j,rfl,rfl,by ring⟩
      have U := amplitudeJet (fun n => symbol (tensor r s (A n)) u w (base i) y)
      have V := amplitudeJet (fun n => symbol (tensor r s (A n)) l k (base j) y)
      have Z := jet_mul U (jet_mul m V)
      simpa only [f,hu,hl,val,mul_zero,zero_mul,add_zero,zero_add,J,S] using Z
    have jets := jet_sum fun i => jet_sum (term i)
    simp only [Finset.sum_const_zero] at jets
    simpa only [pair,Matrix.mulVec,dotProduct,Finset.mul_sum] using jets
  have X := amplitudeJet (fun j => second (tensor r s (A j)) a b y)
  have U := pairing a b a b (fun i => (flat _).2.1) (fun i => (flat _).2.1)
  have V := pairing a a b b (fun i => (flat _).1) (fun i => (flat _).2.2)
  have h := (jet_sub (jet_add X U) V).second
  change iteratedDeriv 2 (tensorNumerator r s A base y a b) 0 = 2*_ at h
  linarith only [h]

end
end LocalHopf.SphereProduct.JetChart
