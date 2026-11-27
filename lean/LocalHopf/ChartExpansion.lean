import LocalHopf.ChartJet

/-! Spatial differentiation of the four metric tensors in the longitude-height
chart before exact division by the determinant of the metric. -/
namespace LocalHopf.SphereProduct.JetChart
open Matrix Filter Set Bundle
open scoped Manifold Topology ContDiff
noncomputable section
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

/-- An ambient tensor evaluated on the two coordinate fields. -/
def tensor (r s : E3 ≃ₗᵢ[ℝ] E3) (A : AmbientTensor) (a b : Params) :=
  ambientPair A (field r s a) (field r s b) ∘ (chart r s).symm

def symbol (C : Params → Params → Params → ℝ) (a b d y : Params) :=
  (D a (C b d) y+D b (C d a) y-D d (C a b) y)/2

def second (C : Params → Params → Params → ℝ) (a b y : Params) :=
  D a (fun z => D b (C b a) z-D a (C b b) z/2) y-D b (fun z => D b (C a a) z/2) y

theorem tensor_smooth (r s : E3 ≃ₗᵢ[ℝ] E3) (A : AmbientTensor) (a b : Params)
    {y : Params} (hy : y ∈ (chart r s).target) : ContDiffAt ℝ ∞ (tensor r s A a b) y :=
  contMDiffAt_iff_contDiffAt.mp ((ambientPair_smooth A (field_smooth r s ((chart r s).map_target hy) a)
    (field_smooth r s ((chart r s).map_target hy) b)).comp y (inv_smooth r s hy))

private theorem smooth_D {f : Params → ℝ} {y : Params} (h : ContDiffAt ℝ ∞ f y) (d : Params) :
    ContDiffAt ℝ ∞ (D d f) y := (h.fderiv_right (by simp : ∞+1 ≤ ∞)).clm_apply contDiffAt_const

private theorem D_cubic (h : ℝ) (f : Fin 4 → Params → ℝ) (d y : Params)
    (reg : ∀ i, DifferentiableAt ℝ (f i) y) :
    D d (fun z => cubicValue h (fun i => f i z)) y = cubicValue h (fun i => D d (f i) y) := by
  have df := ((((reg 0).hasFDerivAt.add ((reg 1).hasFDerivAt.const_smul h)).add
    ((reg 2).hasFDerivAt.const_smul (h^2))).add ((reg 3).hasFDerivAt.const_smul (h^3))).fderiv
  change fderiv ℝ ((f 0+h • f 1+h^2 • f 2+h^3 • f 3)) y d = _
  rw [df]
  rfl

/-- The coordinate second derivatives and first-kind symbols are polynomial
in the perturbation parameter, with the spatial derivatives taken tensor by tensor. -/
theorem tensor_jets (r s : E3 ≃ₗᵢ[ℝ] E3) {g : SmoothMetric} {h : ℝ} {A : Fin 4 → AmbientTensor}
    (hg : Realizes g h A) {y : Params} (hy : y ∈ (chart r s).target) (a b : Params) :
    (∀ d, christoffel r s g a b d y = cubicValue h (fun i => symbol (tensor r s (A i)) a b d y)) ∧
    second (coefficient r s g) a b y = cubicValue h (fun i => second (tensor r s (A i)) a b y) := by
  let T := fun i => tensor r s (A i)
  have val (u w : Params) : coefficient r s g u w = fun z => cubicValue h (fun i => T i u w z) :=
    funext fun _ => hg _ _ _
  have fst (u w l z : Params) (hz : z ∈ (chart r s).target) : D u (coefficient r s g w l) z =
      cubicValue h (fun i => D u (T i w l) z) := by
    rw [val]; exact D_cubic _ _ _ _ fun i => (tensor_smooth _ _ _ _ _ hz).differentiableAt (by simp)
  constructor
  · intro d
    rw [christoffel,fst _ _ _ _ hy,fst _ _ _ _ hy,fst _ _ _ _ hy]
    simp [symbol,T,cubicValue]; ring
  · let f (i : Fin 4) (z : Params) := D b (T i b a) z-D a (T i b b) z/2
    let k (i : Fin 4) (z : Params) := D b (T i a a) z/2
    have l : (fun z => D b (coefficient r s g b a) z-D a (coefficient r s g b b) z/2) =ᶠ[𝓝 y]
        fun z => cubicValue h (fun i => f i z) := by
      filter_upwards [(chart r s).open_target.mem_nhds hy] with z hz
      rw [fst _ _ _ _ hz,fst _ _ _ _ hz]; simp [f,cubicValue]; ring
    have m : (fun z => D b (coefficient r s g a a) z/2) =ᶠ[𝓝 y] fun z => cubicValue h (fun i => k i z) := by
      filter_upwards [(chart r s).open_target.mem_nhds hy] with z hz
      rw [fst _ _ _ _ hz]; simp [k,cubicValue]; ring
    have R (i : Fin 4) (u w d : Params) : ContDiffAt ℝ ∞ (D d (T i u w)) y :=
      smooth_D (tensor_smooth _ _ _ _ _ hy) _
    change fderiv ℝ _ y a - fderiv ℝ _ y b = _
    rw [l.fderiv_eq,m.fderiv_eq]
    change D a _ y - D b _ y = _
    rw [D_cubic h f a y (fun i => ((R i b a b).sub ((R i b b a).div_const 2)).differentiableAt (by simp)),
      D_cubic h k b y (fun i => ((R i a a b).div_const 2).differentiableAt (by simp))]
    simp [cubicValue,second,f,k,T]; ring

/-- The rational curvature jet in the script's own coordinates. -/
def tensorNumerator (r s : E3 ≃ₗᵢ[ℝ] E3) (A : Fin 4 → AmbientTensor) (base : Module.Basis (Fin 4) ℝ Params)
    (y a b : Params) (h : ℝ) :=
  let T := fun i => tensor r s (A i)
  let G : Matrix (Fin 4) (Fin 4) ℝ := fun i j => cubicValue h (fun k => T k (base i) (base j) y)
  let J (u w : Params) (i : Fin 4) := cubicValue h (fun k => symbol (T k) u w (base i) y)
  cubicValue h (fun i => second (T i) a b y) + J a b ⬝ᵥ G⁻¹ *ᵥ J a b - J a a ⬝ᵥ G⁻¹ *ᵥ J b b

theorem tensorNumerator_realizes (r s : E3 ≃ₗᵢ[ℝ] E3) {g : SmoothMetric} {h : ℝ} {A : Fin 4 → AmbientTensor}
    (hg : Realizes g h A) {y : Params} (hy : y ∈ (chart r s).target) (base : Module.Basis (Fin 4) ℝ Params)
    (a b : Params) :
    let p := (chart r s).symm y
    curvatureNumerator g p (field r s a p) (field r s b p) = tensorNumerator r s A base y a b h := by
  dsimp only
  rw [curvature_from_chart_jet r s ((chart r s).map_target hy) g base a b,(chart r s).right_inv hy]
  have hj := fun u w => (tensor_jets r s hg hy u w).1
  change second (coefficient r s g) a b y + _ - _ = _
  rw [(tensor_jets r s hg hy a b).2]
  have hc (i j : Fin 4) : coefficient r s g (base i) (base j) y =
      cubicValue h (fun k => tensor r s (A k) (base i) (base j) y) := hg _ _ _
  simp only [hj,tensorNumerator,hc]


private theorem cubic_deriv (c : Fin 4 → ℝ) : HasDerivAt (fun h => cubicValue h c) (c 1) 0 := by
  have d := (((hasDerivAt_const (0:ℝ) (c 0)).add ((hasDerivAt_id' (0:ℝ)).mul_const (c 1))).add
    (((hasDerivAt_id' (0:ℝ)).pow 2).mul_const (c 2))).add (((hasDerivAt_id' (0:ℝ)).pow 3).mul_const (c 3))
  convert d using 1 <;> simp [cubicValue]
  rfl

/-- When the background first-kind symbols on the two-plane vanish, varying the
inverse Gram matrix and the symbols gives zero at first order. -/
theorem tensorNumerator_deriv (r s : E3 ≃ₗᵢ[ℝ] E3) (A : Fin 4 → AmbientTensor) (base : Module.Basis (Fin 4) ℝ Params)
    (y a b : Params)
    (hd : Matrix.det (fun i j : Fin 4 => tensor r s (A 0) (base i) (base j) y) ≠ 0)
    (flat : ∀ d, symbol (tensor r s (A 0)) a a d y = 0 ∧ symbol (tensor r s (A 0)) a b d y = 0 ∧
      symbol (tensor r s (A 0)) b b d y = 0) :
    HasDerivAt (tensorNumerator r s A base y a b) (second (tensor r s (A 1)) a b y) 0 := by
  let T := fun i => tensor r s (A i)
  let G (h : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => cubicValue h (fun k => T k (base i) (base j) y)
  let J (u w : Params) (i : Fin 4) (h : ℝ) := cubicValue h (fun k => symbol (T k) u w (base i) y)
  have hG (i j : Fin 4) : ContDiff ℝ ∞ (fun h => G h i j) := by dsimp [G,cubicValue]; fun_prop
  have det {n : Type} [Fintype n] [DecidableEq n] (M : ℝ → Matrix n n ℝ)
      (hM : ∀ i j, ContDiff ℝ ∞ (fun q => M q i j)) : ContDiff ℝ ∞ (fun q => (M q).det) := by
    simp only [Matrix.det_apply']
    exact ContDiff.sum fun _ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)
  have nd : (G 0).det ≠ 0 := by simpa [G,cubicValue,T] using hd
  have dg (i j : Fin 4) : DifferentiableAt ℝ (fun q => (G q)⁻¹ i j) 0 := by
    have adj : ContDiff ℝ ∞ (fun q => (G q).adjugate i j) := by
      simp only [adjugate_fin_succ_eq_det_submatrix]
      exact contDiff_const.mul (det (fun q => (G q).submatrix j.succAbove i.succAbove) (fun a c => hG _ _))
    simp only [inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
    exact (((det G hG).differentiable (by simp) 0).inv nd).mul (adj.differentiable (by simp) 0)
  let pair (u w l k : Params) (h : ℝ) := (fun i => J u w i h) ⬝ᵥ (G h)⁻¹ *ᵥ (fun j => J l k j h)
  have one (u w l k : Params) (hu : ∀ i, symbol (T 0) u w (base i) y = 0)
      (hl : ∀ i, symbol (T 0) l k (base i) y = 0) : HasDerivAt (pair u w l k) 0 0 := by
    have e (i : Fin 4) : J u w i 0 = 0 := by simp [J,cubicValue,hu]
    have f (j : Fin 4) : J l k j 0 = 0 := by simp [J,cubicValue,hl]
    have jr (v z : Params) (i : Fin 4) : DifferentiableAt ℝ (J v z i) 0 := (cubic_deriv _).differentiableAt
    have entry (i : Fin 4) : DifferentiableAt ℝ (fun h => ∑ j, (G h)⁻¹ i j * J l k j h) 0 :=
      DifferentiableAt.fun_sum fun j _ => (dg i j).mul (jr l k j)
    have d (i : Fin 4) := ((jr u w i).hasDerivAt.mul (entry i).hasDerivAt)
    have row (i : Fin 4) : HasDerivAt (fun h => J u w i h * ∑ j, (G h)⁻¹ i j * J l k j h) 0 0 := by
      convert d i using 1
      simp only [e,f,mul_zero,Finset.sum_const_zero,zero_mul,add_zero]
    convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => row i) using 1 <;> first | rfl | simp
  have d := ((cubic_deriv (fun i => second (T i) a b y)).add
    (one a b a b (fun i => (flat _).2.1) (fun i => (flat _).2.1))).sub
    (one a a b b (fun i => (flat _).1) (fun i => (flat _).2.2))
  convert d using 1 <;> first | rfl | simp [T]



theorem tensor_second_add (r s : E3 ≃ₗᵢ[ℝ] E3) (P Q : AmbientTensor)
    (a b : Params) {y : Params} (hy : y ∈ (chart r s).target) :
    second (tensor r s (P+Q)) a b y = second (tensor r s P) a b y+second (tensor r s Q) a b y := by
  let F := tensor r s
  have d {q : Params} (hq : q∈(chart r s).target) (u v w : Params) :
      D u (F (P+Q) v w) q=D u (F P v w) q+D u (F Q v w) q := by
    have sm (T : AmbientTensor) := (tensor_smooth r s T v w hq).differentiableAt (by simp)
    change fderiv ℝ (F P v w+F Q v w) q u=_
    rw [fderiv_add (sm P) (sm Q),add_apply]; rfl
  let x (T : AmbientTensor) (q : Params) := D b (F T b a) q-D a (F T b b) q/2
  let z (T : AmbientTensor) (q : Params) := D b (F T a a) q/2
  have near := (chart r s).open_target.mem_nhds hy
  have sx : x (P+Q)=ᶠ[𝓝 y] x P+x Q := by
    filter_upwards [near] with q hq; dsimp [x]; rw [d hq,d hq]; ring
  have sz : z (P+Q)=ᶠ[𝓝 y] z P+z Q := by
    filter_upwards [near] with q hq; dsimp [z]; rw [d hq]; ring
  have sm (T : AmbientTensor) (d u v : Params) := smooth_D (tensor_smooth r s T u v hy) d
  have dx (T : AmbientTensor) : DifferentiableAt ℝ (x T) y :=
    ((sm T b b a).sub ((sm T a b b).div_const 2)).differentiableAt (by simp)
  have dz (T : AmbientTensor) : DifferentiableAt ℝ (z T) y := ((sm T b a a).div_const 2).differentiableAt (by simp)
  change fderiv ℝ (x (P+Q)) y a-fderiv ℝ (z (P+Q)) y b =
    (fderiv ℝ (x P) y a-fderiv ℝ (z P) y b)+(fderiv ℝ (x Q) y a-fderiv ℝ (z Q) y b)
  rw [sx.fderiv_eq,sz.fderiv_eq,fderiv_add (dx P) (dx Q),fderiv_add (dz P) (dz Q),add_apply,add_apply]
  ring

end
end LocalHopf.SphereProduct.JetChart
