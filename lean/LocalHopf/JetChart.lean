import LocalHopf.LongitudeHeight
import LocalHopf.CurvatureFields
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! The two longitude-height charts and the change to the coordinates of
`quadratic_coefficient.chart`. The independent isometries permit a separate center
on each sphere, including at antipodal pairs. -/
namespace LocalHopf.SphereProduct.JetChart
open Bundle Filter Set VectorField Matrix
open scoped Manifold ContDiff Topology
noncomputable section

abbrev Params := (ℝ × ℝ) × (ℝ × ℝ)
private abbrev J := 𝓘(ℝ, Params)
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

def sphereAction (r : E3 ≃ₗᵢ[ℝ] E3) : Sphere ≃ₜ Sphere where
  toFun p := ⟨r p.val, mem_sphere_zero_iff_norm.mpr ((r.norm_map _).trans (mem_sphere_zero_iff_norm.mp p.property))⟩
  invFun p := ⟨r.symm p.val, mem_sphere_zero_iff_norm.mpr ((r.symm.norm_map _).trans (mem_sphere_zero_iff_norm.mp p.property))⟩
  left_inv _ := Subtype.ext (r.symm_apply_apply _)
  right_inv _ := Subtype.ext (r.apply_symm_apply _)
  continuous_toFun := (r.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (r.symm.continuous.comp continuous_subtype_val).subtype_mk _

private theorem smooth_act (r : E3 ≃ₗᵢ[ℝ] E3) : ContMDiff (𝓡 2) (𝓡 2) ∞ (sphereAction r) :=
  (r.toContinuousLinearEquiv.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere
    (fun p => (sphereAction r p).property)

private def mix : Params ≃ₜ Params where
  toFun q := (((q.1.1+q.2.1)/2,(q.2.1-q.1.1)/2),(q.1.2,q.2.2))
  invFun q := ((q.1.1-q.1.2,q.2.1),(q.1.1+q.1.2,q.2.2))
  left_inv := by rintro ⟨⟨a,b⟩,c,d⟩; simp only [Prod.mk.injEq, and_true]; constructor <;> ring
  right_inv := by rintro ⟨⟨a,b⟩,c,d⟩; simp only [Prod.mk.injEq, and_true]; constructor <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def rotated (r : E3 ≃ₗᵢ[ℝ] E3) := (sphereAction r.symm).toOpenPartialHomeomorph.trans LongitudeHeight.chart

def chart (r₁ r₂ : E3 ≃ₗᵢ[ℝ] E3) : OpenPartialHomeomorph Base Params :=
  ((rotated r₁).prod (rotated r₂)).trans mix.toOpenPartialHomeomorph

variable (r₁ r₂ : E3 ≃ₗᵢ[ℝ] E3)
local notation "e" => chart r₁ r₂

theorem chart_inv_apply (q : Params) : (chart r₁ r₂).symm q =
    (sphereAction r₁ (LongitudeHeight.point (q.1.1-q.1.2,q.2.1)), sphereAction r₂ (LongitudeHeight.point (q.1.1+q.1.2,q.2.2))) := rfl

theorem chart_smooth {p : Base} (hp : p ∈ (chart r₁ r₂).source) : ContMDiffAt productModel J ∞ e p := by
  have hr (r : E3 ≃ₗᵢ[ℝ] E3) (q : Sphere) (hr : sphereAction r.symm q ∈ LongitudeHeight.source) :=
    (LongitudeHeight.coords_smooth hr).comp q (smooth_act r.symm).contMDiffAt
  have a := (hr r₁ p.1 hp.1.1.2).comp p (contMDiffAt_fst (I := 𝓡 2) (J := 𝓡 2))
  have b := (hr r₂ p.2 hp.1.2.2).comp p (contMDiffAt_snd (I := 𝓡 2) (J := 𝓡 2))
  have h : ContDiff ℝ ∞ mix := by change ContDiff ℝ ∞ (fun q : Params => _); dsimp [mix]; fun_prop
  exact h.contMDiff.contMDiffAt.comp p (a.prodMk_space b)

theorem inv_smooth {q : Params} (hq : q ∈ (chart r₁ r₂).target) : ContMDiffAt J productModel ∞ (chart r₁ r₂).symm q := by
  have f : ContDiff ℝ ∞ (fun v : Params => (v.1.1-v.1.2,v.2.1)) := by fun_prop
  have k : ContDiff ℝ ∞ (fun v : Params => (v.1.1+v.1.2,v.2.2)) := by fun_prop
  have a := (smooth_act r₁).contMDiffAt.comp _ ((LongitudeHeight.point_smooth (q := (q.1.1-q.1.2,q.2.1))
    hq.2.1.1.2).comp q f.contMDiff.contMDiffAt)
  have b := (smooth_act r₂).contMDiffAt.comp _ ((LongitudeHeight.point_smooth (q := (q.1.1+q.1.2,q.2.2))
    hq.2.2.1.2).comp q k.contMDiff.contMDiffAt)
  exact a.prodMk b

private def smoothChart : PartialDiffeomorph productModel J Base Params ∞ where
  toPartialEquiv := (chart r₁ r₂).toPartialEquiv
  open_source := (chart r₁ r₂).open_source
  open_target := (chart r₁ r₂).open_target
  contMDiffOn_toFun _ hp := (chart_smooth r₁ r₂ hp).contMDiffWithinAt
  contMDiffOn_invFun _ hq := (inv_smooth r₁ r₂ hq).contMDiffWithinAt

private def constantField (v : Params) (q : Params) : TangentSpace J q := v
def field (v : Params) : Field := mpullback productModel J e (constantField v)

private theorem smooth_const (v q : Params) : ContMDiffAt J J.tangent ∞
    (fun z => TotalSpace.mk' Params z (constantField v z)) q :=
  contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const

theorem field_equiv {p : Base} (hp : p ∈ (chart r₁ r₂).source) :
    ∃ L : Params ≃L[ℝ] Tangent p, ∀ a, L a = field r₁ r₂ a p := by
  have d := (smoothChart r₁ r₂).isLocalDiffeomorphAt productModel J ∞ hp
  obtain ⟨A, hA⟩ := d.isInvertible_mfderiv (by simp)
  refine ⟨A.symm, fun a => ?_⟩
  change A.symm a = (mfderiv productModel J (smoothChart r₁ r₂) p).inverse a
  rw [← hA, ContinuousLinearMap.inverse_equiv]
  rfl

theorem field_smooth {p : Base} (hp : p ∈ (chart r₁ r₂).source) (v : Params) : FieldSmoothAt (field r₁ r₂ v) p := by
  have d := (smoothChart r₁ r₂).isLocalDiffeomorphAt productModel J ∞ hp
  exact (smooth_const v _).mpullback_vectorField_preimage (chart_smooth r₁ r₂ hp)
    (d.isInvertible_mfderiv (by simp)) (by simp)

theorem fields_commute {p : Base} (hp : p ∈ (chart r₁ r₂).source) (v w : Params) :
    mlieBracket productModel (field r₁ r₂ v) (field r₁ r₂ w) p = 0 := by
  have eq : mlieBracket J (constantField v) (constantField w) = 0 := by
    rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
    ext1 z
    change (fderivWithin ℝ (fun _ : Params => w) univ z) v - (fderivWithin ℝ (fun _ : Params => v) univ z) w = 0
    simp
  unfold field
  rw [← mpullback_mlieBracket ((smooth_const v _).mdifferentiableAt (by simp))
    ((smooth_const w _).mdifferentiableAt (by simp)) (chart_smooth r₁ r₂ hp) (by simp), eq, mpullback_apply]
  exact map_zero _


/-- Differentiation in a chart field is ordinary differentiation
of the coordinate expression in the corresponding constant direction. -/
theorem derivative_field {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {p : Base} (hp : p ∈ (chart r₁ r₂).source) (v : Params) (f : Base → W)
    (hd : DifferentiableAt ℝ (f ∘ (chart r₁ r₂).symm) ((chart r₁ r₂) p)) :
    mvfderiv productModel f p (field r₁ r₂ v p) = fderiv ℝ (f ∘ (chart r₁ r₂).symm) ((chart r₁ r₂) p) v := by
  let φ := chart r₁ r₂
  let F := f ∘ φ.symm
  have eq : F ∘ φ =ᶠ[𝓝 p] f := by
    filter_upwards [φ.open_source.mem_nhds hp] with q hq
    simp [F, φ.left_inv hq]
  have d := (smoothChart r₁ r₂).isLocalDiffeomorphAt productModel J ∞ hp
  have hinv := (d.isInvertible_mfderiv (by simp)).self_comp_inverse
  have h := congrArg (fun L : Params →L[ℝ] Params => L v) hinv
  have de : mvfderiv productModel (F ∘ φ) p (field r₁ r₂ v p) = mvfderiv productModel f p (field r₁ r₂ v p) := by
    unfold mvfderiv
    rw [eq.mfderiv_eq]
    rfl
  rw [← de]
  change mfderiv productModel 𝓘(ℝ,W) (F ∘ φ) p _ = _
  rw [mfderiv_comp p hd.mdifferentiableAt ((chart_smooth r₁ r₂ hp).mdifferentiableAt (by simp))]
  change mfderiv J 𝓘(ℝ,W) F (φ p) ((mfderiv productModel J φ p) ((mfderiv productModel J φ p).inverse v)) = _
  rw [show (mfderiv productModel J φ p) ((mfderiv productModel J φ p).inverse v) = v from h, mfderiv_eq_fderiv]
  rfl

/-- A scalar directional derivative in a chart field is the ordinary derivative
of the scalar coefficient in the corresponding constant direction. -/
theorem directional_apply {p : Base} (hp : p ∈ (chart r₁ r₂).source) (v : Params) (f : Base → ℝ)
    (hd : DifferentiableAt ℝ (f ∘ (chart r₁ r₂).symm) ((chart r₁ r₂) p)) :
    directional (field r₁ r₂ v) f p = fderiv ℝ (f ∘ (chart r₁ r₂).symm) ((chart r₁ r₂) p) v :=
  derivative_field r₁ r₂ hp v f hd

/-- Actual Levi-Civita curvature in any two constant directions of the rotated
longitude-height chart, including graph tilts in the height directions. -/
theorem numerator {p : Base} (hp : p ∈ (chart r₁ r₂).source) (g : SmoothMetric) (v w : Params) :
    let U := field r₁ r₂ v
    let V := field r₁ r₂ w
    curvatureNumerator g p (U p) (V p) =
      directional U (fun q => directional V (metricPair g V U) q - directional U (metricPair g V V) q / 2) p -
      directional V (fun q => directional V (metricPair g U U) q / 2) p +
      metricPair g (nabla g U V) (nabla g U V) p - metricPair g (nabla g U U) (nabla g V V) p := by
  have hs (a : Params) : FieldSmoothNear p (field r₁ r₂ a) :=
    Filter.mem_of_superset ((chart r₁ r₂).open_source.mem_nhds hp) (fun _ h => field_smooth r₁ r₂ h a)
  exact curvatureNumerator_commuting g p _ _ (hs v) (hs w)
    (Filter.mem_of_superset ((chart r₁ r₂).open_source.mem_nhds hp) (fun _ h => fields_commute r₁ r₂ h v w))



/-- The centered chart for a flat plane uses the ordered axes p, n × p and n. -/
def axes (n p : FlatLocus.UnitVector) : Fin 3 → E3 :=
  ![WithLp.toLp 2 p.val, WithLp.toLp 2 (n.val ⨯₃ p.val), WithLp.toLp 2 n.val]

private theorem orthonormal_axes (n p : FlatLocus.UnitVector) (hp : n.val ⬝ᵥ p.val = 0) :
    Orthonormal ℝ (axes n p) := by
  have a := cross_unit n.val p.val n.property p.property hp
  have b : n.val ⬝ᵥ (n.val ⨯₃ p.val) = 0 := dot_self_cross _ _
  have pn := (dotProduct_comm p.val n.val).trans hp
  have cp := (dotProduct_comm p.val _).trans a.2
  have cn := (dotProduct_comm _ n.val).trans b
  rw [orthonormal_iff_ite]
  intro i j
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  fin_cases i <;> fin_cases j <;>
    simp [axes, a.1, a.2, b, pn, cp, cn, hp] <;> first | exact n.property | exact p.property

def axesBasis (n p : FlatLocus.UnitVector) (hp : n.val ⬝ᵥ p.val = 0) : OrthonormalBasis (Fin 3) ℝ E3 :=
  let h := orthonormal_axes n p hp
  OrthonormalBasis.mk h (h.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [E3])).ge

theorem axesBasis_apply (n p : FlatLocus.UnitVector) (hp : n.val ⬝ᵥ p.val = 0) (i : Fin 3) :
    (axesBasis n p hp).repr.symm (EuclideanSpace.single i 1) = axes n p i := by
  rw [OrthonormalBasis.repr_symm_single]
  exact congrFun (OrthonormalBasis.coe_mk (orthonormal_axes n p hp) _) i

private theorem point_origin : (LongitudeHeight.point (0,0)).val = EuclideanSpace.single 0 1 := by
  ext i
  change (![Real.cos (Real.arcsin 0)*Real.cos 0,Real.cos (Real.arcsin 0)*Real.sin 0,Real.sin (Real.arcsin 0)] : R3) i = _
  fin_cases i <;> simp [EuclideanSpace.single]

theorem center (v : FlatLocus.Representative) :
    let n := v.val.1
    let p := v.val.2.1
    let q := v.val.2.2
    let r := (axesBasis n p v.property.1).repr.symm
    let s := (axesBasis n q v.property.2).repr.symm
    (0 : Params) ∈ (chart r s).target ∧ (chart r s).symm 0 = (unitSphere p,unitSphere q) := by
  dsimp only
  constructor
  · change _ ∈ (Set.univ : Set Params) ∧
      ((|((0:ℝ)-0)| < Real.pi/2 ∧ |(0:ℝ)| < 1) ∧ _) ∧
      ((|((0:ℝ)+0)| < Real.pi/2 ∧ |(0:ℝ)| < 1) ∧ _)
    simp [Real.pi_pos]
  · rw [chart_inv_apply]
    change (sphereAction _ (LongitudeHeight.point ((0:ℝ)-0,0)),sphereAction _ (LongitudeHeight.point ((0:ℝ)+0,0))) = _
    simp only [sub_zero, add_zero]
    apply Prod.ext <;> apply Subtype.ext
    all_goals change (axesBasis _ _ _).repr.symm (LongitudeHeight.point (0,0)).val = _
    all_goals rw [point_origin,axesBasis_apply]; rfl



private def splitParams : Params →L[ℝ] Params where
  toFun q := ((q.1.1-q.1.2,q.2.1),(q.1.1+q.1.2,q.2.2))
  map_add' a b := by ext <;> simp <;> ring
  map_smul' k a := by ext <;> simp <;> ring
  cont := by fun_prop

private def rawRotation (r : E3 ≃ₗᵢ[ℝ] E3) : R3 →L[ℝ] R3 :=
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  (L.symm.trans (r.toContinuousLinearEquiv.trans L)).toContinuousLinearMap

/-- The four-coordinate velocity used when evaluating the metric tensors in
the verifier. Angles change by x-y and x+y and the two heights vary independently. -/
theorem chart_velocity {q : Params} (hq : q ∈ (chart r₁ r₂).target) (v : Params) :
    let A := q.1.1-q.1.2
    let B := q.1.1+q.1.2
    fderiv ℝ (ambientPoint ∘ (chart r₁ r₂).symm) q v =
      ((r₁ (WithLp.toLp 2 ((v.1.1-v.1.2) • LongitudeHeight.lonVector A q.2.1 + v.2.1 • LongitudeHeight.heightVector A q.2.1))).ofLp,
       (r₂ (WithLp.toLp 2 ((v.1.1+v.1.2) • LongitudeHeight.lonVector B q.2.2 + v.2.2 • LongitudeHeight.heightVector B q.2.2))).ofLp) := by
  let f (x : ℝ × ℝ) := (LongitudeHeight.point x).val.ofLp
  let h₁ := (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)).comp splitParams
  let h₂ := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)).comp splitParams
  have z₁ : |q.2.1| < 1 := hq.2.1.1.2
  have z₂ : |q.2.2| < 1 := hq.2.2.1.2
  have df (h : Params →L[ℝ] ℝ × ℝ) (r : E3 ≃ₗᵢ[ℝ] E3) (hz : |(h q).2| < 1) :
      HasFDerivAt (fun x => rawRotation r (f (h x)))
        ((rawRotation r).comp ((fderiv ℝ f (h q)).comp h)) q :=
    (rawRotation r).hasFDerivAt.comp q ((LongitudeHeight.raw_differentiable hz).hasFDerivAt.comp q h.hasFDerivAt)
  have gh := (df h₁ r₁ z₁).prodMk (df h₂ r₂ z₂)
  have eq : (ambientPoint ∘ (chart r₁ r₂).symm) = (fun x => (rawRotation r₁ (f (h₁ x)),rawRotation r₂ (f (h₂ x)))) := rfl
  rw [eq,gh.fderiv]
  dsimp only
  change (rawRotation r₁ ((fderiv ℝ f (h₁ q)) (h₁ v)),rawRotation r₂ ((fderiv ℝ f (h₂ q)) (h₂ v))) = _
  have eval (y w : ℝ × ℝ) (hz : |y.2| < 1) : (fderiv ℝ f y) w =
      w.1 • LongitudeHeight.lonVector y.1 y.2 + w.2 • LongitudeHeight.heightVector y.1 y.2 :=
    LongitudeHeight.point_fderiv y.1 y.2 hz w
  rw [eval (h₁ q) (h₁ v) z₁,eval (h₂ q) (h₂ v) z₂]
  rfl



private def basePair (v : FlatLocus.Representative) : Base :=
  (unitSphere v.val.2.1, unitSphere v.val.2.2)

private theorem continuous_basePair : Continuous basePair :=
  (unitSphere.continuous.comp (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))).prodMk
    (unitSphere.continuous.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))

def adaptedChart (v : FlatLocus.Representative) : OpenPartialHomeomorph Base Params :=
  chart (axesBasis v.val.1 v.val.2.1 v.property.1).repr.symm
    (axesBasis v.val.1 v.val.2.2 v.property.2).repr.symm

/-- On this set the mixed plane projects invertibly onto the two longitude
directions. The inequality is invariant under either choice of normal sign. -/
def framePatch (c : FlatLocus.Representative) : Set FlatLocus.Representative :=
  basePair ⁻¹' (adaptedChart c).source ∩ {v | v.val.1.val ⬝ᵥ c.val.1.val ≠ 0}

theorem framePatch_open (c : FlatLocus.Representative) : IsOpen (framePatch c) := by
  apply IsOpen.inter ((adaptedChart c).open_source.preimage continuous_basePair)
  apply isOpen_ne.preimage
  exact (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).dotProduct continuous_const

theorem finite_frame_patches : ∃ S : Finset FlatLocus.Representative,
    ∀ v : FlatLocus.Representative, ∃ c ∈ S, v ∈ framePatch c := by
  classical
  have self (v : FlatLocus.Representative) : v ∈ framePatch v := by
    have h := center v
    refine ⟨?_, ?_⟩
    · change (unitSphere _,unitSphere _) ∈ (adaptedChart v).source
      rw [← h.2]
      exact (adaptedChart v).map_target h.1
    · exact ne_zero_of_eq_one v.val.1.property
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover framePatch framePatch_open
    (fun v _ => mem_iUnion.mpr ⟨v, self v⟩)
  refine ⟨S,fun v => ?_⟩
  obtain ⟨c,hc⟩ := mem_iUnion.mp (hS (mem_univ v))
  obtain ⟨h,hv⟩ := mem_iUnion.mp hc
  exact ⟨c,h,hv⟩

/-- The two diagonal entries pairing a mixed-plane basis with the separate
longitude vectors about the chart axis both equal the normal dot product.
Their determinant stays nonzero on its entire patch, also at singular pairs. -/
theorem longitude_determinant {c v : FlatLocus.Representative} (hv : v ∈ framePatch c) :
    let n := v.val.1.val
    let m := c.val.1.val
    let p := v.val.2.1.val
    let q := v.val.2.2.val
    ((n ⨯₃ p) ⬝ᵥ (m ⨯₃ p)) * ((n ⨯₃ q) ⬝ᵥ (m ⨯₃ q)) = (n ⬝ᵥ m)^2 ∧ 0 < (n ⬝ᵥ m)^2 := by
  dsimp only
  have unit (x : FlatLocus.UnitVector) : x.val ⬝ᵥ x.val = 1 := x.property
  simp only [cross_dot_cross,unit,v.property.1,v.property.2,mul_one,zero_mul,sub_zero,← sq]
  exact ⟨trivial,sq_pos_of_ne_zero hv.2⟩


end
end LocalHopf.SphereProduct.JetChart
