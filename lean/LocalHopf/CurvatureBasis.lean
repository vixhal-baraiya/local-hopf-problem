import LocalHopf.MetricCurvatureExpansion

/-! Change of spanning vectors for the intrinsic Levi-Civita curvature numerator. -/
namespace LocalHopf.SphereProduct
open Bundle FiberBundle Filter Set VectorField
open scoped Manifold Topology ContDiff
noncomputable section

private abbrev extF {p : Base} (X : Tangent p) : Field := extend Coordinates X

private theorem scalar_commute {p : Base} (x y z : Tangent p) (nz : z ≠ 0) {f : Base → ℝ}
    (hf : ∀ᶠ q in 𝓝 p, ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ f q) :
    directional (extF x) (directional (extF y) f) p = directional (extF y) (directional (extF x) f) p := by
  let X := extF x
  let Y := extF y
  let Z := extF z
  have sx := (extend_smooth_near x).self_of_nhds
  have sy := (extend_smooth_near y).self_of_nhds
  have sz := (extend_smooth_near z).self_of_nhds
  have eq (u : Tangent p) : mlieBracket productModel (extF u) (f • Z) =ᶠ[𝓝 p] directional (extF u) f • Z := by
    filter_upwards [hf,extend_smooth_near z,extend_commute u z] with q fq zq h
    rw [mlieBracket_smul_right (fq.mdifferentiableAt (by simp)) (zq.mdifferentiableAt (by simp))]
    change _ + _ • mlieBracket productModel (extF u) (extF z) q = _
    rw [h,smul_zero,add_zero]; rfl
  have twice (u v : Tangent p) :
      mlieBracket productModel (extF u) (mlieBracket productModel (extF v) (f • Z)) p =
      directional (extF u) (directional (extF v) f) p • z := by
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (Filter.EventuallyEq.rfl : extF u =ᶠ[𝓝 p] extF u) (eq v),
      mlieBracket_smul_right ((directional_smoothAt (extend_smooth_near v).self_of_nhds hf.self_of_nhds).mdifferentiableAt (by simp))
        (sz.mdifferentiableAt (by simp))]
    change _ • extend Coordinates z p + _ • mlieBracket productModel (extF u) (extF z) p = _
    rw [(extend_commute u z).self_of_nhds,extend_apply_self,smul_zero,add_zero]; rfl
  have h := leibniz_identity_mlieBracket_apply (I := productModel) (U := X) (V := Y) (W := f • Z)
    (sx.of_le (by simp)) (sy.of_le (by simp)) ((hf.self_of_nhds.smul_section sz).of_le (by simp))
  have zero : mlieBracket productModel (mlieBracket productModel X Y) (f • Z) p = 0 := by
    have ex : mlieBracket productModel X Y =ᶠ[𝓝 p] (0:Field) := extend_commute x y
    rw [ex.mlieBracket_vectorField_eq (Filter.EventuallyEq.rfl (f := f • Z)),mlieBracket_zero_left]; rfl
  rw [zero,zero_add,twice x y,twice y x] at h
  exact smul_left_injective ℝ nz h

private theorem pair_diff (g : SmoothMetric) (A B C : Field) {p : Base} (b : FieldSmoothAt B p) (c : FieldSmoothAt C p) :
    directional A (metricPair g B C) p = metricPair g (nabla g A B) C p + metricPair g B (nabla g A C) p := by
  let : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.isMetricCompatible_leviCivitaConnection productModel (M := Base)
    ).mvfderiv_inner_eq A (b.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp))

private theorem scalar_skew (g : SmoothMetric) (p : Base) (x y z : Tangent p) :
    g.inner p (fieldR g (extF x) (extF y) (extF z) p) z = 0 := by
  by_cases hz : z=0
  · rw [hz]; exact map_zero _
  let Z := extF z
  let f := metricPair g Z Z
  let : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  have zsm := extend_smooth_near z
  have fs : ∀ᶠ q in 𝓝 p, ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ f q := by
    filter_upwards [zsm] with q h using h.inner_bundle h
  have comm := scalar_commute x y z hz fs
  have second (u v : Tangent p) : directional (extF u) (directional (extF v) f) p =
      2*(metricPair g (nabla g (extF u) (nabla g (extF v) Z)) Z p +
        metricPair g (nabla g (extF v) Z) (nabla g (extF u) Z) p) := by
    let V := extF v
    let N := nabla g V Z
    have before : directional V f =ᶠ[𝓝 p] (2:ℝ) • metricPair g N Z := by
      filter_upwards [zsm] with q h
      rw [show directional V f q = _ from pair_diff g V Z Z h h]
      change _ + g.inner q (Z q) (N q) = _
      rw [g.symm q (Z q) (N q)]
      change metricPair g N Z q + metricPair g N Z q = 2*metricPair g N Z q
      ring
    have ns := nabla_smoothAt g (extend_smooth_near v) zsm
    have d : ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ (metricPair g N Z) p := ns.inner_bundle zsm.self_of_nhds
    rw [directional_congr (U := extF u) before,directional_mul_const _ _ (d.mdifferentiableAt (by simp)),
      pair_diff g _ N Z ns zsm.self_of_nhds]
  rw [second x y,second y x] at comm
  have zz : Z p = z := extend_apply_self ..
  have sym (A B : Field) : metricPair g A B p = metricPair g B A p := g.symm p _ _
  rw [sym (nabla g (extF y) Z) (nabla g (extF x) Z)] at comm
  change g.inner p (nabla g (extF x) (nabla g (extF y) Z) p - nabla g (extF y) (nabla g (extF x) Z) p -
      nabla g (mlieBracket productModel (extF x) (extF y)) Z p) z = 0
  have zero : nabla g (mlieBracket productModel (extF x) (extF y)) Z p = 0 := by
    unfold nabla; rw [(extend_commute x y).self_of_nhds]; exact map_zero _
  rw [zero,sub_zero,map_sub,sub_apply,← zz]
  change metricPair g _ Z p - metricPair g _ Z p = 0
  linarith only [comm]

private abbrev operatorR (g : SmoothMetric) {p : Base} (x y z : Tangent p) := fieldR g (extF x) (extF y) (extF z) p

private theorem in_first (g : SmoothMetric) {p : Base} (a b : ℝ) (x y u z : Tangent p) :
    operatorR g (a • x+b • y) u z = a • operatorR g x u z + b • operatorR g y u z := by
  let P := fun X : Field => fieldR g X (extF u) (extF z) p
  let L := TensorialAt.mkHom P p (fieldR_tensorial g p (extF u) (extend_smooth_near z))
  change L (a • x+b • y) = a • L x + b • L y
  rw [map_add,map_smul,map_smul]

private theorem in_second (g : SmoothMetric) {p : Base} (a b : ℝ) (x y u z : Tangent p) :
    operatorR g u (a • x+b • y) z = a • operatorR g u x z + b • operatorR g u y z := by
  have swap (x y : Tangent p) : operatorR g x y z = -operatorR g y x z := fieldR_swap g ..
  rw [swap,in_first,swap x u,swap y u]
  module

private theorem in_third (g : SmoothMetric) {p : Base} (a b : ℝ) (x y u v : Tangent p) :
    operatorR g u v (a • x+b • y) = a • operatorR g u v x + b • operatorR g u v y := by
  have bianchi (z : Tangent p) : operatorR g u v z = operatorR g u z v - operatorR g v z u := by
    have h := fieldR_bianchi g (extF u) (extF v) (extF z) p (extend_smooth_near u) (extend_smooth_near v) (extend_smooth_near z)
    unfold operatorR
    linear_combination (norm := abel) h
  rw [bianchi,in_second,in_second,bianchi x,bianchi y]
  module

private theorem skew_last (g : SmoothMetric) {p : Base} (x y u v : Tangent p) :
    g.inner p (operatorR g x y u) v = -g.inner p (operatorR g x y v) u := by
  have e := scalar_skew g p x y (u+v)
  have eq := in_third g (1:ℝ) 1 u v x y
  simp only [one_smul] at eq
  change g.inner p (operatorR g x y (u+v)) (u+v) = 0 at e
  simp only [eq,map_add,add_apply,scalar_skew g p x y u,scalar_skew g p x y v] at e
  linarith

private theorem plane_operator (g : SmoothMetric) {p : Base} (a b c d : ℝ) (x y z : Tangent p) :
    operatorR g (a • x+b • y) (c • x+d • y) z = (a*d-b*c) • operatorR g x y z := by
  have diag (w : Tangent p) : operatorR g w w z = 0 := by
    simp only [operatorR,fieldR,sub_self,mlieBracket_self]
    unfold nabla
    simp
  have swap : operatorR g y x z = -operatorR g x y z := fieldR_swap g ..
  rw [in_first,in_second,in_second,diag,diag,swap]
  module

/-- The sectional curvature numerator changes by the square of the determinant
under any change of spanning vectors at the same point. -/
theorem curvatureNumerator_basis_change (g : SmoothMetric) (p : Base) (x y : Tangent p) (a b c d : ℝ) :
    curvatureNumerator g p (a • x+b • y) (c • x+d • y) = (a*d-b*c)^2 * curvatureNumerator g p x y := by
  have numerator (u v : Tangent p) : curvatureNumerator g p u v = g.inner p (operatorR g u v v) u := by
    simpa only [extend_apply_self] using curvatureNumerator_fields g p (extF u) (extF v)
      (extend_smooth_near u) (extend_smooth_near v)
  rw [numerator,numerator,plane_operator,in_third]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul,scalar_skew g p x y x,scalar_skew g p x y y,
    skew_last g x y x y]
  ring


/-- Three evaluations determine a quadratic on an affine line. The samples are taken at 0, 1 and −1. -/
def quadraticSamples (h x p m : ℝ) := x + h*(p-m)/2 + h^2*((p+m)/2-x)

/-- Polarization in either spanning vector, holding the other one fixed. -/
theorem curvatureNumerator_interpolate (g : SmoothMetric) (p : Base) (x u y : Tangent p) (h : ℝ) :
    curvatureNumerator g p (x+h • u) y =
      quadraticSamples h (curvatureNumerator g p x y) (curvatureNumerator g p (x+u) y) (curvatureNumerator g p (x-u) y) ∧
    curvatureNumerator g p y (x+h • u) =
      quadraticSamples h (curvatureNumerator g p y x) (curvatureNumerator g p y (x+u)) (curvatureNumerator g p y (x-u)) := by
  have val (a b : Tangent p) : curvatureNumerator g p a b = g.inner p (operatorR g a b b) a := by
    simpa only [extend_apply_self] using curvatureNumerator_fields g p (extF a) (extF b) (extend_smooth_near a) (extend_smooth_near b)
  have exp (c : ℝ) : curvatureNumerator g p (x+c • u) y =
      curvatureNumerator g p x y + c*(g.inner p (operatorR g x y y) u + g.inner p (operatorR g u y y) x) + c^2*curvatureNumerator g p u y := by
    have lin := in_first g 1 c x u y y
    simp only [one_smul] at lin
    simp only [val,lin,map_add,map_smul,add_apply,smul_apply,smul_eq_mul]; ring
  have plus : x+u = x+(1:ℝ) • u := by simp
  have minus : x-u = x+(-1:ℝ) • u := by simp [sub_eq_add_neg]
  have fst : curvatureNumerator g p (x+h • u) y =
      quadraticSamples h (curvatureNumerator g p x y) (curvatureNumerator g p (x+u) y) (curvatureNumerator g p (x-u) y) := by
    rw [plus,minus,exp h,exp 1,exp (-1),quadraticSamples]; ring
  have swap (a b : Tangent p) : curvatureNumerator g p b a = curvatureNumerator g p a b := by
    simpa using curvatureNumerator_basis_change g p a b 0 1 1 0
  exact ⟨fst,by simpa only [show ∀ a, curvatureNumerator g p y a = curvatureNumerator g p a y from fun a => swap a y] using fst⟩

end
end LocalHopf.SphereProduct
