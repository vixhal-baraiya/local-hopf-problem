import LocalHopf.Curvature

/-! Independence of the curvature numerator from the fields extending a tangent frame.
This permits use of the longitude-height chart in the intrinsic curvature formula. -/
namespace LocalHopf.SphereProduct
open Bundle FiberBundle Filter VectorField Set
open scoped Manifold Topology ContDiff
noncomputable section

abbrev FieldSmoothNear (p : Base) (U : Field) := ∀ᶠ q in 𝓝 p, FieldSmoothAt U q

private def connection (g : SmoothMetric) : CovariantDerivative productModel Coordinates Tangent :=
  letI : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  CovariantDerivative.leviCivitaConnection productModel Base

private theorem nabla_add_left (g : SmoothMetric) (X Y W : Field) :
    nabla g (X+Y) W = nabla g X W + nabla g Y W :=
  funext fun q => (connection g W q).map_add _ _

private theorem nabla_smul_left (g : SmoothMetric) (f : Base → ℝ) (X W : Field) :
    nabla g (f • X) W = f • nabla g X W := funext fun q => (connection g W q).map_smul _ _

private theorem nabla_add_right (g : SmoothMetric) (X : Field) {Y W : Field} {p : Base}
    (hY : FieldDiffAt Y p) (hW : FieldDiffAt W p) :
    nabla g X (Y+W) p = nabla g X Y p + nabla g X W p :=
  congrArg (fun L : Tangent p →L[ℝ] Tangent p => L (X p))
    ((connection g).isCovariantDerivativeOn.add hY hW (mem_univ p))

private theorem nabla_leibniz (g : SmoothMetric) (X : Field) {Y : Field} {f : Base → ℝ} {p : Base}
    (hY : FieldDiffAt Y p) (hf : MDifferentiableAt productModel 𝓘(ℝ,ℝ) f p) :
    nabla g X (f • Y) p = directional X f p • Y p + f p • nabla g X Y p := by
  rw [add_comm]
  exact congrArg (fun L : Tangent p →L[ℝ] Tangent p => L (X p))
    ((connection g).isCovariantDerivativeOn.leibniz hY hf (mem_univ p))

private theorem nabla_diff_left (g : SmoothMetric) {p : Base} {X W : Field}
    (hX : FieldDiffAt X p) (hW : FieldSmoothNear p W) : FieldDiffAt (nabla g X W) p := by
  classical
  let t := trivializationAt Coordinates (TangentSpace productModel : Base → Type) p
  let b := Module.Basis.ofVectorSpace ℝ Coordinates
  let s := t.localFrame b
  let c := t.localFrameCoeff productModel b
  have hp : p ∈ t.baseSet := mem_baseSet_trivializationAt' p
  have h (i) : FieldDiffAt (nabla g (s i) W) p := by
    apply (nabla_smoothAt g _ hW).mdifferentiableAt (by simp)
    filter_upwards [t.open_baseSet.mem_nhds hp] with q hq
    exact contMDiffAt_localFrame_of_mem ∞ _ b i hq
  have hc (i) := mdifferentiableAt_localFrameCoeff b hp hX i
  have d : FieldDiffAt (fun q => ∑ i, c i q (X q) • nabla g (s i) W q) p :=
    .sum_section fun i _ => (hc i).smul_section (h i)
  apply d.congr_of_eventuallyEq
  filter_upwards [t.eventually_eq_localFrame_sum_coeff_smul (s := X) (I := productModel) b hp] with q hq
  apply congrArg (TotalSpace.mk' Coordinates q)
  change (connection g W q) (X q) = _
  nth_rw 1 [hq]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (connection g W q).map_smul _ _

/-- Curvature applied to vector fields before specializing the values of the fields at p. -/
def fieldR (g : SmoothMetric) (X Y W : Field) (p : Base) : Tangent p :=
  nabla g X (nabla g Y W) p - nabla g Y (nabla g X W) p -
  nabla g (mlieBracket productModel X Y) W p

theorem fieldR_tensorial (g : SmoothMetric) (p : Base) (Y : Field) {W : Field}
    (hW : FieldSmoothNear p W) : TensorialAt productModel Coordinates (fun X => fieldR g X Y W p) p where
  add hX hZ := by
    unfold fieldR
    rw [nabla_add_left, nabla_add_left, nabla_add_right g Y (nabla_diff_left g hX hW) (nabla_diff_left g hZ hW)]
    change _ - _ - (connection g W p) (mlieBracket productModel _ Y p) = _
    rw [mlieBracket_add_left hX hZ, map_add]
    simp only [Pi.add_apply, nabla, connection]
    abel
  smul hf hX := by
    unfold fieldR
    rw [nabla_smul_left, nabla_smul_left, nabla_leibniz g Y (nabla_diff_left g hX hW) hf]
    change _ - _ - (connection g W p) (mlieBracket productModel _ Y p) = _
    rw [mlieBracket_smul_left hf hX, map_add, map_smul, map_smul]
    simp only [Pi.smul_apply', directional, smul_sub, neg_smul, nabla, connection]
    abel

theorem fieldR_swap (g : SmoothMetric) (X Y W : Field) (p : Base) :
    fieldR g Y X W p = -fieldR g X Y W p := by
  unfold fieldR
  change _ - _ - (connection g W p) (mlieBracket productModel Y X p) = _
  rw [mlieBracket_swap (V := Y) (W := X)]
  simp only [Pi.neg_apply, map_neg]
  abel

private theorem torsion_identity (g : SmoothMetric) {p : Base} {X Y : Field}
    (hX : FieldDiffAt X p) (hY : FieldDiffAt Y p) :
    nabla g X Y p - nabla g Y X p = mlieBracket productModel X Y p := by
  let : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero productModel (M := Base)) hX hY

private theorem cyclic_term (g : SmoothMetric) (X Y Z : Field) (p : Base)
    (hX : FieldSmoothNear p X) (hY : FieldSmoothNear p Y) (hZ : FieldSmoothNear p Z) :
    nabla g X (nabla g Y Z) p - nabla g X (nabla g Z Y) p - nabla g (mlieBracket productModel Y Z) X p =
      mlieBracket productModel X (mlieBracket productModel Y Z) p := by
  have bs : FieldSmoothAt (mlieBracket productModel Y Z) p :=
    hY.self_of_nhds.mlieBracket_vectorField hZ.self_of_nhds (by simp)
  have b := bs.mdifferentiableAt (by simp)
  have n := (nabla_smoothAt g hZ hY).mdifferentiableAt (by simp)
  have eq : ∀ᶠ q in 𝓝 p, nabla g Y Z q = (mlieBracket productModel Y Z + nabla g Z Y) q := by
    filter_upwards [hY,hZ] with q hy hz
    exact sub_eq_iff_eq_add.mp (torsion_identity g (hy.mdifferentiableAt (by simp)) (hz.mdifferentiableAt (by simp)))
  have h := (connection g).isCovariantDerivativeOn.congr_of_eventuallyEq
    ((nabla_smoothAt g hY hZ).mdifferentiableAt (by simp)) ((bs.add_section (nabla_smoothAt g hZ hY)).mdifferentiableAt (by simp)) univ_mem eq
  have he := congrArg (fun L : Tangent p →L[ℝ] Tangent p => L (X p)) h
  change nabla g X (nabla g Y Z) p = nabla g X (mlieBracket productModel Y Z + nabla g Z Y) p at he
  rw [he,nabla_add_right g X b n,add_sub_cancel_right]
  exact torsion_identity g (hX.self_of_nhds.mdifferentiableAt (by simp)) b

theorem fieldR_bianchi (g : SmoothMetric) (X Y Z : Field) (p : Base)
    (hX : FieldSmoothNear p X) (hY : FieldSmoothNear p Y) (hZ : FieldSmoothNear p Z) :
    fieldR g X Y Z p - fieldR g X Z Y p + fieldR g Y Z X p = 0 := by
  have h := leibniz_identity_mlieBracket_apply (I := productModel)
    (hX.self_of_nhds.of_le (by simp)) (hY.self_of_nhds.of_le (by simp)) (hZ.self_of_nhds.of_le (by simp))
  have hs : mlieBracket productModel (mlieBracket productModel X Y) Z p =
    -mlieBracket productModel Z (mlieBracket productModel X Y) p :=
    congrFun (mlieBracket_swap (I := productModel) (V := mlieBracket productModel X Y) (W := Z)) p
  rw [hs, ← cyclic_term g X Y Z p hX hY hZ, ← cyclic_term g Z X Y p hZ hX hY,
    ← cyclic_term g Y X Z p hY hX hZ] at h
  unfold fieldR
  linear_combination (norm := abel) h

/-- With smooth extensions in a neighborhood, all three vector arguments of
the curvature operator depend only on their values at the base point. -/
theorem fieldR_congr (g : SmoothMetric) {p : Base} {X Y Z X' Y' Z' : Field}
    (hX : FieldSmoothNear p X) (hY : FieldSmoothNear p Y) (hZ : FieldSmoothNear p Z)
    (hX' : FieldSmoothNear p X') (hY' : FieldSmoothNear p Y') (hZ' : FieldSmoothNear p Z')
    (ex : X p = X' p) (ey : Y p = Y' p) (ez : Z p = Z' p) :
    fieldR g X Y Z p = fieldR g X' Y' Z' p := by
  have first {A B T S : Field} (a : FieldSmoothNear p A) (b : FieldSmoothNear p B)
      (s : FieldSmoothNear p S) (e : A p = B p) : fieldR g A T S p = fieldR g B T S p :=
    (fieldR_tensorial g p T s).pointwise (a.self_of_nhds.mdifferentiableAt (by simp))
      (b.self_of_nhds.mdifferentiableAt (by simp)) e
  have second {A B T S : Field} (a : FieldSmoothNear p A) (b : FieldSmoothNear p B)
      (s : FieldSmoothNear p S) (e : A p = B p) : fieldR g T A S p = fieldR g T B S p := by
    exact (fieldR_swap g A T S p).trans ((congrArg Neg.neg (first (T := T) a b s e)).trans (fieldR_swap g B T S p).symm)
  rw [first hX hX' hZ ex, second hY hY' hZ ey]
  have a := fieldR_bianchi g X' Y' Z p hX' hY' hZ
  have b := fieldR_bianchi g X' Y' Z' p hX' hY' hZ'
  rw [second hZ hZ' hY' ez, second hZ hZ' hX' ez] at a
  exact sub_left_inj.mp (add_right_cancel (a.trans b.symm))

/-- Evaluation of the true numerator using any smooth local extensions. -/
theorem curvatureNumerator_fields (g : SmoothMetric) (p : Base) (U V : Field)
    (hU : FieldSmoothNear p U) (hV : FieldSmoothNear p V) :
    curvatureNumerator g p (U p) (V p) = g.inner p (fieldR g U V V p) (U p) := by
  let A := extend (E := Tangent) Coordinates (U p)
  let B := extend (E := Tangent) Coordinates (V p)
  have ha : A p = U p := extend_apply_self ..
  have hb : B p = V p := extend_apply_self ..
  have e := fieldR_congr g (extend_smooth_near _) (extend_smooth_near _) (extend_smooth_near _)
    hU hV hV ha hb hb
  rw [← e]
  change g.inner p ((connection g (nabla g B B) p) (U p) - (connection g (nabla g A B) p) (V p) -
    nabla g (mlieBracket productModel A B) B p) (U p) =
    g.inner p ((connection g (nabla g B B) p) (A p) - (connection g (nabla g A B) p) (B p) -
    nabla g (mlieBracket productModel A B) B p) (U p)
  rw [ha,hb]

theorem directional_congr {U : Field} {f k : Base → ℝ} {p : Base}
    (h : f =ᶠ[𝓝 p] k) : directional U f p = directional U k p := by
  unfold directional mvfderiv
  rw [h.mfderiv_eq]
  rfl

/-- The Levi-Civita numerator in any smooth commuting pair of local fields. -/
theorem curvatureNumerator_commuting (g : SmoothMetric) (p : Base) (U V : Field)
    (hU : ∀ᶠ q in 𝓝 p, FieldSmoothAt U q) (hV : ∀ᶠ q in 𝓝 p, FieldSmoothAt V q)
    (hbr : ∀ᶠ q in 𝓝 p, mlieBracket productModel U V q = 0) :
    curvatureNumerator g p (U p) (V p) =
      directional U (fun q => directional V (metricPair g V U) q - directional U (metricPair g V V) q / 2) p -
      directional V (fun q => directional V (metricPair g U U) q / 2) p +
      metricPair g (nabla g U V) (nabla g U V) p - metricPair g (nabla g U U) (nabla g V V) p := by
  let : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
  have symm (A B : Field) : metricPair g A B = metricPair g B A := funext fun q => g.symm q _ _
  have vv : firstKind g V V U =ᶠ[𝓝 p] fun q => directional V (metricPair g V U) q -
      directional U (metricPair g V V) q / 2 := by
    filter_upwards [hU,hV,hbr] with q u v b
    rw [firstKind_koszul g V V U q (v.mdifferentiableAt (by simp)) (v.mdifferentiableAt (by simp))
      (u.mdifferentiableAt (by simp)),symm U V]
    have c : mlieBracket productModel V U q = 0 := by rw [mlieBracket_swap_apply, b, neg_zero]
    simp [metricPair,b,c]
    ring
  have uv : firstKind g U V U =ᶠ[𝓝 p] fun q => directional V (metricPair g U U) q / 2 := by
    filter_upwards [hU,hV,hbr] with q u v b
    rw [firstKind_koszul g U V U q (u.mdifferentiableAt (by simp)) (v.mdifferentiableAt (by simp))
      (u.mdifferentiableAt (by simp)),symm V U]
    have c : mlieBracket productModel V U q = 0 := by rw [mlieBracket_swap_apply, b, neg_zero]
    simp [metricPair,b,c]
  have diff (A B C : Field) (b : FieldDiffAt B p) (c : FieldDiffAt C p) :
      directional A (metricPair g B C) p =
        metricPair g (nabla g A B) C p + metricPair g B (nabla g A C) p :=
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection productModel (M := Base)).mvfderiv_inner_eq A b c
  have u := hU.self_of_nhds.mdifferentiableAt (by simp)
  have v := hV.self_of_nhds.mdifferentiableAt (by simp)
  have equal := sub_eq_zero.mp ((torsion_identity g u v).trans hbr.self_of_nhds)
  rw [curvatureNumerator_fields g p U V hU hV, ← directional_congr vv, ← directional_congr uv]
  unfold firstKind
  rw [diff U _ _ ((nabla_smoothAt g hV hV).mdifferentiableAt (by simp)) u,
      diff V _ _ ((nabla_smoothAt g hU hV).mdifferentiableAt (by simp)) u, symm (nabla g U U)]
  simp only [fieldR,metricPair,map_sub, sub_apply]
  change _ - _ - (g.inner p ((connection g V p) (mlieBracket productModel U V p))) (U p) = _
  rw [hbr.self_of_nhds, map_zero, map_zero, zero_apply, sub_zero, ← equal]
  ring

end
end LocalHopf.SphereProduct
