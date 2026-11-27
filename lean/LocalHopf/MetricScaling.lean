import LocalHopf.MetricCurvatureExpansion

/-! # Constant rescaling of the intrinsic curvature numerator -/
namespace LocalHopf.SphereProduct
open Bundle FiberBundle Filter
open scoped Manifold Topology
noncomputable section

private theorem extend_smul_near {p : Base} (c : ℝ) (v : Tangent p) :
    extend (E := Tangent) Coordinates (c • v) =ᶠ[𝓝 p] c • extend Coordinates v := by
  let e := trivializationAt Coordinates Tangent p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt' p
  filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
  change e.symm q (e ⟨p,c • v⟩).2 = c • e.symm q (e ⟨p,v⟩).2
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hp, ← e.continuousLinearMapAt_apply_of_mem ℝ hp,
    ← e.symmL_apply (R := ℝ) hq, ← e.symmL_apply (R := ℝ) hq, map_smul, map_smul]

private theorem directional_weight (U : Field) (c : ℝ) (f : Base → ℝ) (p : Base) :
    directional U (fun q => c * f q) p = c * directional U f p := by
  by_cases hf : MDifferentiableAt productModel 𝓘(ℝ,ℝ) f p
  · exact directional_mul_const U c hf
  by_cases hc : c = 0
  · subst c; simp [directional,mvfderiv_const]
  have hn : ¬ MDifferentiableAt productModel 𝓘(ℝ,ℝ) (fun q => c * f q) p := by
    intro h
    apply hf
    simpa only [Pi.mul_def,← mul_assoc,inv_mul_cancel₀ hc,one_mul] using
      ((mdifferentiableAt_const (c := c⁻¹)).mul h)
  simp [directional,mvfderiv,mfderiv_zero_of_not_mdifferentiableAt hf,
    mfderiv_zero_of_not_mdifferentiableAt hn]

variable {g g' : SmoothMetric} {k : ℝ}
private abbrev Scales (g g' : SmoothMetric) (k : ℝ) :=
  ∀ p X Y, g'.inner p X Y = k * g.inner p X Y

private theorem pair_scaled (h : Scales g g' k) (c d : ℝ) (U V : Field) :
    metricPair g' (c • U) (d • V) = fun p => (k*c*d) * metricPair g U V p := by
  funext p
  simp only [metricPair,h,Pi.smul_apply,map_smul,smul_apply,smul_eq_mul]
  ring

private theorem jet_scaled (h : Scales g g' k) {p : Base} (c d e : ℝ) (X Y Z : Tangent p) :
    let U : Tangent p → Field := fun x => extend Coordinates x
    directional (U (c • X)) (metricPair g' (U (d • Y)) (U (e • Z))) =ᶠ[𝓝 p]
      fun q => (c*(k*d*e)) * directional (U X) (metricPair g (U Y) (U Z)) q := by
  intro U
  have pair : metricPair g' (extend Coordinates (d • Y)) (extend Coordinates (e • Z)) =ᶠ[𝓝 p]
      metricPair g' (d • extend Coordinates Y) (e • extend Coordinates Z) := by
    filter_upwards [extend_smul_near d Y,extend_smul_near e Z] with q hy hz
    change g'.inner q _ _ = g'.inner q _ _
    rw [hy,hz]
  have scaled := pair.trans (Filter.EventuallyEq.of_eq (pair_scaled h d e (extend Coordinates Y) (extend Coordinates Z)))
  filter_upwards [scaled.eventuallyEq_nhds,extend_smul_near c X] with q hp hx
  change directional (extend Coordinates (c • X)) _ q = _
  exact (directional_congr (U := extend Coordinates (c • X)) hp).trans ((directional_weight _ _ _ _).trans (by
    change _ * (mvfderiv productModel _ q _) = _
    rw [hx]; simp only [Pi.smul_apply,map_smul,smul_eq_mul,directional,U]; ring))

private theorem gamma_scaled (h : Scales g g' k) (c d e : ℝ) {p : Base} (X Y Z : Tangent p) :
    gamma g' (c • X) (d • Y) (e • Z) = k*c*d*e * gamma g X Y Z := by
  simp only [gamma,(jet_scaled h c d e X Y Z).self_of_nhds,(jet_scaled h d c e Y X Z).self_of_nhds,
    (jet_scaled h e c d Z X Y).self_of_nhds]
  ring

private theorem connection_scaled (h : Scales g g' k) (hk : k ≠ 0) (c : ℝ) {p : Base}
    (X Y : Tangent p) :
    nabla g' (extend Coordinates (c • X)) (extend Coordinates (c • Y)) p =
      c^2 • nabla g (extend Coordinates X) (extend Coordinates Y) p := by
  let L := nabla g' (extend Coordinates (c • X)) (extend Coordinates (c • Y)) p
  let R := c^2 • nabla g (extend Coordinates X) (extend Coordinates Y) p
  have eq (Z : Tangent p) : g.inner p L Z = g.inner p R Z := by
    have he := gamma_scaled h c c 1 X Y Z
    rw [one_smul,gamma_eq,gamma_eq,h] at he
    change g.inner p L Z = _
    dsimp only [R]
    rw [map_smul,smul_apply,smul_eq_mul]
    apply mul_left_cancel₀ hk
    exact he.trans (by ring)
  change L = R
  by_contra hn
  have hp := g.pos p (L-R) (sub_ne_zero.mpr hn)
  rw [show g.inner p (L-R) = g.inner p L - g.inner p R from map_sub _ _ _,sub_apply,eq (L-R),sub_self] at hp
  exact (lt_irrefl _ hp)

private theorem second_scaled (h : Scales g g' k) (c : ℝ) {p : Base} (X Y : Tangent p) :
    secondPart g' (c • X) (c • Y) = k*c^4 * secondPart g X Y := by
  let U := extend (E := Tangent) Coordinates X
  let V := extend (E := Tangent) Coordinates Y
  let a := fun q => directional V (metricPair g V U) q - directional U (metricPair g V V) q / 2
  let b := fun q => directional V (metricPair g U U) q / 2
  let u := extend (E := Tangent) Coordinates (c • X)
  let v := extend (E := Tangent) Coordinates (c • Y)
  have first : (fun q => directional v (metricPair g' v u) q - directional u (metricPair g' v v) q / 2)
      =ᶠ[𝓝 p] fun q => (k*c^3) * a q := by
    filter_upwards [jet_scaled h c c c Y Y X,jet_scaled h c c c X Y Y] with q h1 h2
    dsimp only [u,v,a,U,V]; rw [h1,h2]; ring
  have last : (fun q => directional v (metricPair g' u u) q / 2) =ᶠ[𝓝 p] fun q => (k*c^3) * b q := by
    filter_upwards [jet_scaled h c c c Y X X] with q h1
    dsimp only [u,v,b,U,V]; rw [h1]; ring
  change directional u _ p - directional v _ p = k*c^4*(directional U a p - directional V b p)
  rw [directional_congr (U := u) first,directional_congr (U := v) last,
    directional_weight u _ a,directional_weight v _ b]
  dsimp only [u,v]
  unfold directional
  rw [(extend_smul_near c X).self_of_nhds,(extend_smul_near c Y).self_of_nhds]
  simp only [Pi.smul_apply,map_smul,smul_eq_mul]
  dsimp only [a,b,U,V,directional]
  ring

/-- Rescaling the metric by a nonzero constant and both plane vectors by
`c` multiplies the lowered curvature numerator by `k c⁴`. -/
theorem curvatureNumerator_homothety (hk : k ≠ 0)
    (h : ∀ p X Y, g'.inner p X Y = k * g.inner p X Y)
    (c : ℝ) (p : Base) (X Y : Tangent p) :
    curvatureNumerator g' p (c • X) (c • Y) = k*c^4 * curvatureNumerator g p X Y := by
  rw [curvatureNumerator_coordinates,curvatureNumerator_coordinates]
  change secondPart g' _ _ + g'.inner p _ _ - g'.inner p _ _ =
    k*c^4 * (secondPart g _ _ + g.inner p _ _ - g.inner p _ _)
  simp only [second_scaled h c,connection_scaled h hk c,h,map_smul,smul_apply,smul_eq_mul]
  ring

end
end LocalHopf.SphereProduct
