import LocalHopf.CometricTaylor

/-! Curvature of the concrete background obtained by contracting its matrix
two-jet in the longitude-height chart. -/
namespace LocalHopf.SphereProduct.JetChart
open Real Matrix Filter Set LongitudeHeight Bundle
open scoped ContDiff Topology
noncomputable section

private abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

private def pairing (G : Mat) (u v : Params) :=
  ∑ i, ∑ j, (parameterBasis.equivFun u i*parameterBasis.equivFun v j)*G i j

private theorem coefficient_pairing (r s : E3 ≃ₗᵢ[ℝ] E3) {y : Params} (hy : y ∈ (chart r s).target)
    (g : SmoothMetric) (a b : Params) :
    coefficient r s g a b y = pairing (fun i j => coefficient r s g (parameterBasis i) (parameterBasis j) y) a b := by
  let p := (chart r s).symm y
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target hy)
  have e (u : Params) : field r s u p = ∑ i, parameterBasis.equivFun u i • field r s (parameterBasis i) p := by
    have sum := congrArg L (parameterBasis.equivFun.symm_apply_apply u)
    rw [parameterBasis.equivFun_symm_apply,map_sum] at sum
    simp_rw [L.map_smul] at sum
    simpa only [hL] using sum.symm
  change g.inner p (field r s a p) (field r s b p) = ∑ i, ∑ j, _ * g.inner p (field r s (parameterBasis i) p) (field r s (parameterBasis j) p)
  conv_lhs => rw [e a,e b]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _; ring

/-- The two directional derivatives of the covariant Gram matrix in any direction. -/
def metricTaylor (t u w : ℝ) (d : Params) : Fin 3 → Mat :=
  let den := 2*Profiles.D t u
  let B : Mat := ![![(1+2*t)⁻¹,0,0,0],![0,1,0,0],![0,0,(1+t)/den,-t*u/den],![0,0,-t*u/den,(1+t)/den]]
  let A := separationJet t u w d.1.2 d.2.1 d.2.2
  ![B,-(B*A 1*B),B*A 1*B*A 1*B-B*A 2*B]

/-- The explicit signed-separation Taylor coefficients of each covariant entry
along any straight spatial direction in the actual chart. -/
theorem coordinate_gram_jet (v : FlatLocus.Representative) (t : ℝ) (ht : 0 ≤ t) (d : Params) (i j : Fin 4) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let T := metricTaylor t (v.val.2.1.val ⬝ᵥ v.val.2.2.val) ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val) d
    SpatialJet (fun z : ℝ => coefficient r s (backgroundMetric t ht) (parameterBasis i) (parameterBasis j) (z • d))
      (T 0 i j) (T 1 i j) (T 2 i j) := by
  intro r s T
  have ln (z : ℝ) : line d.1.1 d.1.2 d.2.1 d.2.2 z = z • d := by
    ext <;> dsimp [line] <;> ring
  have q := metricGram_jet v t ht d.1.1 d.1.2 d.2.1 d.2.2 i j
  dsimp only at q
  simp only [ln,zero_smul] at q
  have eq := metric_at_center v t ht
  dsimp only at eq
  let B : Mat := fun m n => coefficient r s (backgroundMetric t ht) (parameterBasis m) (parameterBasis n) 0
  let A := inverseTaylor v t d.1.1 d.1.2 d.2.1 d.2.2
  change SpatialJet _ (B i j) (-(B*A 1*B) i j) ((B*A 1*B*A 1*B-B*A 2*B) i j) at q
  have ee : B = T 0 := eq
  have ae : A = _ := inverseTaylor_eq_separationJet v t d.1.1 d.1.2 d.2.1 d.2.2
  rw [ee,ae] at q
  exact q

private theorem fields_jet (v : FlatLocus.Representative) (g : SmoothMetric) (d a b : Params) (T : Fin 3 → Mat)
    (hT : ∀ i j, SpatialJet (fun z : ℝ => coefficient (align _ _ v.property.1) (align _ _ v.property.2)
      g (parameterBasis i) (parameterBasis j) (z • d)) (T 0 i j) (T 1 i j) (T 2 i j)) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    SpatialJet (fun z : ℝ => coefficient r s g a b (z • d)) (pairing (T 0) a b) (pairing (T 1) a b) (pairing (T 2) a b) := by
  intro r s
  have j := jet_sum (fun i => jet_sum (fun j => jet_scale (parameterBasis.equivFun a i*parameterBasis.equivFun b j) (hT i j)))
  apply j.congr
  have path : Continuous (fun z : ℝ => z • d) := continuous_id.smul continuous_const
  have e : (0:ℝ) • d ∈ (chart r s).target := by rw [zero_smul]; exact (center v).1
  filter_upwards [path.continuousAt.preimage_mem_nhds ((chart r s).open_target.mem_nhds e)] with z hz
  exact coefficient_pairing r s hz _ a b

theorem D_line (f : Params → ℝ) (h : ContDiffAt ℝ ∞ f 0) (d : Params) :
    D d f 0 = deriv (fun z : ℝ => f (z • d)) 0 := by
  have line : HasDerivAt (fun z : ℝ => z • d) d 0 := by simpa using (hasDerivAt_id' (0:ℝ)).smul_const d
  exact ((h.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 line (by simp)).deriv.symm

private theorem D_hessian (f : Params → ℝ) (h : ContDiffAt ℝ ∞ f 0) (a b : Params) :
    D a (D b f) 0 = fderiv ℝ (fderiv ℝ f) 0 a b := by
  let ev : (Params →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ b
  have dh := ((h.fderiv_right (by simp : ∞+1 ≤ ∞)).differentiableAt (by simp)).hasFDerivAt
  exact congrArg (fun L : Params →L[ℝ] ℝ => L a) ((ev.hasFDerivAt.comp 0 dh).fderiv)


/-- Polarization recovers the second curvature term from diagonal directional derivatives. -/
theorem second_from_diagonal (C q : Params → Params → Params → ℝ) (a b : Params)
    (reg : ∀ u w, ContDiffAt ℝ ∞ (C u w) 0)
    (dd : ∀ d u w, D d (D d (C u w)) 0=2*q d u w) :
    second C a b 0=q (a+b) b a-q a b a-q b b a-q a b b-q b a a := by
  have mixed (u w : Params) : D a (D b (C u w)) 0 = q (a+b) u w-q a u w-q b u w := by
    let H := fderiv ℝ (fderiv ℝ (C u w)) 0
    have diag (d : Params) : H d d = 2*q d u w := (D_hessian _ (reg _ _) d d).symm.trans (dd d u w)
    have sym : H b a = H a b := (reg u w).isSymmSndFDerivAt (by simp) b a
    rw [D_hessian _ (reg _ _)]
    change H a b = _
    have add := diag (a+b)
    rw [H.map_add,add_apply,map_add,map_add] at add
    linarith only [sym, add, diag a, diag b]
  have diff (d u w : Params) : DifferentiableAt ℝ (D d (C u w)) 0 :=
    (((reg u w).fderiv_right (by simp : ∞+1 ≤ ∞)).clm_apply (contDiffAt_const (c := d))).differentiableAt (by simp)
  have half (f : Params → ℝ) (hf : DifferentiableAt ℝ f 0) (d : Params) :
      D d (fun x => f x/2) 0 = D d f 0/2 := by
    have eq := congrArg (fun L : Params →L[ℝ] ℝ => L d) (hf.hasFDerivAt.const_smul (2:ℝ)⁻¹).fderiv
    simpa only [D,Pi.smul_def,smul_apply,smul_eq_mul,div_eq_inv_mul] using eq
  have sub (f g : Params → ℝ) (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0) (d : Params) :
      D d (fun x => f x-g x) 0 = D d f 0-D d g 0 := by
    exact congrArg (fun L : Params →L[ℝ] ℝ => L d) (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
  unfold second
  rw [sub (D b (C b a)) (fun x => D a (C b b) x/2) (diff ..) (by simpa only [div_eq_inv_mul] using (diff a b b).const_mul (2:ℝ)⁻¹),
    half _ (diff ..),half _ (diff ..),mixed,dd,dd]
  ring

/-- Contraction of the directional covariant matrix jets with the inverse Gram matrix at the origin. -/
def contractSpatial (T : Params → Fin 3 → Mat) (I : Mat) (a b : Params) :=
  let q (d u z : Params) := pairing (T d 2) u z
  let first (d u z : Params) := pairing (T d 1) u z
  let Γ (u w : Params) (i : Fin 4) :=
    (first u w (parameterBasis i)+first w (parameterBasis i) u-first (parameterBasis i) u w)/2
  q (a+b) b a-q a b a-q b b a-q a b b-q b a a +
    Γ a b ⬝ᵥ I *ᵥ Γ a b - Γ a a ⬝ᵥ I *ᵥ Γ b b

/-- Finite contraction of the two background metric derivatives in the adapted frame. -/
def backgroundNumerator (t c w : ℝ) (a b : Params) : ℝ :=
  let I : Mat := ![![1+2*t,0,0,0],![0,1,0,0],![0,0,2*(1+t),2*t*c],![0,0,2*t*c,2*(1+t)]]
  contractSpatial (metricTaylor t c w) I a b

/-- For any realized metric the directional jets of its sixteen Gram entries compute its full sectional numerator. -/
theorem curvature_from_spatial_terms (v : FlatLocus.Representative) (g : SmoothMetric) (T : Params → Fin 3 → Mat) (I : Mat)
    (entry : ∀ d i j, SpatialJet (fun z : ℝ => coefficient (align _ _ v.property.1) (align _ _ v.property.2)
      g (parameterBasis i) (parameterBasis j) (z • d)) (T d 0 i j) (T d 1 i j) (T d 2 i j))
    (inv : let G : Mat := fun i j => coefficient (align _ _ v.property.1) (align _ _ v.property.2) g (parameterBasis i) (parameterBasis j) 0
           G⁻¹ = I)
    (a b : Params) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    curvatureNumerator g p (field r s a p) (field r s b p) = contractSpatial T I a b := by
  intro r s p
  let C := coefficient r s g
  have h0 : (0:Params) ∈ (chart r s).target := (center v).1
  have reg (u w : Params) {y : Params} (hy : y ∈ (chart r s).target) : ContDiffAt ℝ ∞ (C u w) y := by
    let : RiemannianBundle (Tangent : Base → Type) := ⟨g.toRiemannianMetric⟩
    have hp := (chart r s).map_target hy
    exact contMDiffAt_iff_contDiffAt.mp (((field_smooth r s hp u).inner_bundle (field_smooth r s hp w)).comp y (inv_smooth r s hy))
  let q (d u z : Params) := pairing (T d 2) u z
  let first (d u z : Params) := pairing (T d 1) u z
  have dx (d u w : Params) : D d (C u w) 0 = first d u w :=
    (D_line _ (reg u w h0) d).trans (fields_jet v g d u w (T d) (entry d)).first
  have dd (d u w : Params) : D d (D d (C u w)) 0 = 2*q d u w :=
    (along_axis v _ d (fun _ hy => reg u w hy) h0).trans (fields_jet v g d u w (T d) (entry d)).second
  have second_eq := second_from_diagonal C q a b (fun u w => reg u w h0) dd
  let Γ (u w : Params) (i : Fin 4) := (first u w (parameterBasis i)+first w (parameterBasis i) u-first (parameterBasis i) u w)/2
  have gamma (u w : Params) (i : Fin 4) : christoffel r s g u w (parameterBasis i) 0 = Γ u w i := by
    change (D u (C w _) 0+D w (C _ u) 0-D _ (C u w) 0)/2 = _
    rw [dx,dx,dx]
  have main := curvature_from_chart_jet r s ((chart r s).map_target h0) g parameterBasis a b
  dsimp only at main
  rw [(chart r s).right_inv h0] at main
  let G : Mat := fun i j => C (parameterBasis i) (parameterBasis j) 0
  change _ = second C a b 0 + _ - _ at main
  simp_rw [gamma] at main
  change _ = second C a b 0 + Γ a b ⬝ᵥ G⁻¹ *ᵥ Γ a b - Γ a a ⬝ᵥ G⁻¹ *ᵥ Γ b b at main
  rw [second_eq,show G⁻¹ = I from inv] at main
  exact main

/-- Intrinsic curvature on arbitrary chart vectors at an arbitrary sphere pair
with a common normal, including coincident and antipodal pairs. -/
theorem curvature_eq_backgroundNumerator (v : FlatLocus.Representative) (t : ℝ) (ht : 0 ≤ t) (a b : Params) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    curvatureNumerator (backgroundMetric t ht) p (field r s a p) (field r s b p) =
      backgroundNumerator t (v.val.2.1.val ⬝ᵥ v.val.2.2.val) ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val) a b := by
  apply curvature_from_spatial_terms v (backgroundMetric t ht) (metricTaylor t _ _) _
  · exact coordinate_gram_jet v t ht
  · exact inverse_at_center v t ht

end
end LocalHopf.SphereProduct.JetChart
