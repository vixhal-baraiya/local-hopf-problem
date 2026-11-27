import LocalHopf.BackgroundGrowth
import LocalHopf.TorusFrame
import LocalHopf.ChartExpansion
import LocalHopf.CubicCorrection
import LocalHopf.EquatorForcing

/-! The intrinsic background at the great-circle tori, in centered longitude-height coordinates. -/
namespace LocalHopf.SphereProduct.JetChart
open Matrix Real Filter Set
open scoped Manifold Topology ContDiff
noncomputable section

def align (n p : FlatLocus.UnitVector) (perp : n.val ⬝ᵥ p.val = 0) := (axesBasis n p perp).repr.symm

theorem align_apply (n p : FlatLocus.UnitVector) (perp : n.val ⬝ᵥ p.val = 0) (x : R3) :
    (align n p perp (WithLp.toLp 2 x)).ofLp =
      x 0 • p.val + x 1 • (n.val ⨯₃ p.val) + x 2 • n.val := by
  let e (i : Fin 3) := EuclideanSpace.single i (1:ℝ)
  have eq : WithLp.toLp 2 x = x 0 • e 0 + x 1 • e 1 + x 2 • e 2 := by
    ext i; fin_cases i <;> simp [e,EuclideanSpace.single]
  rw [eq]
  simp only [align,map_add,map_smul,e,axesBasis_apply]
  rfl

private theorem aligned_lon (n p : FlatLocus.UnitVector) (perp : n.val ⬝ᵥ p.val = 0)
    (s z : ℝ) (hz : |z| < 1) :
    (align n p perp (WithLp.toLp 2 (LongitudeHeight.lonVector s z))).ofLp =
      n.val ⨯₃ (sphereAction (align n p perp) (LongitudeHeight.point (s,z))).val.ofLp := by
  let rad := sqrt (1-z^2)
  have e : (LongitudeHeight.point (s,z)).val.ofLp = ![rad*cos s,rad*sin s,z] := by
    change ![cos (arcsin z)*cos s,cos (arcsin z)*sin s,sin (arcsin z)] = _
    rw [cos_arcsin,sin_arcsin (abs_lt.mp hz).1.le (abs_lt.mp hz).2.le]
  change _ = n.val ⨯₃ (align n p perp (WithLp.toLp 2 (LongitudeHeight.point (s,z)).val.ofLp)).ofLp
  rw [align_apply,align_apply,e]
  have twice : n.val ⨯₃ (n.val ⨯₃ p.val) = -p.val := by
    rw [cross_cross_eq_smul_sub_smul',perp,show n.val ⬝ᵥ n.val = 1 from n.property,zero_smul,one_smul,zero_sub]
  change (-(rad)*sin s) • p.val + (rad*cos s) • (n.val ⨯₃ p.val) + (0:ℝ) • n.val =
    n.val ⨯₃ ((rad*cos s) • p.val+(rad*sin s) • (n.val ⨯₃ p.val)+z • n.val)
  simp only [map_add,map_smul,twice,cross_self,smul_zero,zero_smul,add_zero,smul_neg,neg_mul,neg_smul]
  abel

/-- The chart whose height axes both use the actual common normal. -/
def coreChart (v : FlatLocus.Representative) := chart (align _ _ v.property.1) (align _ _ v.property.2)

private def angular (c : ℝ × ℝ) : Params := (c,0)

private theorem angular_velocity (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (c : ℝ × ℝ) :
    let p := (coreChart v).symm y
    fderiv ℝ (ambientPoint ∘ (coreChart v).symm) y (angular c) =
      Cheeger.longitude (ambientPoint p).1 (ambientPoint p).2 v.val.1.val (c.1-c.2) (c.1+c.2) := by
  dsimp only
  rw [coreChart,chart_velocity _ _ hy]
  simp only [angular, Prod.fst_zero,Prod.snd_zero,zero_smul,add_zero]
  change ((align _ _ _ (WithLp.toLp 2 ((c.1-c.2) • _))).ofLp, (align _ _ _ (WithLp.toLp 2 ((c.1+c.2) • _))).ofLp) = _
  rw [WithLp.toLp_smul,WithLp.toLp_smul,map_smul,map_smul]
  apply Prod.ext
  · change (c.1-c.2) • _ = (c.1-c.2) • _
    exact congrArg ((c.1-c.2) • ·) (aligned_lon _ _ v.property.1 (y.1.1-y.1.2) y.2.1 hy.2.1.1.2)
  · change (c.1+c.2) • _ = (c.1+c.2) • _
    exact congrArg ((c.1+c.2) • ·) (aligned_lon _ _ v.property.2 (y.1.1+y.1.2) y.2.2 hy.2.2.1.2)


/-- Ambient velocities of the chart longitude fields at the center of the torus. -/
theorem center_longitude (v : FlatLocus.Representative) (c : ℝ × ℝ) :
    let r := (axesBasis _ _ v.property.1).repr.symm
    let s := (axesBasis _ _ v.property.2).repr.symm
    let p := (chart r s).symm 0
    ambientVelocityL p (field r s (c,0) p) =
      Cheeger.longitude v.val.2.1.val v.val.2.2.val v.val.1.val (c.1-c.2) (c.1+c.2) := by
  intro r s p
  have hy : (0 : Params) ∈ (coreChart v).target := (center v).1
  change ambientVelocityL ((chart r s).symm 0) (field r s (c,0) ((chart r s).symm 0)) = _
  rw [ambient_field r s ((chart r s).map_target hy), (chart r s).right_inv hy]
  have h := angular_velocity v hy c
  dsimp only at h
  rw [show (coreChart v).symm 0 = _ from (center v).2] at h
  exact h

private def raw (v : FlatLocus.Representative) := ambientPoint ∘ (coreChart v).symm
private def sep (v : FlatLocus.Representative) (y : Params) := (raw v y).1 ⬝ᵥ (raw v y).2
private def gram (v : FlatLocus.Representative) (g : SmoothMetric) :=
  coefficient (align _ _ v.property.1) (align _ _ v.property.2) g

private theorem coord_height (n p : FlatLocus.UnitVector) (perp : n.val ⬝ᵥ p.val = 0)
    (s z : ℝ) (hz : |z| < 1) :
    n.val ⬝ᵥ (sphereAction (align n p perp) (LongitudeHeight.point (s,z))).val.ofLp = z := by
  change n.val ⬝ᵥ (align n p perp (WithLp.toLp 2 (LongitudeHeight.point (s,z)).val.ofLp)).ofLp = z
  rw [align_apply]
  simp only [dotProduct_add,dotProduct_smul,smul_eq_mul,perp,dot_self_cross,
    show n.val ⬝ᵥ n.val = 1 from n.property,mul_zero,mul_one,zero_add]
  exact sin_arcsin (abs_lt.mp hz).1.le (abs_lt.mp hz).2.le

private theorem base_gram (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (t : ℝ) (ht : 0 ≤ t) (a b : Params) :
    let p := raw v y
    let L := fderiv ℝ (raw v) y
    gram v (backgroundMetric t ht) a b y = Cheeger.pairing p.1 p.2 t ht (L a) (L b)/2 := by
  dsimp only
  let p := (coreChart v).symm y
  rw [gram,background_coefficient _ _ hy,Cheeger.pairing_formula (raw v y).1 (raw v y).2 ht
    (unitSphere.symm p.1).property (unitSphere.symm p.2).property]
  rfl

private theorem longitudinal_gram (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (t : ℝ) (ht : 0 ≤ t) (a b : ℝ × ℝ) :
    gram v (backgroundMetric t ht) (angular a) (angular b) y =
      Cheeger.longitudeGram t (sep v y) y.2.1 y.2.2 (a.1-a.2) (a.1+a.2) (b.1-b.2) (b.1+b.2)/2 := by
  rw [base_gram v hy]
  let p := (coreChart v).symm y
  change Cheeger.pairing (ambientPoint p).1 (ambientPoint p).2 t ht
    (fderiv ℝ (ambientPoint ∘ (coreChart v).symm) y (angular a))
    (fderiv ℝ (ambientPoint ∘ (coreChart v).symm) y (angular b))/2 = _
  rw [angular_velocity v hy,angular_velocity v hy,Cheeger.pairing_longitude (ambientPoint p).1
    (ambientPoint p).2 v.val.1.val ht (unitSphere.symm p.1).property (unitSphere.symm p.2).property v.val.1.property]
  have pz : v.val.1.val ⬝ᵥ (ambientPoint p).1 = y.2.1 := coord_height _ _ v.property.1 _ _ hy.2.1.1.2
  have qz : v.val.1.val ⬝ᵥ (ambientPoint p).2 = y.2.2 := coord_height _ _ v.property.2 _ _ hy.2.2.1.2
  rw [pz,qz]; rfl

private def ray (y d : Params) (s : ℝ) := y+s • d
private theorem ray_deriv (y d : Params) : HasDerivAt (ray y d) d 0 := by
  change HasDerivAt (fun x : ℝ => y+x • d) d 0
  simpa only [one_smul] using ((hasDerivAt_id' (0:ℝ)).smul_const d).const_add y

private theorem dir_zero (f : Params → ℝ) (y d : Params) (hf : HasDerivAt (f ∘ ray y d) 0 0) :
    D d f y = 0 := by
  by_cases reg : DifferentiableAt ℝ f y
  · exact ((reg.hasFDerivAt.comp_hasDerivAt_of_eq 0 (ray_deriv y d) (by simp [ray])).deriv.symm).trans hf.deriv
  · simp [D,fderiv_zero_of_not_differentiableAt reg]

private theorem ray_target (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target) (d : Params) :
    ∀ᶠ s in 𝓝 (0:ℝ), ray y d s ∈ (coreChart v).target := by
  apply (ray_deriv y d).continuousAt.preimage_mem_nhds
  apply (coreChart v).open_target.mem_nhds
  simpa [ray] using hy

private theorem stationary (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (slice : y.2 = 0) (t : ℝ) (ht : 0 ≤ t) (a b : ℝ × ℝ) (d : Params) :
    D d (gram v (backgroundMetric t ht) (angular a) (angular b)) y = 0 := by
  let u := sep v ∘ ray y d
  let z := fun s => (ray y d s).2.1
  let w := fun s => (ray y d s).2.2
  have reg : DifferentiableAt ℝ (raw v) y := (contMDiffAt_iff_contDiffAt.mp
    (ambientPoint_smooth.contMDiffAt.comp _ (inv_smooth _ _ hy))).differentiableAt (by simp)
  have du : DifferentiableAt ℝ u 0 := by
    have h : DifferentiableAt ℝ (sep v) y := by
      change DifferentiableAt ℝ (fun x => ∑ i, (raw v x).1 i * (raw v x).2 i) y
      fun_prop
    exact (h.hasFDerivAt.comp_hasDerivAt_of_eq 0 (ray_deriv y d) (by simp [ray])).differentiableAt
  have uz : u 0 ^ 2 ≤ 1 := by
    let p := (coreChart v).symm y
    change (sep v (ray y d 0))^2 ≤ 1
    simp only [ray,zero_smul,add_zero,sep,raw,Function.comp_apply]
    let P := (ambientPoint p).1
    let Q := (ambientPoint p).2
    have nn := BackgroundGrowth.sqLength_nonneg (P ⨯₃ Q)
    change 0 ≤ (P ⨯₃ Q) ⬝ᵥ (P ⨯₃ Q) at nn
    rw [cross_dot_cross,show P ⬝ᵥ P = 1 from (unitSphere.symm p.1).property,
      show Q ⬝ᵥ Q = 1 from (unitSphere.symm p.2).property,dotProduct_comm Q P] at nn
    change (P ⬝ᵥ Q)^2 ≤ 1
    nlinarith only [nn]
  have H := Cheeger.longitudeGram_stationary (a.1-a.2) (a.1+a.2) (b.1-b.2) (b.1+b.2) ht du
    (show DifferentiableAt ℝ z 0 by dsimp [z,ray]; fun_prop)
    (show DifferentiableAt ℝ w 0 by dsimp [w,ray]; fun_prop) uz
    (by simp [z,ray,slice]) (by simp [w,ray,slice])
  apply dir_zero
  have hd := H.div_const 2
  rw [zero_div] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [ray_target v hy d] with s hs
  exact longitudinal_gram v hs t ht a b

private theorem vertical_velocity (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2 = 0) (d : ℝ × ℝ) :
    fderiv ℝ (raw v) y (0,d) = (d.1 • v.val.1.val,d.2 • v.val.1.val) := by
  rw [raw,coreChart,chart_velocity _ _ hy]
  have H (n p : FlatLocus.UnitVector) (hp : n.val ⬝ᵥ p.val = 0) (s c : ℝ) :
      (align n p hp (WithLp.toLp 2 (c • LongitudeHeight.heightVector s 0))).ofLp = c • n.val := by
    rw [align_apply]
    simp [LongitudeHeight.heightVector]
  simp only [Prod.fst_zero,Prod.snd_zero,sub_zero,add_zero,zero_smul,zero_add,hz]
  exact Prod.ext (H _ _ _ _ _) (H _ _ _ _ _)

private theorem vertical_pair (p q n : R3) (t : ℝ) (ht : 0 ≤ t) (a b r s : ℝ)
    (hp : p ⬝ᵥ p = 1) (hq : q ⬝ᵥ q = 1) (np : n ⬝ᵥ p = 0) (nq : n ⬝ᵥ q = 0) :
    Cheeger.pairing p q t ht (Cheeger.longitude p q n a b) (r • n,s • n) = 0 := by
  have ba := dotProduct_comm p n
  have bb := dotProduct_comm q n
  rw [Cheeger.pairing_formula p q ht hp hq]
  simp [Cheeger.longitude,gprod,moment,Cheeger.orbitSolve,cross_cross_eq_smul_sub_smul',hp,hq,
    add_dotProduct,dotProduct_add,dotProduct_smul,smul_dotProduct,np,nq,ba,bb,
    dotProduct_comm (n ⨯₃ p) n,dotProduct_comm (n ⨯₃ q) n,
    dotProduct_comm (p ⨯₃ n) n,dotProduct_comm (q ⨯₃ n) n]

private theorem mixed_slice (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2=0) (t : ℝ) (ht : 0 ≤ t) (a : ℝ × ℝ) (d : Params) :
    gram v (backgroundMetric t ht) (angular a) d y =
      ((a.1-a.2)*(d.1.1-d.1.2)+(a.1+a.2)*(d.1.1+d.1.2)-t/(Profiles.hh t)*
        ((a.1-a.2+(a.1+a.2))*(d.1.1-d.1.2+(d.1.1+d.1.2))))/2 := by
  let L := fderiv ℝ (raw v) y
  let p := (coreChart v).symm y
  let P := (ambientPoint p).1
  let Q := (ambientPoint p).2
  let n := v.val.1.val
  have np : n ⬝ᵥ P = 0 := (coord_height _ _ v.property.1 _ _ hy.2.1.1.2).trans
    (congrArg Prod.fst hz)
  have nq : n ⬝ᵥ Q = 0 := (coord_height _ _ v.property.2 _ _ hy.2.2.1.2).trans
    (congrArg Prod.snd hz)
  have split : L d = L (angular d.1) + L (0,d.2) := by rw [← L.map_add]; congr 1; exact (Prod.ext (by simp [angular]) (by simp [angular])).symm
  have add (x b c : Cheeger.V) : Cheeger.pairing P Q t ht x (b+c) =
      Cheeger.pairing P Q t ht x b + Cheeger.pairing P Q t ht x c := by simp [Cheeger.pairing,gprod,dotProduct_add]; ring
  have H := longitudinal_gram v hy t ht a d.1
  rw [base_gram v hy] at H ⊢
  change Cheeger.pairing P Q t ht (L (angular a)) (L (angular d.1))/2 = _ at H
  change Cheeger.pairing P Q t ht (L (angular a)) (L d)/2 = _
  rw [split,add,show L (0,d.2) = _ from vertical_velocity v hy hz d.2]
  have ang : L (angular a) = Cheeger.longitude P Q n (a.1-a.2) (a.1+a.2) := angular_velocity v hy a
  have zero := vertical_pair P Q n t ht (a.1-a.2) (a.1+a.2) d.2.1 d.2.2
    (unitSphere.symm p.1).property (unitSphere.symm p.2).property np nq
  rw [← ang] at zero
  rw [zero,add_zero,H,hz]
  simp [Cheeger.longitudeGram]

private theorem angular_const (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2 = 0) (a : ℝ × ℝ) {f : Params → ℝ} {C : ℝ}
    (h : ∀ q ∈ (coreChart v).target, q.2 = 0 → f q = C) : D (angular a) f y = 0 := by
  apply dir_zero _ _ _
  apply (hasDerivAt_const (0:ℝ) C).congr_of_eventuallyEq
  filter_upwards [ray_target v hy (angular a)] with s hs
  exact h _ hs (by simp [ray,angular,hz])

private theorem mixed_deriv (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2 = 0) (t : ℝ) (ht : 0 ≤ t) (a b : ℝ × ℝ) (d : Params) :
    D (angular a) (gram v (backgroundMetric t ht) (angular b) d) y = 0 :=
  angular_const v hy hz a fun _ hq hs => mixed_slice v hq hs t ht b d

theorem core_gamma (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2 = 0) (t : ℝ) (ht : 0 ≤ t) (a b : ℝ × ℝ) (d : Params) :
    christoffel (align _ _ v.property.1) (align _ _ v.property.2) (backgroundMetric t ht)
      (angular a) (angular b) d y = 0 := by
  let g := backgroundMetric t ht
  have symm (u w : Params) : gram v g u w = gram v g w u := funext fun q => g.symm _ _ _
  change (D _ (gram v g (angular b) d) y+D _ (gram v g d (angular a)) y-D d (gram v g (angular a) (angular b)) y)/2 = 0
  rw [symm d (angular a)]
  dsimp only [g]
  rw [mixed_deriv v hy hz t ht a b d,mixed_deriv v hy hz t ht b a d,stationary v hy hz t ht a b d]
  norm_num

/-- The actual Levi-Civita curvature numerator vanishes on every common-normal
longitude plane, including at either singular separation. -/
theorem flat_torus_curvature (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2 = 0) (t : ℝ) (ht : 0 ≤ t) (a b : ℝ × ℝ) :
    let r := (axesBasis _ _ v.property.1).repr.symm
    let s := (axesBasis _ _ v.property.2).repr.symm
    let p := (chart r s).symm y
    curvatureNumerator (backgroundMetric t ht) p (field r s (a,0) p) (field r s (b,0) p) = 0 := by
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let g := backgroundMetric t ht
  let p := (coreChart v).symm y
  let A := angular a
  let B := angular b
  have dim : Module.finrank ℝ Params = 4 := by simp [Params,Module.finrank_prod]
  let base := (Module.finBasis ℝ Params).reindex (finCongr dim)
  have cur := curvature_from_chart_jet r s ((coreChart v).map_target hy) g base A B
  change curvatureNumerator g p (field r s A p) (field r s B p) = _
  rw [cur,(show chart r s p = y from (coreChart v).right_inv hy)]
  have ga (u w : ℝ × ℝ) : (fun i => christoffel r s g (angular u) (angular w) (base i) y) = 0 :=
    funext fun i => core_gamma v hy hz t ht u w (base i)
  change _ + (fun i => christoffel r s g (angular a) (angular b) (base i) y) ⬝ᵥ _ - _ = 0
  simp only [A,B,ga,zero_dotProduct,add_zero,sub_zero]
  have row (q : Params) (hq : q ∈ (coreChart v).target) (hs : q.2 = 0) (u w l : ℝ × ℝ) :
      D (angular u) (coefficient r s g (angular w) (angular l)) q = 0 := mixed_deriv v hq hs t ht u w _
  rw [angular_const v hy hz a (C := 0) (by intros q hq hs; rw [row q hq hs,row q hq hs]; norm_num),
    angular_const v hy hz b (C := 0) (by intros q hq hs; rw [row q hq hs]; norm_num),sub_zero]

private theorem bilinear_longitudes (H : AmbientForm) (u w : Cheeger.V) (a b : ℝ × ℝ)
    (hw : H w u = H u w) : H (a.1 • u-a.2 • w) (b.1 • u-b.2 • w) =
      a.1*b.1*H u u - (a.1*b.2+a.2*b.1)*H u w + a.2*b.2*H w w := by
  simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul,hw]
  ring

private theorem slice_velocity (v : FlatLocus.Representative) {q : Params} (hq : q ∈ (coreChart v).target)
    (d : ℝ × ℝ) :
    let p := (coreChart v).symm q
    let n := v.val.1.val
    ambientVelocityL p (field (align _ _ v.property.1) (align _ _ v.property.2) (angular d) p) =
      d.1 • K (point₁ p) (point₂ p) n - d.2 • J (point₁ p) (point₂ p) n := by
  intro p n
  have vel := ambient_field _ _ ((coreChart v).map_target hq) (angular d)
  change ambientVelocityL p _ = fderiv ℝ (raw v) ((coreChart v) p) (angular d) at vel
  rw [show coreChart v p=q from (coreChart v).right_inv hq] at vel
  rw [vel,show fderiv ℝ (raw v) q (angular d) = _ from angular_velocity v hq d]
  change Cheeger.longitude (point₁ p) (point₂ p) n (d.1-d.2) (d.1+d.2) = _
  apply Prod.ext <;> simp only [Cheeger.longitude,K,J,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
    sub_smul,add_smul,smul_neg,sub_neg_eq_add]

set_option maxHeartbeats 800000 in
private theorem first_slice (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2 = 0) (t : ℝ) (ht : 0 ≤ t) (a b : ℝ × ℝ) :
    let n := v.val.1.val
    tensor (align _ _ v.property.1) (align _ _ v.property.2) (firstOrderTensor t ht) (angular a) (angular b) y =
      a.1*b.1*(Profiles.lamC*(n 2/Profiles.hh t)^2) -
      (a.1*b.2+a.2*b.1)*(Profiles.lamD*(n 0/Profiles.hh t)*n 2/2) := by
  let p := (coreChart v).symm y
  let n := v.val.1.val
  let P := point₁ p
  let Q := point₂ p
  have np : n ⬝ᵥ P = 0 := (coord_height _ _ v.property.1 _ _ hy.2.1.1.2).trans (congrArg Prod.fst hz)
  have nq : n ⬝ᵥ Q = 0 := (coord_height _ _ v.property.2 _ _ hy.2.2.1.2).trans (congrArg Prod.snd hz)
  let fld := field (align _ _ v.property.1) (align _ _ v.property.2)
  let H := (firstOrderTensor t ht).form p
  change H (ambientVelocityL p (fld (angular a) p)) (ambientVelocityL p (fld (angular b) p)) = _
  obtain ⟨uu,uv,vv⟩ := firstOrder_on_torus t ht p n np nq
  change H (K P Q n) (K P Q n) = _ at uu
  change H (K P Q n) (J P Q n) = _ at uv
  change H (J P Q n) (J P Q n) = _ at vv
  have vu : H (J P Q n) (K P Q n) = H (K P Q n) (J P Q n) := (firstOrderTensor t ht).symm p _ _
  rw [slice_velocity v hy a,slice_velocity v hy b,bilinear_longitudes H _ _ a b vu,uu,uv,vv,mul_zero,add_zero]

private theorem angular_variation (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2 = 0) (t : ℝ) (ht : 0 ≤ t) (A : Fin 4 → AmbientTensor) (hbg : A 0 = backgroundTensor t ht)
    (realizes : ∀ᶠ r in 𝓝 (0:ℝ), ∃ g : SmoothMetric, Realizes g r A) (a b : ℝ × ℝ) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm y
    let pair := TangentPair.mk p (field r s (angular a) p) (field r s (angular b) p)
    HasDerivAt (pair.numerator A) (second (tensor r s (A 1)) (angular a) (angular b) y) 0 := by
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (coreChart v).symm y
  let g := backgroundMetric t ht
  let U := angular a
  let V := angular b
  let pair := TangentPair.mk p (field r s U p) (field r s V p)
  change HasDerivAt (pair.numerator A) (second _ _ _ _) 0
  have dim : Module.finrank ℝ Params = 4 := by simp [Params,Module.finrank_prod]
  let base := (Module.finBasis ℝ Params).reindex (finCongr dim)
  obtain ⟨L,hL⟩ := field_equiv r s ((coreChart v).map_target hy)
  let B : Frame p := base.map L.toLinearEquiv
  have bval (i : Fin 4) : B i = field r s (base i) p := by simpa [B] using hL (base i)
  have mat : (fun i j => tensor r s (A 0) (base i) (base j) y) = gramMatrix g B := by
    rw [hbg]
    funext i j
    change g.inner p (field r s (base i) p) (field r s (base j) p) = g.inner p (B i) (B j)
    rw [bval,bval]
  have flat (c d : ℝ × ℝ) (w : Params) : symbol (tensor r s (A 0)) (angular c) (angular d) w y = 0 := by
    rw [hbg]
    exact core_gamma v hy hz t ht c d w
  have h := tensorNumerator_deriv r s A base y U V (mat ▸ (gram_isUnit g B).ne_zero)
    (fun w => ⟨flat a a w,flat a b w,flat b b w⟩)
  apply h.congr_of_eventuallyEq
  filter_upwards [realizes] with z hg
  obtain ⟨g,hg⟩ := hg
  exact (pair.numerator_eq hg).trans (tensorNumerator_realizes r s hg hy base U V)

/-- Lemma 4.3 for the actual prescribed tensor family: the first derivative
of its intrinsic curvature numerator is zero on every common-normal plane. -/
theorem flat_torus_first (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2 = 0) (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) (a b : ℝ × ℝ) :
    let r := (axesBasis _ _ v.property.1).repr.symm
    let s := (axesBasis _ _ v.property.2).repr.symm
    let p := (chart r s).symm y
    let pair := TangentPair.mk p (field r s (a,0) p) (field r s (b,0) p)
    HasDerivAt (pair.numerator (paperCoefficients t ht χ)) 0 0 := by
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (coreChart v).symm y
  let A := paperCoefficients t ht χ
  let U := angular a
  let V := angular b
  let pair := TangentPair.mk p (field r s U p) (field r s V p)
  change HasDerivAt (pair.numerator A) 0 0
  have h := angular_variation v hy hz t ht A rfl (paper_metrics_realize t ht χ) a b
  change HasDerivAt (pair.numerator A) (second (tensor r s (A 1)) U V y) 0 at h
  have row (q : Params) (hq : q ∈ (coreChart v).target) (hs : q.2 = 0) (c d l : ℝ × ℝ) :
      D (angular c) (tensor r s (A 1) (angular d) (angular l)) q = 0 :=
    angular_const v hq hs c (fun _ hq hs => first_slice v hq hs t ht d l)
  have hS : second (tensor r s (A 1)) U V y = 0 := by
    unfold second
    rw [angular_const v hy hz a (C := 0) (by intros q hq hs; rw [row q hq hs,row q hq hs]; norm_num),
      angular_const v hy hz b (C := 0) (by intros q hq hs; rw [row q hq hs]; norm_num),sub_zero]
  rwa [hS] at h


private theorem angular_congr (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2 = 0) (a : ℝ × ℝ) {f k : Params → ℝ} (df : DifferentiableAt ℝ f y)
    (dk : DifferentiableAt ℝ k y) (agree : ∀ q ∈ (coreChart v).target, q.2 = 0 → f q = k q) :
    D (angular a) f y = D (angular a) k y := by
  have z := angular_const v hy hz a (f := f-k) (C := 0) (fun q hq hs => sub_eq_zero.mpr (agree q hq hs))
  rw [D,fderiv_sub df dk,sub_apply] at z
  exact sub_eq_zero.mp z

private theorem D_scale (d y : Params) {f : Params → ℝ} (df : DifferentiableAt ℝ f y) (c : ℝ) :
    D d (fun z => c*f z) y = c*D d f y := by
  change fderiv ℝ (c • f) y d = _
  rw [fderiv_const_smul df]
  rfl

/-- Full cubic response on the common-normal tori. The two coordinate
directions are the simultaneous and opposite longitude rotations. -/
theorem flat_torus_cubic (v : FlatLocus.Representative) {y : Params} (hy : y ∈ (coreChart v).target)
    (hz : y.2 = 0) (t : ℝ) (ht : 0 ≤ t) (φ : Scalar) :
    let r := (axesBasis _ _ v.property.1).repr.symm
    let s := (axesBasis _ _ v.property.2).repr.symm
    let p := (chart r s).symm y
    let A : Params := ((1,0),0)
    let B : Params := ((0,1),0)
    let U := field r s A p
    let V := field r s B p
    let pull := φ ∘ (chart r s).symm
    ∀ (N₁ N₂ : Tangent p) (z : Fin 4 → ℝ),
      graphCoefficient (paperCoefficients t ht φ) U V N₁ N₂ 3 z -
        graphCoefficient (paperCoefficients t ht 0) U V N₁ N₂ 3 z =
        -(Profiles.hh t * D A (D A pull) y + D B (D B pull) y) := by
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let p := (coreChart v).symm y
  let A := angular (1,0)
  let B := angular (0,1)
  let U := field r s A p
  let V := field r s B p
  let pull := φ ∘ (coreChart v).symm
  let C := tensor r s (thirdOrderTensor t ht φ)
  let H := Profiles.hh t
  have pos : H ≠ 0 := (Profiles.hh_pos ht).ne'
  have pull_reg {q : Params} (hq : q ∈ (coreChart v).target) : ContDiffAt ℝ ∞ pull q :=
    contMDiffAt_iff_contDiffAt.mp (φ.contMDiff.contMDiffAt.comp _ (inv_smooth r s hq))
  have sr {q : Params} (hq : q ∈ (coreChart v).target) (c d : Params) : ContDiffAt ℝ ∞ (C c d) q :=
    tensor_smooth r s _ _ _ hq
  have Dsmooth {f : Params → ℝ} {q : Params} (h : ContDiffAt ℝ ∞ f q) (d : Params) :
      ContDiffAt ℝ ∞ (D d f) q := (h.fderiv_right (by simp : ∞+1 ≤ ∞)).clm_apply contDiffAt_const
  have cov (c d q : Params) : C c d q = 2*H*pull q * gram v (backgroundMetric t ht) c d q := rfl
  have entries {q : Params} (hq : q ∈ (coreChart v).target) (hs : q.2=0) :
      C A A q = 2*pull q ∧ C B B q = (2*H)*pull q ∧ C B A q = 0 := by
    rw [cov,cov,cov,mixed_slice v hq hs t ht (1,0) A,mixed_slice v hq hs t ht (0,1) B,
      mixed_slice v hq hs t ht (0,1) A]
    dsimp [A,B,angular,H]
    have ne := (Profiles.hh_pos ht).ne'
    constructor
    · field_simp [ne]; unfold Profiles.hh; ring
    constructor <;> ring
  have first {q : Params} (hq : q ∈ (coreChart v).target) (hs : q.2=0) :
      D B (C B A) q = 0 ∧ D A (C B B) q = (2*H)*D A pull q ∧ D B (C A A) q = 2*D B pull q := by
    have f (d : ℝ × ℝ) (x w : Params) (c : ℝ)
        (h : ∀ z ∈ (coreChart v).target, z.2=0 → C x w z = c*pull z) :
        D (angular d) (C x w) q = c*D (angular d) pull q := by
      have dr := (pull_reg hq).differentiableAt (by simp)
      exact (angular_congr v hq hs d ((sr hq x w).differentiableAt (by simp)) (dr.const_mul c) h).trans
        (D_scale _ _ dr c)
    exact ⟨angular_const v hq hs (0,1) (fun z hz h => (entries hz h).2.2),
      f (1,0) B B (2*H) (fun z hz h => (entries hz h).2.1),f (0,1) A A 2 (fun z hz h => (entries hz h).1)⟩
  have sr' (d c w : Params) := Dsmooth (sr hy c w) d
  have ds (d : Params) := Dsmooth (pull_reg hy) d
  have sx : D A (fun q => D B (C B A) q-D A (C B B) q/2) y = (-H)*D A (D A pull) y := by
    apply (angular_congr v hy hz (1,0) ((sr' B B A).sub ((sr' A B B).div_const 2) |>.differentiableAt (by simp))
      (((ds A).differentiableAt (by simp)).const_mul (-H)) (k := fun q => (-H)*D A pull q) ?_).trans
      (D_scale _ _ ((ds A).differentiableAt (by simp)) _)
    intro q hq hs; rw [(first hq hs).1,(first hq hs).2.1]; ring
  have sy : D B (fun q => D B (C A A) q/2) y = D B (D B pull) y := by
    apply angular_congr v hy hz (0,1) (((sr' B A A).div_const 2).differentiableAt (by simp))
      ((ds B).differentiableAt (by simp))
    intro q hq hs; rw [(first hq hs).2.2]; ring
  dsimp only
  intro N₁ N₂ z
  change graphCoefficient _ U V N₁ N₂ 3 z - graphCoefficient _ U V N₁ N₂ 3 z = _
  refine (graph_cubic_pencil t ht φ U V N₁ N₂ z).trans ?_
  have res := angular_variation v hy hz t ht (conformalPencil t ht φ) rfl (conformalPencil_realized t ht φ) (1,0) (0,1)
  change HasDerivAt ((TangentPair.mk p U V).numerator (conformalPencil t ht φ)) (second C A B y) 0 at res
  rw [res.deriv,second,sx,sy]
  change -H * D A (D A pull) y - D B (D B pull) y = -(H * D A (D A pull) y + D B (D B pull) y)
  ring

private def pole : FlatLocus.UnitVector := ⟨Pi.single 2 1,by simp⟩
private def equatorial (s : ℝ) := unitSphere.symm (equatorPoint s)

private theorem eq_perp (s : ℝ) : pole.val ⬝ᵥ (equatorial s).val = 0 := by
  change Pi.single 2 (1:ℝ) ⬝ᵥ ![cos s,sin s,0] = 0
  simp [single_dotProduct]

/-- An equatorial incidence representative at longitudes m+d and m-d. -/
def equatorCore (m d : ℝ) : FlatLocus.Representative :=
  ⟨(pole,equatorial (m+d),equatorial (m-d)),eq_perp _,eq_perp _⟩

private theorem eq_rotate (s a : ℝ) :
    sphereAction (align pole (equatorial s) (eq_perp s)) (LongitudeHeight.point (a,0)) = equatorPoint (s+a) := by
  apply Subtype.ext; apply (WithLp.equiv 2 _).injective
  change (align pole (equatorial s) (eq_perp s) (WithLp.toLp 2 (LongitudeHeight.point (a,0)).val.ofLp)).ofLp =
    ![cos (s+a),sin (s+a),0]
  rw [align_apply]
  change (cos (arcsin 0)*cos a) • (![cos s,sin s,0] : R3) +
    (cos (arcsin 0)*sin a) • ((Pi.single 2 (1:ℝ)) ⨯₃ ![cos s,sin s,0]) +
    sin (arcsin 0) • _ = _
  ext i
  fin_cases i <;> simp [cos_add,sin_add,cross_apply] <;> ring

private theorem equator_core_point (m d x z : ℝ) :
    (coreChart (equatorCore m d)).symm ((x,z),0) =
      (equatorPoint ((m+x)+(d-z)),equatorPoint ((m+x)-(d-z))) := by
  rw [coreChart,chart_inv_apply]
  change (sphereAction _ (LongitudeHeight.point (x-z,0)),sphereAction _ (LongitudeHeight.point (x+z,0))) = _
  exact Prod.ext ((eq_rotate (m+d) (x-z)).trans (congrArg equatorPoint (by ring)))
    ((eq_rotate (m-d) (x+z)).trans (congrArg equatorPoint (by ring)))

theorem along_axis (v : FlatLocus.Representative) (f : Params → ℝ) (d : Params)
    (reg : ∀ q ∈ (coreChart v).target, ContDiffAt ℝ ∞ f q) (h0 : (0:Params) ∈ (coreChart v).target) :
    D d (D d f) 0 = iteratedDeriv 2 (fun h : ℝ => f (h • d)) 0 := by
  have path (s : ℝ) : HasDerivAt (fun h : ℝ => h • d) d s := by simpa using (hasDerivAt_id' s).smul_const d
  have eq : deriv (fun h : ℝ => f (h • d)) =ᶠ[𝓝 0] fun h => D d f (h • d) := by
    filter_upwards [ray_target v h0 d] with h hh
    have hq : h • d ∈ (coreChart v).target := by simpa [ray] using hh
    exact (((reg _ hq).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt h (path h)).deriv
  have df : ContDiffAt ℝ ∞ (D d f) 0 :=
    ((reg _ h0).fderiv_right (by simp : ∞+1 ≤ ∞)).clm_apply contDiffAt_const
  rw [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,eq.deriv_eq]
  exact (((df.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) (path 0) (by simp)).deriv).symm

/-- The correction constructed for the certified forcing contributes precisely
μ minus that forcing to the intrinsic moving-plane cubic at every equatorial
separation. Only the value of the uncorrected moving minimum still needs to be
identified with the forcing. -/
theorem corrected_equator_increment (t : ℝ) (ht : 0 ≤ t) :
    ∃ φ : Scalar, ∀ m d : ℝ,
      let v := equatorCore m d
      let r := (axesBasis _ _ v.property.1).repr.symm
      let s := (axesBasis _ _ v.property.2).repr.symm
      let p := (chart r s).symm 0
      let U := field r s ((1,0),0) p
      let V := field r s ((0,1),0) p
      ∀ (N₁ N₂ : Tangent p) (z : Fin 4 → ℝ),
        EquatorJet.forcing t (m+d,m-d) + (graphCoefficient (paperCoefficients t ht φ) U V N₁ N₂ 3 z -
          graphCoefficient (paperCoefficients t ht 0) U V N₁ N₂ 3 z) = Profiles.mu t := by
  obtain ⟨φ,_,cor,_⟩ := EquatorJet.corrected_forcing t ht
  refine ⟨φ,?_⟩
  intro m d
  let v := equatorCore m d
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let A := angular (1,0)
  let B := angular (0,1)
  let pull := φ ∘ (coreChart v).symm
  let f := fun (x z : ℝ) => φ (equatorPoint (x+z),equatorPoint (x-z))
  have reg (q : Params) (hq : q ∈ (coreChart v).target) : ContDiffAt ℝ ∞ pull q :=
    contMDiffAt_iff_contDiffAt.mp (φ.contMDiff.contMDiffAt.comp _ (inv_smooth r s hq))
  have h0 : (0:Params) ∈ (coreChart v).target := (center v).1
  have dx : (fun h : ℝ => pull (h • A)) = fun h => f (m+h) d := by
    funext h
    have eq : h • A = ((h,0),0) := by simp [A,angular]
    simp only [eq,pull,Function.comp_apply,v,equator_core_point,sub_zero,f]
  have dy : (fun h : ℝ => pull (h • B)) = fun h => f m (d-h) := by
    funext h
    have eq : h • B = ((0,h),0) := by simp [B,angular]
    simp only [eq,pull,Function.comp_apply,v,equator_core_point,add_zero,f]
  have xx := along_axis v pull A reg h0
  rw [dx,iteratedDeriv_comp_const_add 2 (fun x => f x d) m] at xx
  simp only [add_zero] at xx
  have yy := along_axis v pull B reg h0
  rw [dy,iteratedDeriv_comp_const_sub 2 (f m) d] at yy
  simp only [sub_zero,neg_one_sq,one_smul] at yy
  have h := cor m d
  dsimp only at h
  rw [equator_conformal_second t ht φ m d] at h
  dsimp only
  intro N₁ N₂ z
  refine (congrArg (EquatorJet.forcing t (m+d,m-d) + ·) (flat_torus_cubic v h0 rfl t ht φ N₁ N₂ z)).trans ?_
  change EquatorJet.forcing t (m+d,m-d) + -(Profiles.hh t * D A (D A pull) 0 + D B (D B pull) 0) = _
  rw [xx,yy]
  simpa [f] using h



/-- Longitudinal contribution of a weighted square of a lowered simultaneous rotation.
The aa and bb channels use the x and y axes respectively. -/
theorem flat_profile_second (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t)
    (i : Fin 3) (f : Scalar) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let k := rotationFlat t ht false (axis i)
    let H := (symmetricProduct k k).weight f f.contMDiff
    let A : Params := ((1,0),0)
    let B : Params := ((0,1),0)
    second (tensor r s H) A B 0 =
      -((v.val.1.val i/Profiles.hh t)^2/2) * iteratedDeriv 2 (fun h : ℝ => f ((coreChart v).symm (h • B))) 0 := by
  intro r s k H A B
  let C := tensor r s H
  let pull := f ∘ (coreChart v).symm
  let c := (v.val.1.val i/Profiles.hh t)^2
  have h0 : (0:Params) ∈ (coreChart v).target := (center v).1
  have sm {q : Params} (hq : q ∈ (coreChart v).target) : ContDiffAt ℝ ∞ pull q :=
    contMDiffAt_iff_contDiffAt.mp (f.contMDiff.contMDiffAt.comp _ (inv_smooth r s hq))
  have smC {q : Params} (hq : q ∈ (coreChart v).target) (a b : Params) : ContDiffAt ℝ ∞ (C a b) q :=
    tensor_smooth r s H a b hq
  have Dsm {g : Params → ℝ} {q : Params} (hg : ContDiffAt ℝ ∞ g q) (d : Params) :
      ContDiffAt ℝ ∞ (D d g) q := (hg.fderiv_right (by simp : ∞+1≤∞)).clm_apply contDiffAt_const
  have entries (q : Params) (hq : q ∈ (coreChart v).target) (hz : q.2=0) :
      C A A q = c*pull q ∧ C B A q=0 ∧ C B B q=0 := by
    let p := (coreChart v).symm q
    let n := v.val.1.val
    have np : n ⬝ᵥ point₁ p = 0 := (coord_height _ _ v.property.1 _ _ hq.2.1.1.2).trans (congrArg Prod.fst hz)
    have nq : n ⬝ᵥ point₂ p = 0 := (coord_height _ _ v.property.2 _ _ hq.2.2.1.2).trans (congrArg Prod.snd hz)
    have rot := rotationFlat_longitude t ht p n np nq (axis i)
    have a : k p (ambientVelocityL p (field r s A p)) = n i/Profiles.hh t := by
      change k p (ambientVelocityL p (field r s (angular (1,0)) p)) = _
      rw [slice_velocity v hq]; simp only [one_smul,zero_smul,sub_zero]
      exact rot.1.trans (by change ((Pi.single i (1:ℝ)) ⬝ᵥ n)/_ = _; rw [single_dotProduct,one_mul])
    have b : k p (ambientVelocityL p (field r s B p))=0 := by
      change k p (ambientVelocityL p (field r s (angular (0,1)) p)) = _
      rw [slice_velocity v hq]; simp only [one_smul,zero_smul,zero_sub,map_neg]
      exact neg_eq_zero.mpr rot.2.1
    let V (d : Params) := ambientVelocityL p (field r s d p)
    have val (u w : Params) : C u w q = f p * ((1/2:ℝ)*(k p (V u)*k p (V w)+k p (V u)*k p (V w))) := rfl
    change k p (V A)=_ at a
    change k p (V B)=_ at b
    rw [val,val,val,a,b]
    change _ = (n i/Profiles.hh t)^2*f p ∧ _=0 ∧ _=0
    exact ⟨by ring,by ring,by ring⟩
  have fst (q : Params) (hq : q ∈ (coreChart v).target) (hz : q.2=0) :
      D B (C B A) q=0 ∧ D A (C B B) q=0 ∧ D B (C A A) q=c*D B pull q := by
    refine ⟨angular_const v hq hz (0,1) (fun z h1 h2 => (entries z h1 h2).2.1),
      angular_const v hq hz (1,0) (fun z h1 h2 => (entries z h1 h2).2.2),?_⟩
    have df := (sm hq).differentiableAt (by simp)
    exact (angular_congr v hq hz (0,1) ((smC hq A A).differentiableAt (by simp)) (df.const_mul c)
      (fun z h1 h2 => (entries z h1 h2).1)).trans (D_scale _ _ df c)
  have x : D A (fun q => D B (C B A) q - D A (C B B) q/2) 0 = 0 := by
    apply angular_const v h0 rfl (1,0)
    intro q hq hz; rw [(fst q hq hz).1,(fst q hq hz).2.1]
  have y : D B (fun q => D B (C A A) q/2) 0 = c/2*D B (D B pull) 0 := by
    have df := (Dsm (sm h0) B).differentiableAt (by simp)
    refine (angular_congr v h0 rfl (0,1) (((Dsm (smC h0 A A) B).div_const 2).differentiableAt (by simp))
      (df.const_mul (c/2)) (k := fun q => c/2*D B pull q) ?_).trans (D_scale _ _ df _)
    intro q hq hz; rw [(fst q hq hz).2.2]; ring
  change D A _ 0-D B _ 0 = _
  rw [x,y,along_axis v pull B (fun _ => sm) h0]
  dsimp only [c,pull, Function.comp_apply]
  ring

end
end LocalHopf.SphereProduct.JetChart
