import LocalHopf.EquatorExtension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! Smooth longitude-height coordinates on the actual round sphere, as used by the jet calculation. -/
namespace LocalHopf.SphereProduct.LongitudeHeight
open Real Set Filter Matrix
open scoped Topology Manifold ContDiff
noncomputable section

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

private def angles (q : ℝ × ℝ) : Sphere :=
  unitSphere ⟨![cos q.2*cos q.1, cos q.2*sin q.1, sin q.2], by
    change (![_,_,_] : R3) ⬝ᵥ ![_,_,_] = 1
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, ← sq]
    change (cos q.2*cos q.1)^2+(cos q.2*sin q.1)^2+(sin q.2)^2=1
    linear_combination cos q.2^2*(cos_sq_add_sin_sq q.1) + cos_sq_add_sin_sq q.2⟩

def point (q : ℝ × ℝ) : Sphere := angles (q.1, arcsin q.2)

def coords (p : Sphere) : ℝ × ℝ := ((longitude p.val.ofLp).arg, p.val.ofLp 2)

def source : Set Sphere := {p | 0 < p.val.ofLp 0}
def target : Set (ℝ × ℝ) := {q | |q.1| < π/2 ∧ |q.2| < 1}

private theorem height_sq (p : Sphere) : (p.val.ofLp 0)^2+(p.val.ofLp 1)^2+(p.val.ofLp 2)^2=1 := by
  have h := (unitSphere.symm p).property
  change p.val.ofLp ⬝ᵥ p.val.ofLp = 1 at h
  simpa [dotProduct, Fin.sum_univ_three, ← sq, add_assoc] using h

private theorem height_lt {p : Sphere} (hp : p ∈ source) : |p.val.ofLp 2| < 1 := by
  change 0 < p.val.ofLp 0 at hp
  apply abs_lt.mpr
  constructor <;> nlinarith [height_sq p, sq_pos_of_pos hp, sq_nonneg (p.val.ofLp 1),
    sq_nonneg (p.val.ofLp 2-1), sq_nonneg (p.val.ofLp 2+1)]

private theorem radial_pos {z : ℝ} (hz : |z| < 1) : 0 < cos (arcsin z) :=
  cos_pos_of_mem_Ioo ⟨neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp hz).1,
    arcsin_lt_pi_div_two.mpr (abs_lt.mp hz).2⟩

theorem coords_point {q : ℝ × ℝ} (hq : q ∈ target) : coords (point q) = q := by
  obtain ⟨ha,hz⟩ := hq
  have e : longitude (point q).val.ofLp = (cos (arcsin q.2) : ℂ) *
      (cos q.1 + sin q.1 * Complex.I) := by
    apply Complex.ext <;> simp [point, angles, unitSphere, longitude, -Complex.ofReal_sin, -Complex.ofReal_cos]
  apply Prod.ext
  · change (longitude _).arg = q.1
    rw [e]
    have harg : q.1 ∈ Ioc (-π) π := ⟨by linarith [(abs_lt.mp ha).1, pi_pos], by linarith [(abs_lt.mp ha).2, pi_pos]⟩
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using Complex.arg_mul_cos_add_sin_mul_I (radial_pos hz) harg
  · exact sin_arcsin (abs_lt.mp hz).1.le (abs_lt.mp hz).2.le

theorem point_coords {p : Sphere} (hp : p ∈ source) : point (coords p) = p := by
  let z := longitude p.val.ofLp
  have hz := height_lt hp
  have hnorm : cos (arcsin (p.val.ofLp 2)) = ‖z‖ := by
    have h := Complex.sq_norm z
    change ‖z‖^2 = (p.val.ofLp 0)*(p.val.ofLp 0)+(p.val.ofLp 1)*(p.val.ofLp 1) at h
    apply (sq_eq_sq₀ (radial_pos hz).le (norm_nonneg z)).mp
    rw [cos_arcsin, Real.sq_sqrt (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).2 hz.le)), h]
    nlinarith [height_sq p]
  apply unitSphere.symm.injective
  apply Subtype.ext
  change ![cos (arcsin (p.val.ofLp 2))*cos z.arg,cos (arcsin (p.val.ofLp 2))*sin z.arg,
    sin (arcsin (p.val.ofLp 2))] = p.val.ofLp
  rw [hnorm, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg,
    sin_arcsin (abs_lt.mp hz).1.le (abs_lt.mp hz).2.le]
  funext i
  fin_cases i <;> rfl

private theorem smooth_angles : ContMDiff 𝓘(ℝ,ℝ × ℝ) (𝓡 2) ∞ angles := by
  let f (q : ℝ × ℝ) : R3 := ![cos q.2*cos q.1, cos q.2*sin q.1, sin q.2]
  have hf : ContDiff ℝ ∞ f := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [f] <;> fun_prop
  exact (PiLp.contDiff_toLp.comp hf).contMDiff.codRestrict_sphere (fun q => (angles q).property)

theorem point_smooth {q : ℝ × ℝ} (hz : |q.2| < 1) : ContMDiffAt 𝓘(ℝ,ℝ × ℝ) (𝓡 2) ∞ point q := by
  have h := contDiffAt_arcsin (ne_of_gt (abs_lt.mp hz).1) (ne_of_lt (abs_lt.mp hz).2) (n := ∞)
  exact smooth_angles.contMDiffAt.comp q (contDiffAt_fst.prodMk (h.comp q contDiffAt_snd)).contMDiffAt

private theorem raw_smooth : ContMDiff (𝓡 2) 𝓘(ℝ,R3) ∞ (fun p : Sphere => p.val.ofLp) :=
  PiLp.contDiff_ofLp.contMDiff.comp contMDiff_coe_sphere

theorem coords_smooth {p : Sphere} (hp : p ∈ source) : ContMDiffAt (𝓡 2) 𝓘(ℝ,ℝ × ℝ) ∞ coords p := by
  let z (p : Sphere) := longitude p.val.ofLp
  have f (i : Fin 3) : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun q : Sphere => q.val.ofLp i) :=
    (ContinuousLinearMap.proj i : R3 →L[ℝ] ℝ).contDiff.contMDiff.comp raw_smooth
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ,ℂ) ∞ z := by
    have he : z = fun q : Sphere => (q.val.ofLp 0 : ℂ) + (q.val.ofLp 1 : ℂ)*Complex.I :=
      funext fun _ => Complex.mk_eq_add_mul_I ..
    rw [he]
    have sm : ContDiff ℝ ∞ (fun y : ℝ × ℝ => (y.1 : ℂ)+(y.2 : ℂ)*Complex.I) :=
      (Complex.ofRealCLM.contDiff.comp contDiff_fst).add ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
    exact sm.contMDiff.comp ((f 0).prodMk_space (f 1))
  have hlog := (Complex.contDiffAt_log (n := ∞) (x := z p) (Or.inl hp)).restrict_scalars ℝ
  change ContMDiffAt (𝓡 2) 𝓘(ℝ,ℝ × ℝ) ∞ (fun x => ((z x).arg,x.val.ofLp 2)) p
  simpa only [Function.comp_apply, Complex.imCLM_apply, Complex.log_im] using ((Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp _ (hlog.contMDiffAt.comp p hc.contMDiffAt))).prodMk_space
    (f 2).contMDiffAt

/-- The inverses and both smoothness assertions hold on these open sets. -/
def chart : OpenPartialHomeomorph Sphere (ℝ × ℝ) where
  toFun := coords
  invFun := point
  source := source
  target := target
  map_source' _ hp := ⟨Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hp), height_lt hp⟩
  map_target' _ hq := mul_pos (radial_pos hq.2) (cos_pos_of_mem_Ioo (abs_lt.mp hq.1))
  left_inv' _ := point_coords
  right_inv' _ := coords_point
  open_source := isOpen_lt continuous_const (((continuous_apply 0).comp raw_smooth.continuous))
  open_target := (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  continuousOn_toFun _ hp := (coords_smooth hp).continuousAt.continuousWithinAt
  continuousOn_invFun _ hq := (point_smooth hq.2).continuousAt.continuousWithinAt


private def radial (z : ℝ) := sqrt (1-z^2)
def lonVector (a z : ℝ) : R3 := ![-radial z*sin a,radial z*cos a,0]
def heightVector (a z : ℝ) : R3 := ![-(z/radial z)*cos a,-(z/radial z)*sin a,1]

private theorem radial_sq {z : ℝ} (hz : |z| < 1) : radial z ^ 2 = 1-z^2 :=
  sq_sqrt (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).2 hz.le))

private theorem radial_ne {z : ℝ} (hz : |z| < 1) : radial z ≠ 0 := by
  rw [radial, ← cos_arcsin]
  exact (radial_pos hz).ne'

private theorem point_raw (a z : ℝ) (hz : |z| < 1) :
    (point (a,z)).val.ofLp = ![radial z*cos a,radial z*sin a,z] := by
  change ![cos (arcsin z)*cos a,cos (arcsin z)*sin a,sin (arcsin z)] = _
  rw [cos_arcsin,sin_arcsin (abs_lt.mp hz).1.le (abs_lt.mp hz).2.le]
  rfl

/-- The coordinate velocities are derivatives of the actual sphere chart. -/
theorem coordinate_velocities (a z : ℝ) (hz : |z| < 1) :
    HasDerivAt (fun x => (point (x,z)).val.ofLp) (lonVector a z) a ∧
    HasDerivAt (fun y => (point (a,y)).val.ofLp) (heightVector a z) z := by
  have dr : HasDerivAt radial (-(z/radial z)) z := by
    have h := (((hasDerivAt_id' z).pow 2).const_sub 1).sqrt (by
      dsimp
      have p := (radial_pos hz)
      rw [cos_arcsin, sqrt_pos] at p
      exact p.ne')
    apply h.congr_deriv
    dsimp [radial]
    field_simp [radial, radial_ne hz]
  constructor
  · simp_rw [point_raw _ _ hz]
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [lonVector] using (hasDerivAt_cos a).const_mul (radial z)
    · exact (hasDerivAt_sin a).const_mul (radial z)
    · exact hasDerivAt_const a z
  · apply HasDerivAt.congr_of_eventuallyEq (f := fun y => ![radial y*cos a,radial y*sin a,y])
    · apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · exact dr.mul_const _
      · exact dr.mul_const _
      · exact hasDerivAt_id' _
    · filter_upwards [continuous_abs.continuousAt.eventually_lt_const hz] with y hy using point_raw a y hy


theorem raw_differentiable {q : ℝ × ℝ} (hz : |q.2| < 1) :
    DifferentiableAt ℝ (fun y => (point y).val.ofLp) q :=
  (contMDiffAt_iff_contDiffAt.mp (raw_smooth.contMDiffAt.comp q (point_smooth hz))).differentiableAt (by simp)

/-- Both columns of the differential in ambient Euclidean coordinates. -/
theorem point_fderiv (a z : ℝ) (hz : |z| < 1) (v : ℝ × ℝ) :
    fderiv ℝ (fun q => (point q).val.ofLp) (a,z) v =
      v.1 • lonVector a z + v.2 • heightVector a z := by
  let f (q : ℝ × ℝ) := (point q).val.ofLp
  let j := fderiv ℝ f (a,z)
  have h : HasFDerivAt f j (a,z) := (raw_differentiable hz).hasFDerivAt
  have c := coordinate_velocities a z hz
  have c₁ : j (1,0) = lonVector a z := (HasFDerivAt.comp_hasDerivAt (l := f) a h
    ((hasDerivAt_id' a).prodMk (hasDerivAt_const a z))).unique c.1
  have c₂ : j (0,1) = heightVector a z := (HasFDerivAt.comp_hasDerivAt (l := f) z h
    ((hasDerivAt_const z a).prodMk (hasDerivAt_id' z))).unique c.2
  change j v = _
  rw [← c₁, ← c₂, ← j.map_smul, ← j.map_smul, ← j.map_add]
  congr 1
  ext <;> simp


/-- Round covariant longitude/height block; its inverse is used in the cometric. -/
theorem round_gram (a z : ℝ) (hz : |z| < 1) :
    lonVector a z ⬝ᵥ lonVector a z = 1-z^2 ∧ lonVector a z ⬝ᵥ heightVector a z = 0 ∧
    heightVector a z ⬝ᵥ heightVector a z = 1/(1-z^2) := by
  rw [← radial_sq hz]
  simp [lonVector,heightVector,dotProduct,Fin.sum_univ_three]
  refine ⟨?_, by ring, ?_⟩
  · linear_combination (radial z)^2 * (sin_sq_add_cos_sq a)
  · field_simp [radial_ne hz]
    linear_combination (z^2)*(sin_sq_add_cos_sq a) + radial_sq hz

/-- Exact contravariant components of the sphere Killing field in the verifier's
longitude-height chart, before its spatial Taylor truncation. -/
theorem rotation_components (w : R3) (a z : ℝ) (hz : |z| < 1) :
    w ⨯₃ (point (a,z)).val.ofLp =
      (w 2 - z/radial z*(cos a*w 0+sin a*w 1)) • lonVector a z +
      (radial z*(sin a*w 0-cos a*w 1)) • heightVector a z := by
  rw [point_raw _ _ hz]
  funext i
  fin_cases i <;> simp [crossProduct,lonVector,heightVector]
  all_goals field_simp [radial_ne hz]
  all_goals ring_nf
  all_goals rw [show sin a^2 = 1-cos a^2 by linarith [sin_sq_add_cos_sq a]]
  all_goals ring


end
end LocalHopf.SphereProduct.LongitudeHeight
