import LocalHopf.GraphCoefficients
import LocalHopf.NormalEquation
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! # The minimizing four-coordinate graph tilt

Centered finite differences of the quadratic coefficient give its exact gradient
and Hessian. Background growth proves that the matrix being inverted is a unit.
-/
namespace LocalHopf.SphereProduct
open Matrix Polynomial Set Metric Filter LocalHopf.UniformTube
open scoped Topology ContDiff
noncomputable section

private abbrev V4 := Fin 4 → ℝ

/-- Exact gradient of a quadratic in the four graph coordinates. -/
def tiltGradient (Q : V4 → ℝ) (a : V4) (i : Fin 4) : ℝ :=
  (Q (a + Pi.single i 1) - Q (a - Pi.single i 1))/2

/-- The four-by-four normal Hessian obtained from the quadratic coefficient alone. -/
def tiltHessian (Q : (Fin 4 → ℝ) → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => tiltGradient Q (Pi.single j 1) i - tiltGradient Q 0 i

/-- The solution of the script's four-coordinate linear system. -/
def stationaryTilt (Q : (Fin 4 → ℝ) → ℝ) : Fin 4 → ℝ :=
  (tiltHessian Q)⁻¹ *ᵥ (-tiltGradient Q 0)

private abbrev Domain := ℝ × V4 × ℝ

private def normalDir : V4 →ₗ[ℝ] Domain where
  toFun v := (0,v,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private def hessianMap (H : Domain →L[ℝ] Domain →L[ℝ] ℝ) : V4 →ₗ[ℝ] V4 where
  toFun a i := H (normalDir a) (normalDir (Pi.single i 1))
  map_add' a b := by ext i; simp
  map_smul' r a := by ext i; simp

private theorem gradient_eq (F : Domain → ℝ) (hf : ContDiffAt ℝ 2 F (0,0,0)) (a : V4) (i : Fin 4) :
    tiltGradient (coeff F 2 0) a i = fderiv ℝ (fderiv ℝ F) (0,0,0) (0,a,1) (normalDir (Pi.single i 1)) := by
  have e₁ := quadratic_line F hf a (Pi.single i 1) 1
  have e₂ := quadratic_line F hf a (Pi.single i 1) (-1)
  simp only [one_smul,neg_smul,one_pow,one_mul,neg_mul,neg_one_sq,← sub_eq_add_neg] at e₁ e₂
  unfold tiltGradient
  change _ = fderiv ℝ (fderiv ℝ F) (0,0,0) (0,a,1) (0,Pi.single i 1,0)
  linarith only [e₁,e₂]

private theorem gradient_affine (F : Domain → ℝ) (hf : ContDiffAt ℝ 2 F (0,0,0)) (a : V4) :
    let H := fderiv ℝ (fderiv ℝ F) (0,0,0)
    tiltGradient (coeff F 2 0) a = hessianMap H a + tiltGradient (coeff F 2 0) 0 := by
  intro H
  ext i
  rw [Pi.add_apply,gradient_eq F hf,gradient_eq F hf]
  change H (0,a,1) _ = H (normalDir a) _ + H (0,0,1) _
  rw [show ((0,a,1) : Domain) = normalDir a + (0,0,1) by simp [normalDir],map_add]
  rfl

private theorem matrix_eq (F : Domain → ℝ) (hf : ContDiffAt ℝ 2 F (0,0,0)) :
    tiltHessian (coeff F 2 0) = LinearMap.toMatrix' (hessianMap (fderiv ℝ (fderiv ℝ F) (0,0,0))) := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change tiltGradient _ _ _ - tiltGradient _ _ _ = _
  rw [gradient_affine F hf (Pi.single j 1),Pi.add_apply,add_sub_cancel_right]

private theorem matrix_nonsingular (F : Domain → ℝ) (hf : ContDiffAt ℝ 2 F (0,0,0)) {δ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hflat : F (0,0,0) = 0)
    (growth : ∀ v, ‖v‖ ≤ δ → lam*‖v‖^2 ≤ F (0,v,0)) : IsUnit (tiltHessian (coeff F 2 0)).det := by
  let H := fderiv ℝ (fderiv ℝ F) (0,0,0)
  rw [matrix_eq F hf]
  rw [← Matrix.isUnit_iff_isUnit_det]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  have hinj : Function.Injective (hessianMap H) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    have vanish : ((H (normalDir a)).toLinearMap.comp normalDir) = 0 := by
      apply (Pi.basisFun ℝ (Fin 4)).ext
      intro i
      simpa [H,hessianMap] using congrFun ha i
    have h := LinearMap.congr_fun vanish a
    change H (normalDir a) (normalDir a) = 0 at h
    have lower := normal_second_lower F hδ hf hflat growth a
    change 2*lam*‖a‖^2 ≤ H (normalDir a) (normalDir a) at lower
    by_contra ne
    nlinarith only [h,lower,mul_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr ne))]
  intro a b h
  exact hinj (by simpa only [LinearMap.toMatrix'_mulVec] using h)

theorem stationaryTilt_of_minimum (F : Domain → ℝ) (hf : ContDiffAt ℝ 2 F (0,0,0)) (a : V4)
    (hm : ∀ z, coeff F 2 0 a ≤ coeff F 2 0 z) (hd : IsUnit (tiltHessian (coeff F 2 0)).det) :
    stationaryTilt (coeff F 2 0) = a := by
  have normeq := normalEquation_of_minimum F hf hm
  have ha : tiltGradient (coeff F 2 0) a = 0 := funext fun i =>
    (gradient_eq F hf a i).trans (normeq (Pi.single i 1))
  let Q := coeff F 2 0
  have eq : tiltHessian Q *ᵥ a = -tiltGradient Q 0 := by
    rw [matrix_eq F hf,LinearMap.toMatrix'_mulVec]
    exact eq_neg_of_add_eq_zero_left ((gradient_affine F hf a).symm.trans ha)
  unfold stationaryTilt
  change (tiltHessian Q)⁻¹ *ᵥ (-tiltGradient Q 0) = a
  rw [← eq,mulVec_mulVec,nonsing_inv_mul _ hd,one_mulVec]

/-- Polarization extracts the normal Hessian from the background alone. -/
theorem tiltHessian_background (F : Domain → ℝ) (hf : ContDiffAt ℝ 2 F (0,0,0)) (i j : Fin 4) :
    let d (z : V4) := iteratedDeriv 2 (fun s : ℝ => F (0,s • z,0)) 0
    let u := Pi.single i (1:ℝ)
    let v := Pi.single j (1:ℝ)
    tiltHessian (coeff F 2 0) i j = (d (u+v)-d u-d v)/2 := by
  intro d u v
  let H := fderiv ℝ (fderiv ℝ F) (0,0,0)
  have twice (z : V4) : d z = H (normalDir z) (normalDir z) := by
    let γ (s : ℝ) : Domain := (0,s • z,0)
    have zero : γ 0 = (0,0,0) := by simp [γ]
    have vel (s : ℝ) : HasDerivAt γ (normalDir z) s := (hasDerivAt_const s (0:ℝ)).prodMk
      ((show HasDerivAt (fun h : ℝ => h • z) z s by simpa using (hasDerivAt_id' s).smul_const z).prodMk (hasDerivAt_const s (0:ℝ)))
    have acc : iteratedDeriv 2 γ 0=0 := by
      rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,show deriv γ=(fun _ => normalDir z) from funext (fun s => (vel s).deriv),deriv_const]
    have sm : ContDiffAt ℝ 2 γ 0 := by unfold γ; fun_prop
    change iteratedDeriv 2 (F ∘ γ) 0=_
    rw [iteratedDeriv_vcomp_two (zero ▸ hf) sm,iteratedFDeriv_two_apply,(vel 0).deriv,acc,map_zero,add_zero,zero]
  have ij : tiltHessian (coeff F 2 0) i j = H (normalDir v) (normalDir u) := by
    rw [matrix_eq F hf,LinearMap.toMatrix'_apply]; rfl
  have sym := hf.isSymmSndFDerivAt (by norm_num) (normalDir u) (normalDir v)
  rw [ij,twice,twice,twice,map_add,H.map_add,add_apply,map_add,map_add]
  change H (normalDir u) (normalDir v)=H (normalDir v) (normalDir u) at sym
  linarith only [sym]

/-- The minimized quadratic equals its constant term minus the Schur complement
used in the verifier. The finite-difference gradient is in the actual graph basis. -/
theorem quadratic_minimum_schur (F : Domain → ℝ) (hf : ContDiffAt ℝ 2 F (0,0,0)) (a : V4)
    (hm : ∀ z, coeff F 2 0 a ≤ coeff F 2 0 z) :
    coeff F 2 0 a = coeff F 2 0 0 + (tiltGradient (coeff F 2 0) 0 ⬝ᵥ a)/2 := by
  let H := fderiv ℝ (fderiv ℝ F) (0,0,0)
  let T : Domain := (0,0,1)
  let L := (H T).toLinearMap.comp normalDir
  have linear : tiltGradient (coeff F 2 0) 0 ⬝ᵥ a=L a := by
    have basis : (∑ i : Fin 4, (a i) • Pi.single i (1:ℝ)) = a := by ext i; simp [Pi.single_apply]
    calc
      _ = ∑ i : Fin 4, (a i) * L (Pi.single i (1:ℝ)) := by
        unfold dotProduct
        apply Finset.sum_congr rfl
        intro i _
        rw [gradient_eq F hf]
        change _ = a i * H T (normalDir (Pi.single i 1))
        rw [mul_comm]
      _ = L (∑ i : Fin 4, (a i) • Pi.single i (1:ℝ)) := by simp [map_sum]
      _ = _ := congrArg L basis
  have stat := normalEquation_of_minimum F hf hm a
  have hDir : ((0,a,1):Domain)=T+normalDir a := by simp [T,normalDir]
  change H (0,a,1) (normalDir a)=0 at stat
  rw [hDir,H.map_add,add_apply] at stat
  have line := quadratic_line F hf 0 a 1
  simp only [one_smul,zero_add,one_mul,one_pow] at line
  change coeff F 2 0 a = coeff F 2 0 0 + H T (normalDir a) + H (normalDir a) (normalDir a)/2 at line
  rw [linear]
  change _=coeff F 2 0 0 + H T (normalDir a)/2
  linarith only [line,stat]

/-- Finite quotient calculation of the order-`n` graph coefficient. -/
def graphCoefficient {p : Base} (A : Fin 4 → AmbientTensor) (U V N₁ N₂ : Tangent p)
    (n : ℕ) (v : Fin 4 → ℝ) : ℝ :=
  let N := affineNumeratorPolynomial A (U,v 0 • N₁+v 1 • N₂) (V,v 2 • N₁+v 3 • N₂)
  let D := (metricPolynomial A (coordinateFrame p)).det
  quotientCoeff (residual N D n) D

/-- A true minimum of the perturbed curvature numerator has quadratic and cubic
coefficients calculated at the explicit normal-equation solution. The proof
also certifies nonsingularity of the matrix used in that calculation. -/
theorem graph_minimum_coefficients (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) (p : Base)
    (U V N₁ N₂ : Tangent p) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 < lam) :
    let A := paperCoefficients t ht χ
    let F := graphNumerator A U V N₁ N₂
    let Q := graphCoefficient A U V N₁ N₂ 2
    let T := graphCoefficient A U V N₁ N₂ 3
    F (0,0,0) = 0 → (∀ z, ‖z‖ ≤ δ → lam*‖z‖^2 ≤ F (0,z,0)) → deriv (fun s => F (0,0,s)) 0 = 0 →
    IsUnit (tiltHessian Q).det ∧ ∃ C ≥ 0, ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric, Realizes g s A ∧
      let u := fun z => curvatureNumerator g p (tiltedPair U V N₁ N₂ z).first (tiltedPair U V N₁ N₂ z).second
      ∃ m ∈ closedBall 0 δ, IsMinOn u (closedBall 0 δ) m ∧
        |u m - (s^2*Q (stationaryTilt Q) + s^3*T (stationaryTilt Q))| ≤ C*s^4 := by
  intro A F Q T hflat growth first
  obtain ⟨η,hη,_,reg⟩ := graph_window t ht χ p U V N₁ N₂
  have hf : ContDiffAt ℝ 2 F (0,0,0) := (reg (0,0,0) ⟨le_rfl,hη.le⟩).of_le (by norm_num)
  have eq (n : ℕ) : coeff F n 0 = graphCoefficient A U V N₁ N₂ n :=
    funext fun v => graph_coeff_eq_quotient t ht χ p U V N₁ N₂ v n
  have hd := matrix_nonsingular F hf hδ hlam hflat growth
  obtain ⟨a,hq,C,hC,bound⟩ := graph_minimum t ht χ p U V N₁ N₂ hδ hlam hflat growth first
  have he := stationaryTilt_of_minimum F hf a (fun z => (le_add_of_nonneg_right (mul_nonneg (half_pos hlam).le
    (sq_nonneg _))).trans (hq z)) hd
  change IsUnit (tiltHessian (graphCoefficient A U V N₁ N₂ 2)).det ∧ _
  rw [← eq 2] at ⊢
  refine ⟨hd,C,hC,?_⟩
  simpa only [Q,T,← eq 2,← eq 3,he] using bound

end
end LocalHopf.SphereProduct
