import LocalHopf.ChartCometric
import LocalHopf.ChartExpansion
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Matrix.Normed

/-! The finite Neumann inverse in the curvature verification scripts. -/
namespace LocalHopf.SphereProduct.JetChart
open Matrix Filter Set
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
variable {M : Type*} [NormedRing M] [NormedAlgebra ℝ M]

/-- The terms through degree n in the left Neumann expansion about B. -/
def inverseSeries (B L : M) : ℕ → M
  | 0 => B
  | n+1 => B + L * inverseSeries B L n

omit [NormedAlgebra ℝ M] in
private theorem remainder (B L G : M) (h : B+L*G = G) (n : ℕ) :
    G - inverseSeries B L n = L^(n+1)*G := by
  induction n with
  | zero => simp [inverseSeries]; exact sub_eq_iff_eq_add.mpr (by rw [add_comm,h])
  | succ n ih =>
    calc G-inverseSeries B L (n+1) = L*(G-inverseSeries B L n) := by
           rw [inverseSeries,mul_sub]
           have e : G-B=L*G := sub_eq_iff_eq_add.mpr (by rw [add_comm,h])
           abel_nf at e ⊢
           grind
         _ = _ := by rw [ih,pow_succ' L (n+1),mul_assoc]

private theorem vanishing (L G : ℝ → M) (hL : ContDiffAt ℝ ∞ L 0) (hG : ContDiffAt ℝ ∞ G 0)
    (zero : L 0 = 0) (n k : ℕ) (hk : k < n) : iteratedDeriv k (L^n * G) 0 = 0 := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    have hprod : ContDiffAt ℝ (k : ℕ) (L^n * G) 0 := ((hL.pow n).mul hG).of_le (by simp)
    rw [pow_succ',mul_assoc,iteratedDeriv_mul (hL.of_le (by simp)) hprod]
    apply Finset.sum_eq_zero
    intro i hi
    have := Finset.mem_range.mp hi
    cases i with
    | zero => simp [zero]
    | succ j => rw [ih (k-(j+1)) (by omega),mul_zero]

/-- The actual and truncated inverses have identical derivatives through the
requested order. The residual at order n contains n+1 factors vanishing at zero. -/
theorem inverseSeries_deriv (B : M) (L G : ℝ → M) (hL : ContDiffAt ℝ ∞ L 0)
    (hG : ContDiffAt ℝ ∞ G 0) (zero : L 0 = 0) (eq : ∀ᶠ z in 𝓝 0, B+L z*G z=G z)
    (n k : ℕ) (hk : k ≤ n) :
    iteratedDeriv k G 0 = iteratedDeriv k (fun z => inverseSeries B (L z) n) 0 := by
  let S (m : ℕ) (z : ℝ) := inverseSeries B (L z) m
  have hs (m : ℕ) : ContDiffAt ℝ ∞ (S m) 0 := by
    induction m with
    | zero => exact contDiffAt_const
    | succ m ih => exact contDiffAt_const.add (hL.mul ih)
  have h : G-S n =ᶠ[𝓝 0] L^(n+1)*G := by
    filter_upwards [eq] with z hz using remainder B (L z) (G z) hz n
  have e := h.iteratedDeriv_eq (n := k)
  rw [iteratedDeriv_sub (hG.of_le (by simp)) ((hs n).of_le (by simp)),vanishing L G hL hG zero _ _ (by omega)] at e
  exact sub_eq_zero.mp e

/-- Contravariant chart entries before truncating spatial coordinates. -/
def backgroundInverse (r s : E3 ≃ₗᵢ[ℝ] E3) (t : ℝ) (y : Params) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => 2*(roundInverse y.2.1 y.2.2 i j + t*∑ k, rotationEntry r s y i k*rotationEntry r s y j k)

/-- Along every smooth coordinate curve the finite inverse used by the verifier
has the same Taylor coefficients as the actual background. At a common-normal
center its starting value is the explicit matrix in `metric_at_center`. -/
theorem background_inverse_series (r s : E3 ≃ₗᵢ[ℝ] E3) (t : ℝ) (ht : 0 ≤ t)
    (γ : ℝ → Params) (reg : ContDiffAt ℝ ∞ γ 0) (inside : γ 0 ∈ (chart r s).target)
    (n k : ℕ) (hk : k ≤ n) :
    let G (z : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
      coefficient r s (backgroundMetric t ht) (parameterBasis i) (parameterBasis j) (γ z)
    let A := backgroundInverse r s t ∘ γ
    iteratedDeriv k G 0 = iteratedDeriv k (fun z => inverseSeries (G 0) (G 0*(A 0-A z)) n) 0 := by
  intro G A
  have near : ∀ᶠ z in 𝓝 0, γ z ∈ (chart r s).target :=
    reg.continuousAt.preimage_mem_nhds ((chart r s).open_target.mem_nhds inside)
  have invert (z : ℝ) (hz : γ z ∈ (chart r s).target) :
      (G z)⁻¹ = A z ∧ IsUnit (G z).det := by
    constructor
    · exact Matrix.ext (explicit_cometric r s hz t ht)
    · obtain ⟨b,hb,_⟩ := chart_cometric r s hz t ht
      have eq : G z = gramMatrix (backgroundMetric t ht) b := by
        ext i j
        change _ = (backgroundMetric t ht).inner _ (b i) (b j)
        rw [hb,hb]; rfl
      rw [eq]; exact gram_isUnit _ _
  have smoothG : ContDiffAt ℝ ∞ G 0 := by
    let unit (i j : Fin 4) := Matrix.single i j (1:ℝ)
    have e : G = fun z => ∑ i, ∑ j, (G z i j) • unit i j := by
      funext z
      ext i j
      simp [unit,Matrix.sum_apply,Matrix.single_apply,ite_and,Finset.sum_ite_irrel]
    rw [e]
    apply ContDiffAt.sum; intro i _
    apply ContDiffAt.sum; intro j _
    have h := (tensor_smooth r s (backgroundTensor t ht) (parameterBasis i) (parameterBasis j) inside).comp 0 reg
    exact h.smul contDiffAt_const
  have hunit := (Matrix.isUnit_iff_isUnit_det (G 0)).mpr (invert 0 inside).2
  have smInv : ContDiffAt ℝ ∞ Ring.inverse (G 0) := (hunit.unit_spec ▸ contDiffAt_ringInverse ℝ hunit.unit)
  have smoothA : ContDiffAt ℝ ∞ A 0 := by
    apply (smInv.comp 0 smoothG).congr_of_eventuallyEq
    filter_upwards [near] with z hz
    exact (invert z hz).1.symm.trans (nonsing_inv_eq_ringInverse (G z))
  apply inverseSeries_deriv _ _ _ (contDiffAt_const.mul (contDiffAt_const.sub smoothA)) smoothG (by simp)
  · filter_upwards [near] with z hz
    have u := invert z hz
    have v := invert 0 inside
    change G 0 + G 0*(A 0-A z)*G z = G z
    rw [mul_sub,sub_mul,← u.1,← v.1,mul_nonsing_inv _ v.2,one_mul,mul_assoc,nonsing_inv_mul _ u.2,mul_one]
    abel
  · exact hk

end
end LocalHopf.SphereProduct.JetChart
