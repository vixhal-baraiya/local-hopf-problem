import LocalHopf.QuadraticCertificate
import LocalHopf.FlatLocus

/-! The quadratic normal form evaluated on the fitted vectors and both fitted matrices. -/
namespace LocalHopf.Certificate
open Profiles Matrix
noncomputable section

private def orbitFactors (t u : ℝ) := (1+t+t*u)*(1+t-t*u)
private def vd (t u : ℝ) := 40*(hh t)^2*(orbitFactors t u)^2
private def d₁ (t u : ℝ) := 4*hh t*(orbitFactors t u)^2
private def d₂ (t u : ℝ) := 4*hh t*(orbitFactors t u)^3
private def v (i : Fin 4) (t u : ℝ) := eval₂ (vectorNum i) t u
private def m (i : Fin 4) (t u : ℝ) := eval₂ (matrix1Num i) t u
private def n (i : Fin 3) (t u : ℝ) := eval₂ (matrix2Num i) t u

/-- The fit uses the basis (p₁,n × p₁) and the oriented separation with nonnegative sine. -/
def vectorA (t u : ℝ) : Fin 2 → ℝ := ![v 0 t u/vd t u, Real.sqrt (1-u^2)*v 1 t u/vd t u]
def vectorB (t u : ℝ) : Fin 2 → ℝ := ![v 2 t u/vd t u, Real.sqrt (1-u^2)*v 3 t u/vd t u]
def matrix₁ (t u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![m 0 t u/d₁ t u, Real.sqrt (1-u^2)*m 1 t u/d₁ t u;
     Real.sqrt (1-u^2)*m 2 t u/d₁ t u, m 3 t u/d₁ t u]
def matrix₂ (t u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![n 0 t u/d₂ t u, Real.sqrt (1-u^2)*n 1 t u/d₂ t u;
     Real.sqrt (1-u^2)*n 1 t u/d₂ t u, n 2 t u/d₂ t u]

private theorem den_sq (t u : ℝ) :
    (vd t u)^2 = 4*eval₂ sc.den t u ∧
    (d₁ t u)^2 = 2*eval₂ n1.den t u ∧ (d₂ t u)^2 = 2*eval₂ n2.den t u := by
  norm_num [vd, d₁, d₂, hh, orbitFactors, sc, n1, n2, eval₂, horner, List.foldr]
  exact ⟨by ring, by ring, by ring⟩

set_option maxHeartbeats 3000000 in
private theorem vector_sq (t u : ℝ) : (v 0 t u)^2 + (1-u^2)*(v 1 t u)^2 +
    (v 2 t u)^2 + (1-u^2)*(v 3 t u)^2 = 4*eval₂ sc.num t u := by
  norm_num [v, vectorNum, sc, eval₂, horner, List.foldr]
  ring

set_option maxHeartbeats 3000000 in
private theorem matrix₁_sq (t u : ℝ) : (m 0 t u)^2 + (1-u^2)*(m 1 t u)^2 +
    (1-u^2)*(m 2 t u)^2 + (m 3 t u)^2 = 2*eval₂ n1.num t u := by
  norm_num [m, matrix1Num, n1, eval₂, horner, List.foldr]
  ring

set_option maxHeartbeats 3000000 in
private theorem matrix₂_sq (t u : ℝ) : (n 0 t u)^2 + 2*(1-u^2)*(n 1 t u)^2 +
    (n 2 t u)^2 = 2*eval₂ n2.num t u := by
  norm_num [n, matrix2Num, n2, eval₂, horner, List.foldr]
  ring

theorem fitted_norms (t u : ℝ) (hu : |u| ≤ 1) :
    vectorA t u ⬝ᵥ vectorA t u + vectorB t u ⬝ᵥ vectorB t u = sc.value t u ∧
    (∑ i, ∑ j, matrix₁ t u i j^2) = n1.value t u ∧
    (∑ i, ∑ j, matrix₂ t u i j^2) = n2.value t u := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one u).2 hu))
  obtain ⟨dv, dm, dn⟩ := den_sq t u
  constructor
  · calc
      _ = ((v 0 t u)^2 + (1-u^2)*(v 1 t u)^2 + (v 2 t u)^2 + (1-u^2)*(v 3 t u)^2)/(vd t u)^2 := by
        simp [vectorA, vectorB, dotProduct, Fin.sum_univ_two, ← sq, div_pow, mul_pow, hs]
        ring
      _ = _ := by rw [vector_sq, dv, Quotient.value]; exact mul_div_mul_left _ _ (by norm_num)
  constructor
  · calc
      _ = ((m 0 t u)^2 + (1-u^2)*(m 1 t u)^2 + (1-u^2)*(m 2 t u)^2 + (m 3 t u)^2)/(d₁ t u)^2 := by
        simp [matrix₁, Fin.sum_univ_two, div_pow, mul_pow, hs]; ring
      _ = _ := by rw [matrix₁_sq, dm, Quotient.value]; exact mul_div_mul_left _ _ (by norm_num)
  · calc
      _ = ((n 0 t u)^2 + 2*(1-u^2)*(n 1 t u)^2 + (n 2 t u)^2)/(d₂ t u)^2 := by
        simp [matrix₂, Fin.sum_univ_two, div_pow, mul_pow, hs]; ring
      _ = _ := by rw [matrix₂_sq, dn, Quotient.value]; exact mul_div_mul_left _ _ (by norm_num)

/-- The certificate field of the abstract theorem for all the exported functions. -/
theorem fitted_gcal {t u : ℝ} (ht : t ∈ Set.Icc 0 (1/100)) (hu : |u| ≤ 1) :
    3/10 ≤ Gcal lamC lamD (Fx t u) (Fy t u) (vectorA t u) (vectorB t u) (matrix₁ t u) (matrix₂ t u) :=
  let ⟨ab, m₁, m₂⟩ := fitted_norms t u hu
  gcal_ge ht hu _ _ _ _ ab m₁ m₂

/-- Proposition 5.2 on the concrete incidence locus, for the expression in Proposition 5.1. -/
theorem fitted_V2_on_locus {t : ℝ} (ht : t ∈ Set.Icc 0 (1/100)) (x : FlatLocus.Plane) :
    let f := FlatLocus.data
    let u := f.sep x
    3/10*f.ρ x ≤ V2form lamC lamD (Fx t u) (Fy t u) (f.nx x) (f.ny x) (f.nz x)
      (vectorA t u) (vectorB t u) (f.xp x) (f.zp x) (matrix₁ t u) (matrix₂ t u) := by
  intro f u
  let r := FlatLocus.oriented x
  have hx : Set.rangeFactorization FlatLocus.forgetOrientation r = x :=
    Subtype.ext (FlatLocus.oriented_spec x).1
  obtain ⟨hρ,hunit,hz,hp,hsep⟩ := FlatLocus.frame r
  rw [hx] at hρ hz
  have hu : |u| ≤ 1 := by
    have e := congrArg (fun p : FlatLocus.Ambient => p.1.1 ⬝ᵥ p.1.2) (FlatLocus.oriented_spec x).1
    apply abs_le.mpr
    change _ ≤ x.val.1.1 ⬝ᵥ x.val.1.2 ∧ x.val.1.1 ⬝ᵥ x.val.1.2 ≤ _
    rw [← e]
    exact hsep
  exact V2_ge_kappa_rho _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num [lamC]) hρ hunit hz hp (fitted_gcal ht hu)

end
end LocalHopf.Certificate
