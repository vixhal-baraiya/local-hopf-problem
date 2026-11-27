import LocalHopf.TorusCorrection

/-! # Spatial derivatives of the conformal correction along the equator -/
namespace LocalHopf.SphereProduct
open Real
noncomputable section

private def point (m d : ℝ) : Base := (equatorPoint (m+d),equatorPoint (m-d))

/-- Coefficients of a tensor pulled back to the equatorial longitude chart.
The two actual velocities are simultaneous and opposite rotation. -/
def equatorCoefficient (H : AmbientTensor) (i j : Fin 2) (m d : ℝ) : ℝ :=
  let U := deriv (fun x => ambientPoint (point x d)) m
  let V := deriv (fun y => ambientPoint (point m y)) d
  H.form (point m d) (![U,V] i) (![U,V] j)

/-- The scalar second-derivative term in the equatorial curvature formula
for the cubic conformal tensor is the negative flat Laplacian of its potential.
The induced Gram determinant accounts for the factor in the unnormalized numerator. -/
theorem equator_conformal_second (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) (m d : ℝ) :
    let C := equatorCoefficient (thirdOrderTensor t ht χ)
    let f := fun x y => χ (equatorPoint (x+y),equatorPoint (x-y))
    deriv (fun x => deriv (C 0 1 x) d) m -
      (iteratedDeriv 2 (fun x => C 1 1 x d) m + iteratedDeriv 2 (C 0 0 m) d)/2 =
      -(Profiles.hh t * iteratedDeriv 2 (fun x => f x d) m + iteratedDeriv 2 (f m) d) := by
  intro C f
  have mult (i j : Fin 2) (a b : ℝ) :
      C i j a b = (2*Profiles.hh t*f a b) * equatorCoefficient (backgroundTensor t ht) i j a b := rfl
  have diag (a b : ℝ) : C 0 0 a b = 2 * f a b ∧ C 0 1 a b = 0 ∧
      C 1 1 a b = (2*Profiles.hh t)*f a b := by
    have bg : equatorCoefficient (backgroundTensor t ht) 0 0 a b = 1 / Profiles.hh t ∧
        equatorCoefficient (backgroundTensor t ht) 0 1 a b = 0 ∧
        equatorCoefficient (backgroundTensor t ht) 1 1 a b = 1 := equator_metric t ht a b
    rw [mult,mult,mult,bg.1,bg.2.1,bg.2.2]
    have hn := (Profiles.hh_pos ht).ne'
    constructor
    · field_simp
    · simp
  have mixed (a : ℝ) : C 0 1 a = fun _ => 0 := funext (fun b => (diag a b).2.1)
  rw [show (fun x => deriv (C 0 1 x) d) = fun _ => 0 by funext x; rw [mixed,deriv_const],
    show (fun x => C 1 1 x d) = fun x => (2*Profiles.hh t)*f x d from funext fun x => (diag x d).2.2,
    show C 0 0 m = fun y => 2*f m y from funext fun y => (diag m y).1]
  simp only [deriv_const,iteratedDeriv_const_mul_field]
  ring

end
end LocalHopf.SphereProduct
