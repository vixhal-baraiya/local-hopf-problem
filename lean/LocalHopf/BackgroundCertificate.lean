import LocalHopf.BackgroundData
import LocalHopf.BackgroundGrowth

/-! An explicit sum-of-squares verification of (Z) for the exported background
curvature operator. All parameters, tangent vectors and endpoint separations
are included. The intrinsic identification with the
Levi-Civita curvature is proved in BackgroundContraction. -/
namespace LocalHopf.BackgroundGrowth
open Matrix Certificate
noncomputable section

def minors (x y : Fin 4 → ℝ) : Fin 6 → ℝ :=
  let m (i j : Fin 4) := x i*y j-x j*y i
  ![m 0 1,m 0 2,m 0 3,m 1 2,m 1 3,m 2 3]

private theorem plucker (x y : Fin 4 → ℝ) :
    let w := minors x y
    w 0*w 5-w 1*w 4+w 2*w 3 = 0 := by
  simp [minors]; ring

/-- Ambient vector at p=(1,0,0), q=(u,v,0), in the script's four directions. -/
def chartVector (u v : ℝ) (x : Fin 4 → ℝ) : R3 × R3 :=
  (![0,x 0-x 1,x 2],![-v*(x 0+x 1),u*(x 0+x 1),x 3])

private def lowerValue (t u : ℝ) (w : Fin 6 → ℝ) :=
  (w 1-w 3)^2 + (w 2+w 4)^2 + t^3/4*(4*(w 1^2+2*u*w 1*w 2+w 2^2)+(1-u^2)*w 5^2)

private theorem chart_lower (t u v : ℝ) (hv : u^2+v^2=1) (x y : Fin 4 → ℝ) :
    zillerLower ![1,0,0] ![u,v,0] t (chartVector u v x) (chartVector u v y) =
      lowerValue t u (minors x y) := by
  let w := minors x y
  have mm (a : Fin 4 → ℝ) :
      moment ![1,0,0] ![u,v,0] (chartVector u v a) = ![v*a 3,-a 2-u*a 3,2*a 0] := by
    ext i
    fin_cases i <;> simp [chartVector,moment,cross_apply]
    all_goals first | linear_combination (a 0+a 1)*hv | ring
  have h₁ : (chartVector u v x).1 ⨯₃ (chartVector u v y).1 = ![w 1-w 3,0,0] := by
    ext i; fin_cases i <;> simp [chartVector,w,minors,cross_apply]; ring
  have h₂ : (chartVector u v x).2 ⨯₃ (chartVector u v y).2 = ![u*(w 2+w 4),v*(w 2+w 4),0] := by
    ext i; fin_cases i <;> simp [chartVector,w,minors,cross_apply] <;> ring
  have h₃ : moment ![1,0,0] ![u,v,0] (chartVector u v x) ⨯₃ moment ![1,0,0] ![u,v,0] (chartVector u v y) =
      ![2*w 1+2*u*w 2,2*v*w 2,v*w 5] := by
    rw [mm,mm]
    ext i; fin_cases i <;> simp [w,minors,cross_apply] <;> ring
  rw [zillerLower,h₁,h₂,h₃]
  change _ = lowerValue t u w
  simp [sqLength, lowerValue, dotProduct, Fin.sum_univ_three]
  linear_combination ((w 2+w 4)^2+t^3/4*(4*w 2^2+w 5^2))*hv

private def scaleDen (t u : ℝ) := 2*(1+2*t)*((1+t)^2-(t*u)^2)

def curvatureNum (t u : ℝ) (w : Fin 6 → ℝ) :=
  let c (i : Fin 7) := eval₂ (curvatureEntries i) t u
  c 0*(4*w 0*w 5+2*w 1*w 4-2*w 2*w 3) + c 1*(w 1^2+w 2^2) +
    2*c 2*w 1*w 2 + 2*c 3*(w 1*w 3-w 2*w 4) + c 4*(w 3^2+w 4^2) +
    2*c 5*w 3*w 4 + c 6*w 5^2

/-- The full exported (0,4) curvature operator for g_CM evaluated on the
two input vectors after applying the inverse Cheeger endomorphism. -/
def pulledCurvature (t u : ℝ) (x y : Fin 4 → ℝ) :=
  curvatureNum t u (minors x y) / scaleDen t u

private theorem defect (t u : ℝ) (w : Fin 6 → ℝ) :
    let h := 1+2*t
    let d := (1+t)^2-(t*u)^2
    let a := (1+t)*w 1-w 3
    let b := (1+t)*w 2+w 4
    curvatureNum t u w = lowerValue t u w*scaleDen t u +
      3*t*h*((1+u)*(1+t*(1+u))*(a+b)^2 + (1-u)*(1+t*(1-u))*(a-b)^2) +
      (3*t^3/2)*d*(1-u^2)*w 5^2 +
      8*t*u*(1+t)*h^2*(w 0*w 5-w 1*w 4+w 2*w 3) := by
  norm_num [curvatureNum,curvatureEntries,eval₂,horner,List.foldr,scaleDen,lowerValue]
  ring

/-- (Z) for the exact chart table, all t ≥ 0 and all separations. -/
theorem zillerLower_le_chart {t u v : ℝ} (ht : 0 ≤ t) (huv : u^2+v^2=1) (x y : Fin 4 → ℝ) :
    zillerLower ![1,0,0] ![u,v,0] t (chartVector u v x) (chartVector u v y) ≤ pulledCurvature t u x y := by
  have hu : |u| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp (by nlinarith [sq_nonneg v])
  have plus : 0 ≤ 1+u := by linarith [(abs_le.mp hu).1]
  have minus : 0 ≤ 1-u := sub_nonneg.mpr (abs_le.mp hu).2
  have pd : 0 < (1+t)^2-(t*u)^2 := by
    rw [show (1+t)^2-(t*u)^2=(1+t*(1-u))*(1+t*(1+u)) by ring]
    positivity
  have hd : 0 < scaleDen t u := by unfold scaleDen; positivity
  rw [chart_lower _ _ _ huv, pulledCurvature,le_div_iff₀ hd,defect,plucker,mul_zero,add_zero]
  have hv : 0 ≤ 1-u^2 := by nlinarith [sq_nonneg v]
  apply le_trans _ (le_add_of_nonneg_right (by positivity))
  exact le_add_of_nonneg_right (by positivity)


/-- For regular separations the chart curvature has quadratic growth in all four
tilts of the plane, in the coordinates before the inverse Cheeger map. -/
theorem regular_graph_growth {t u v : ℝ} (ht : 0 < t) (hc : u^2+v^2=1) (hu : |u| < 1) :
    ∃ lam > 0, ∀ a b c d : ℝ, lam*(a^2+b^2+c^2+d^2) ≤
      pulledCurvature t u ![1,0,a,b] ![0,1,c,d] := by
  let m := t^3*(1-|u|)
  let k := min (1/2 : ℝ) (m/3)
  have hm : 0 < m := mul_pos (pow_pos ht _) (sub_pos.mpr hu)
  have hk : 0 < k := lt_min (by norm_num) (by positivity)
  refine ⟨k,hk,?_⟩
  intro a b c d
  let x : Fin 4 → ℝ := ![1,0,a,b]
  let y : Fin 4 → ℝ := ![0,1,c,d]
  have h := zillerLower_le_chart ht.le hc x y
  rw [chart_lower _ _ _ hc] at h
  apply le_trans _ h
  simp [x,y,minors,lowerValue]
  have hq : (1-|u|)*(c^2+d^2) ≤ c^2+2*u*c*d+d^2 := by
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
      nlinarith [mul_nonneg h (sq_nonneg (c+d))]
    · rw [abs_of_nonpos h]
      nlinarith [mul_nonneg (neg_nonneg.mpr h) (sq_nonneg (c-d))]
  have bound : k*(a^2+b^2+c^2+d^2) ≤ (a+c)^2+(d-b)^2 + m*(c^2+d^2) := by
    have k₁ := min_le_left (1/2:ℝ) (m/3)
    have k₂ := min_le_right (1/2:ℝ) (m/3)
    change k ≤ _ at k₁ k₂
    have norm : a^2+b^2+c^2+d^2 ≤ 2*((a+c)^2+(d-b)^2)+3*(c^2+d^2) := by
      nlinarith [sq_nonneg (a+2*c),sq_nonneg (b-2*d)]
    nlinarith only [mul_le_mul_of_nonneg_left norm hk.le,
      mul_nonneg (show 0 ≤ 1-2*k by linarith) (add_nonneg (sq_nonneg (a+c)) (sq_nonneg (d-b))),
      mul_nonneg (show 0 ≤ m-3*k by linarith) (add_nonneg (sq_nonneg c) (sq_nonneg d))]
  have tail : 0 ≤ t^3*(1-u^2)*(a*d-b*c)^2 := by
    rw [show 1-u^2=v^2 by linarith]; positivity
  dsimp only [m] at bound
  nlinarith only [bound, mul_le_mul_of_nonneg_left hq (pow_nonneg ht.le 3),tail]

/-- The fixed-base graph disk contains a line of zero-curvature planes at
both singular separations. Such a disk cannot be a transverse normal disk there. -/
theorem singular_graph_line (t z : ℝ) :
    pulledCurvature t 1 ![1,0,z,z] ![0,1,-z,z] = 0 ∧
    pulledCurvature t (-1) ![1,0,z,-z] ![0,1,-z,-z] = 0 := by
  constructor <;> unfold pulledCurvature
  all_goals
    apply div_eq_zero_iff.mpr
    left
    rw [defect]
    norm_num [lowerValue,minors]
    first | (solve | ring_nf) | (ring_nf; simp)


end
end LocalHopf.BackgroundGrowth
