import LocalHopf.BackgroundContraction
import LocalHopf.ChartPolynomials

/-! The fixed-base graph and its minimizing normal equation in the coordinates
used by the exact curvature verifier. -/
namespace LocalHopf.SphereProduct.JetChart
open Matrix Real Filter Set Metric BackgroundGrowth Profiles
open scoped ContDiff Topology
noncomputable section

private abbrev V4 := Fin 4 → ℝ
private def graphA (z : V4) : Params := ((1,0),z 0,z 1)
private def graphB (z : V4) : Params := ((0,1),z 2,z 3)

/-- Inverse of the height block on graph coefficients. The first column also
carries the normalization of the simultaneous longitude by h. -/
private def preimage (t c : ℝ) (z : V4) : V4 :=
  let inv (a b : ℝ) := ((1+t)*a-t*c*b)/Profiles.D t c
  ![hh t*inv (z 0) (z 1),hh t*inv (z 1) (z 0),inv (z 2) (z 3),inv (z 3) (z 2)]

private theorem graph_preimage (t c : ℝ) (ht : 0≤t) (hc : c^2≤1) (z : V4) :
    let w := preimage t c z
    pullCoordinates t c (graphA w)=hh t • graphA z ∧ pullCoordinates t c (graphB w)=graphB z := by
  have den := (D_pos ht hc).ne'
  constructor <;> ext <;> simp [pullCoordinates,graphA,graphB,preimage,hh] <;> field_simp [den] <;> unfold Profiles.D <;> ring

private theorem norm_preimage (t c : ℝ) (ht : 0≤t) (hc : c^2≤1) (z : V4) :
    let w := preimage t c z
    ‖z‖^2 ≤ 2*(hh t)^2*(w 0^2+w 1^2+w 2^2+w 3^2) := by
  intro w
  let h := hh t
  have hge : 1≤h := by dsimp [h,hh]; linarith
  have hh₁ : 0≤h^2-1 := by nlinarith only [hge,sq_nonneg (h-1)]
  have r (x y : ℝ) : ((1+t)*x+t*c*y)^2 ≤ h^2*(x^2+y^2) := by
    have op : (1+t)^2+(t*c)^2 ≤ h^2 := by
      dsimp [h,hh]; nlinarith only [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hc),ht,sq_nonneg t]
    nlinarith only [sq_nonneg ((1+t)*y-t*c*x),mul_le_mul_of_nonneg_right op (add_nonneg (sq_nonneg x) (sq_nonneg y))]
  have ⟨L,R⟩ := graph_preimage t c ht hc z
  have e₀ : (1+t)*w 0+t*c*w 1 = h*z 0 := congrArg (fun x : Params => x.2.1) L
  have e₁ : (1+t)*w 1+t*c*w 0 = h*z 1 := (add_comm ..).trans (congrArg (fun x : Params => x.2.2) L)
  have e₂ : (1+t)*w 2+t*c*w 3 = z 2 := congrArg (fun x : Params => x.2.1) R
  have e₃ : (1+t)*w 3+t*c*w 2 = z 3 := (add_comm ..).trans (congrArg (fun x : Params => x.2.2) R)
  have l₀ := r (w 0) (w 1); rw [e₀] at l₀
  have l₁ := r (w 1) (w 0); rw [e₁] at l₁
  have l₂ := r (w 2) (w 3); rw [e₂] at l₂
  have l₃ := r (w 3) (w 2); rw [e₃] at l₃
  let S := w 0^2+w 1^2+w 2^2+w 3^2
  let M := 2*h^2*S
  have sum : z 0^2+z 1^2+z 2^2+z 3^2 ≤ M := by
    dsimp only [M,S]
    nlinarith only [l₀,l₁,l₂,l₃,mul_nonneg hh₁ (sq_nonneg (z 0)),mul_nonneg hh₁ (sq_nonneg (z 1))]
  exact (Transverse.norm_sq_le_sum z).trans sum

private theorem graph_background_scaled (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (z : V4) :
    let c := v.val.2.1.val ⬝ᵥ v.val.2.2.val
    let W := preimage t c z
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    pulledCurvature t c ![1,0,W 0,W 1] ![0,1,W 2,W 3] = 2*((hh t)^2*
      curvatureNumerator (backgroundMetric t ht) p (field r s (graphA z) p) (field r s (graphB z) p)) := by
  intro c W r s p
  let w := (v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val
  have circle : c^2+w^2=1 := separation_circle v
  have hc : c^2≤1 := by nlinarith only [circle,sq_nonneg w]
  have ⟨ea,eb⟩ := graph_preimage t c ht hc z
  let a := field r s (graphA z) p
  let b := field r s (graphB z) p
  have hp : p ∈ (chart r s).source := (chart r s).map_target (center v).1
  obtain ⟨L,hL⟩ := field_equiv r s hp
  have scaled : field r s (hh t • graphA z) p = hh t • a := by rw [←hL,L.map_smul,hL]
  have cb := curvatureNumerator_basis_change (backgroundMetric t ht) p a b (hh t) 0 0 1
  simp only [zero_smul,one_smul,add_zero,zero_add,mul_one,zero_mul,sub_zero] at cb
  have chartEq := curvature_eq_backgroundNumerator v t ht (pullCoordinates t c (graphA W)) (pullCoordinates t c (graphB W))
  change curvatureNumerator _ p (field r s _ p) (field r s _ p) = _ at chartEq
  have eq := pulledCurvature_eq_intrinsic t c w ht circle (graphA W) (graphB W)
  rw [← chartEq,ea,eb,scaled,cb,parameterBasis_coordinates,parameterBasis_coordinates] at eq
  exact eq

/-- The normal second derivative of the background curvature at a graph tilt.
Its only base parameter is the cosine of the separation. -/
def normalSecond (t c : ℝ) (z : V4) :=
  let w := preimage t c z
  let e (i : Fin 7) := Certificate.eval₂ (curvatureEntries i) t c
  (6*e 0*(w 0*w 3-w 1*w 2) + e 1*(w 2^2+w 3^2) + 2*e 2*w 2*w 3 -
    2*e 3*(w 0*w 2-w 1*w 3) + e 4*(w 0^2+w 1^2) + 2*e 5*w 0*w 1) /
      (2*(hh t)^3*Profiles.D t c)

theorem graph_background_derivative (v : FlatLocus.Representative) (t : ℝ) (ht : 0≤t) (z : V4) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    iteratedDeriv 2 (fun h : ℝ => curvatureNumerator (backgroundMetric t ht) p
      (field r s (graphA (h • z)) p) (field r s (graphB (h • z)) p)) 0 =
        normalSecond t (v.val.2.1.val ⬝ᵥ v.val.2.2.val) z := by
  intro r s p
  let c := v.val.2.1.val ⬝ᵥ v.val.2.2.val
  let W := preimage t c z
  let E (i : Fin 7) := Certificate.eval₂ (curvatureEntries i) t c
  let D := Profiles.D t c
  let H := hh t
  let q := normalSecond t c z
  let k := E 6*(W 0*W 3-W 1*W 2)^2/(4*H^3*D)
  have den : 0<D := D_pos ht (by have circ := separation_circle v; dsimp only at circ; dsimp [c]; nlinarith only [circ,sq_nonneg ((v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val)])
  have hpos : H≠0 := (hh_pos ht).ne'
  let F (h : ℝ) := curvatureNumerator (backgroundMetric t ht) p (field r s (graphA (h • z)) p) (field r s (graphB (h • z)) p)
  have formula (h : ℝ) : F h=(q/2)*h^2+k*h^4 := by
    have linear : preimage t c (h • z)=h • W := by
      funext i; fin_cases i <;> simp [preimage,W] <;> ring
    have eq := graph_background_scaled v t ht (h • z)
    change pulledCurvature t c ![1,0,preimage t c (h • z) 0,preimage t c (h • z) 1]
      ![0,1,preimage t c (h • z) 2,preimage t c (h • z) 3] = 2*(H^2*F h) at eq
    rw [linear] at eq
    change curvatureNum t c (minors _ _) / (2*H*((1+t)^2-(t*c)^2)) = 2*(H^2*F h) at eq
    rw [show (1+t)^2-(t*c)^2=D by dsimp [D,Profiles.D]; ring] at eq
    field_simp [den.ne',hpos] at eq
    simp [curvatureNum,minors] at eq
    change F h = (normalSecond t c z/2)*h^2 + k*h^4
    dsimp only [k,normalSecond]
    change F h = ((6*E 0*(W 0*W 3-W 1*W 2)+E 1*(W 2^2+W 3^2)+2*E 2*W 2*W 3-2*E 3*(W 0*W 2-W 1*W 3)+E 4*(W 0^2+W 1^2)+2*E 5*W 0*W 1) / (2*H^3*D)/2)*h^2+E 6*(W 0*W 3-W 1*W 2)^2/(4*H^3*D)*h^4
    field_simp [den.ne',hpos]
    dsimp only [E]
    linear_combination -4*eq
  have twice : iteratedDeriv 2 F 0=q := by
    rw [show F=(fun h : ℝ => q/2*h^2+k*h^4) from funext formula,
      iteratedDeriv_fun_add (f := fun h : ℝ => q/2*h^2) (g := fun h : ℝ => k*h^4) (by fun_prop) (by fun_prop)]
    simp only [iteratedDeriv_const_mul_field,iteratedDeriv_fun_pow_zero]
    norm_num [Nat.factorial]
  exact twice

private def blockMatrix (a b c d e f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a,b,c,d;b,a,-d,-c;c,-d,e,f;d,-c,f,e]

private def matrixDen (t u : ℝ) := (hh t)^2*(Profiles.D t u)^3

private def matrixNum (t u : ℝ) :=
  let h := hh t
  let d := Profiles.D t u
  blockMatrix
    (h^2*(2*t^4*u^4+18*t^4*u^2+4*t^4+27*t^3*u^2+13*t^3+9*t^2*u^2+15*t^2+7*t+1))
    (-h^2*t*u*(10*t^3*u^2+14*t^3+7*t^2*u^2+33*t^2+24*t+5))
    (h*d*(3*t^3*u^2+3*t^3+2*t^2*u^2+7*t^2+5*t+1)) (h^2*d*3*t*u*(1+t))
    (-(1+t)*d*(t^4*u^2-t^4+4*t^3*u^2-4*t^3+2*t^2*u^2-6*t^2-4*t-1))
    (t*u*d*(t^4*u^2-t^4+4*t^2+4*t+1))

/-- The four-dimensional Hessian in the verifier's unscaled height coordinates. -/
def normalMatrix (t c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := (matrixDen t c)⁻¹ • matrixNum t c

set_option maxHeartbeats 1800000 in
theorem normalSecond_matrix (t c : ℝ) (ht : 0≤t) (hc : c^2≤1) (z : V4) :
    normalSecond t c z = z ⬝ᵥ normalMatrix t c *ᵥ z := by
  have den := (D_pos ht hc).ne'
  have hpos := (hh_pos ht).ne'
  simp [normalSecond,normalMatrix,matrixNum,matrixDen,blockMatrix,preimage,dotProduct,mulVec,Fin.sum_univ_four,
    curvatureEntries,Certificate.eval₂,Certificate.horner,List.foldr]
  field_simp [hpos,den]
  unfold Profiles.D hh
  ring

theorem normalMatrix_symmetric (t c : ℝ) : (normalMatrix t c).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem block_det (a b c d e f : ℝ) :
    (blockMatrix a b c d e f).det = ((a+b)*(e-f)-(c-d)^2)*((a-b)*(e+f)-(c+d)^2) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three,Fin.sum_univ_four,blockMatrix,Fin.succAbove]
  ring

set_option maxHeartbeats 1200000 in
theorem normalMatrix_det (t c : ℝ) (ht : 0≤t) (hc : c^2≤1) :
    (normalMatrix t c).det = 4*t^6*(1-c^2)*(4*(1+t)^2-(t*c)^2)/((hh t)^4*(Profiles.D t c)^5) := by
  have den := (D_pos ht hc).ne'
  have hpos := (hh_pos ht).ne'
  rw [normalMatrix,Matrix.det_smul,matrixNum,block_det]
  simp only [Fintype.card_fin,matrixDen]
  field_simp [hpos,den]
  unfold Profiles.D hh
  ring


private def solvePair (a b c x y : ℝ) : ℝ × ℝ :=
  ((c*x-b*y)/(a*c-b^2),(a*y-b*x)/(a*c-b^2))

private theorem solvePair_spec (a b c x y : ℝ) (h : a*c-b^2≠0) :
    let p := solvePair a b c x y
    a*p.1+b*p.2=x ∧ b*p.1+c*p.2=y := by
  dsimp [solvePair]
  constructor <;> simp only [←mul_div_assoc,←add_div] <;> apply (div_eq_iff h).mpr <;> ring

private def solveBlocks (a b c d e f : ℝ) (x : V4) : V4 :=
  let p := solvePair (a+b) (c-d) (e-f) (x 0+x 1) (x 2-x 3)
  let q := solvePair (a-b) (c+d) (e+f) (x 0-x 1) (x 2+x 3)
  ![(p.1+q.1)/2,(p.1-q.1)/2,(p.2+q.2)/2,(q.2-p.2)/2]

private theorem solveBlocks_spec (a b c d e f : ℝ) (x : V4) (nd : (blockMatrix a b c d e f).det≠0) :
    (blockMatrix a b c d e f) *ᵥ solveBlocks a b c d e f x = x := by
  rw [block_det] at nd
  have p := solvePair_spec (a+b) (c-d) (e-f) (x 0+x 1) (x 2-x 3) (left_ne_zero_of_mul nd)
  have q := solvePair_spec (a-b) (c+d) (e+f) (x 0-x 1) (x 2+x 3) (right_ne_zero_of_mul nd)
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,blockMatrix,solveBlocks] <;>
    linarith only [p.1,p.2,q.1,q.2]

/-- The verifier tilt system splits into its symmetric and antisymmetric two-dimensional blocks. -/
def normalSolve (t u : ℝ) (x : V4) : V4 :=
  let H := normalMatrix t u
  solveBlocks (H 0 0) (H 0 1) (H 0 2) (H 0 3) (H 2 2) (H 2 3) x

theorem normalSolve_eq (t u : ℝ) (ht : 0<t) (hu : |u|<1) (x : V4) :
    normalSolve t u x = (normalMatrix t u)⁻¹ *ᵥ x := by
  let H := normalMatrix t u
  have shape : blockMatrix (H 0 0) (H 0 1) (H 0 2) (H 0 3) (H 2 2) (H 2 3) = H := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [H,normalMatrix,matrixNum,blockMatrix]
  have hsq : u^2 < 1 := by simpa using (sq_lt_sq₀ (abs_nonneg u) (by norm_num : (0:ℝ)≤1)).mpr hu
  have tu := mul_lt_mul_of_pos_left hu ht
  have tu' : |t*u|<2*(1+t) := by rw [abs_mul,abs_of_pos ht]; linarith
  have disc : (t*u)^2<(2*(1+t))^2 := (sq_lt_sq).mpr (by rwa [abs_of_pos (by positivity : 0<2*(1+t))])
  have nd : H.det≠0 := by
    change (normalMatrix t u).det≠0
    rw [normalMatrix_det _ _ ht.le hsq.le]
    have hd := D_pos ht.le hsq.le
    have hh := hh_pos ht.le
    have dpos : 0<4*(1+t)^2-(t*u)^2 := by linarith only [disc]
    positivity
  have z := solveBlocks_spec (H 0 0) (H 0 1) (H 0 2) (H 0 3) (H 2 2) (H 2 3) x (shape.symm ▸ nd)
  rw [shape] at z
  change H *ᵥ normalSolve t u x = x at z
  change _ = H⁻¹ *ᵥ x
  calc
    _ = H⁻¹ *ᵥ (H *ᵥ normalSolve t u x) := by rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr nd),Matrix.one_mulVec]
    _ = H⁻¹ *ᵥ x := congrArg (H⁻¹.mulVec) z

/-- Quadratic coercivity in the verifier's four unscaled height tilts at a
regular pair. The constant is allowed to depend on the separation. -/
private theorem regular_graph_coercive (v : FlatLocus.Representative) (t : ℝ) (ht : 0<t)
    (reg : |v.val.2.1.val ⬝ᵥ v.val.2.2.val|<1) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    ∃ lam>0, ∀ z : V4, lam*‖z‖^2 ≤
      curvatureNumerator (backgroundMetric t ht.le) p (field r s (graphA z) p) (field r s (graphB z) p) := by
  intro r s p
  let c := v.val.2.1.val ⬝ᵥ v.val.2.2.val
  let w := (v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ v.val.2.2.val
  have circle : c^2+w^2=1 := separation_circle v
  have hc : c^2≤1 := by nlinarith only [circle,sq_nonneg w]
  obtain ⟨k,hk,lower⟩ := regular_graph_growth ht circle reg
  have h := hh_pos ht.le
  refine ⟨k/(4*(hh t)^4),by positivity,fun z => ?_⟩
  let W := preimage t c z
  let a := field r s (graphA z) p
  let b := field r s (graphB z) p
  have eq := graph_background_scaled v t ht.le z
  have bnd := lower (W 0) (W 1) (W 2) (W 3)
  change k*(W 0^2+W 1^2+W 2^2+W 3^2) ≤ _ at bnd
  rw [show pulledCurvature t c ![1,0,W 0,W 1] ![0,1,W 2,W 3] = _ from eq] at bnd
  have nz := mul_le_mul_of_nonneg_left (norm_preimage t c ht.le hc z) hk.le
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  change k*‖z‖^2 ≤ curvatureNumerator (backgroundMetric t ht.le) p a b * (4*(hh t)^4)
  nlinarith only [nz, mul_le_mul_of_nonneg_left bnd (show 0≤2*(hh t)^2 by positivity)]


theorem sep_regular (v : FlatLocus.Representative)
    (reg : Set.rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular) :
    |v.val.2.1.val ⬝ᵥ v.val.2.2.val| < 1 := by
  let p := v.val.2.1.val
  let q := v.val.2.2.val
  have hp : p ⬝ᵥ p=1 := v.val.2.1.property
  have hq : q ⬝ᵥ q=1 := v.val.2.2.property
  have hr : q≠p ∧ q≠-p := reg
  have sep := (FlatLocus.frame v).2.2.2.2
  apply abs_lt.mpr
  constructor
  · apply lt_of_le_of_ne sep.1
    intro e
    have zero : (q+p) ⬝ᵥ (q+p)=0 := by
      rw [add_dotProduct,dotProduct_add,dotProduct_add,hp,hq,dotProduct_comm q p,←show -1=p ⬝ᵥ q from e]; norm_num
    exact hr.2 (eq_neg_of_add_eq_zero_left (dotProduct_self_eq_zero.mp zero))
  · apply lt_of_le_of_ne sep.2
    intro e
    have zero : (q-p) ⬝ᵥ (q-p)=0 := by
      rw [sub_dotProduct,dotProduct_sub,dotProduct_sub,hp,hq,dotProduct_comm q p,show p ⬝ᵥ q=1 from e]; norm_num
    exact hr.1 (sub_eq_zero.mp (dotProduct_self_eq_zero.mp zero))

/-- In the verifier's actual longitude-height basis the quadratic tilt Hessian
is invertible at every regular pair. Its stationary tilt gives the quadratic
and cubic coefficients of the true fiberwise minimum. -/
theorem regular_graph_minimum (v : FlatLocus.Representative)
    (reg : Set.rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0<t) (χ : Scalar) {δ : ℝ} (hδ : 0<δ) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    let e (i : Fin 4) := field r s (parameterBasis i) p
    let A := paperCoefficients t ht.le χ
    let Q := graphCoefficient A (e 0) (e 1) (e 2) (e 3) 2
    let T := graphCoefficient A (e 0) (e 1) (e 2) (e 3) 3
    IsUnit (tiltHessian Q).det ∧ ∃ C≥0, ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric, Realizes g s A ∧
      let u := fun z => curvatureNumerator g p (tiltedPair (e 0) (e 1) (e 2) (e 3) z).first (tiltedPair (e 0) (e 1) (e 2) (e 3) z).second
      ∃ m ∈ closedBall 0 δ, IsMinOn u (closedBall 0 δ) m ∧
        |u m-(s^2*Q (stationaryTilt Q)+s^3*T (stationaryTilt Q))| ≤ C*s^4 := by
  intro r s p e A Q T
  have h0 : (0:Params) ∈ (chart r s).target := (center v).1
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target h0)
  have axis (z : V4) :
      tiltedPair (e 0) (e 1) (e 2) (e 3) z = ⟨p,field r s (graphA z) p,field r s (graphB z) p⟩ := by
    have lhs : parameterBasis 0 + z 0 • parameterBasis 2 + z 1 • parameterBasis 3 = graphA z := by
      ext <;> simp [parameterBasis_apply,graphA]
    have rhs : parameterBasis 1 + z 2 • parameterBasis 2 + z 3 • parameterBasis 3 = graphB z := by
      ext <;> simp [parameterBasis_apply,graphB]
    have left := congrArg L lhs
    have right := congrArg L rhs
    simp only [map_add,map_smul] at left right
    simp only [hL] at left right
    unfold tiltedPair
    dsimp only [e]
    rw [left,right]
  have bg := Transverse.background_zero t ht.le χ
  let F := graphNumerator A (e 0) (e 1) (e 2) (e 3)
  have actual (z : V4) : F (0,z,0) = curvatureNumerator (backgroundMetric t ht.le) p (field r s (graphA z) p) (field r s (graphB z) p) := by
    dsimp only [F,graphNumerator]
    rw [axis]
    exact TangentPair.numerator_eq _ bg
  obtain ⟨lam,hl,lower⟩ := regular_graph_coercive v t ht (sep_regular v reg)
  apply graph_minimum_coefficients t ht.le χ p (e 0) (e 1) (e 2) (e 3) hδ hl
  · change F _ = 0
    rw [actual]
    exact flat_torus_curvature v h0 rfl t ht.le (1,0) (0,1)
  · intro z _
    exact (lower z).trans_eq (actual z).symm
  · have e0 : tiltedPair (e 0) (e 1) (e 2) (e 3) 0 =
        ⟨p,field r s ((1,0),0) p,field r s ((0,1),0) p⟩ := axis 0
    dsimp only [graphNumerator]
    rw [e0]
    exact (flat_torus_first v h0 rfl t ht.le χ (1,0) (0,1)).deriv


/-- The intrinsic regular-fiber minimum with both coefficients evaluated from
the spatial tensor entries and the fixed-plane response of the conformal correction. -/
theorem regular_minimum_from_entries (v : FlatLocus.Representative)
    (reg : Set.rangeFactorization FlatLocus.forgetOrientation v ∈ FlatLocus.regular)
    (t : ℝ) (ht : 0<t) (χ : Scalar) {δ : ℝ} (hδ : 0<δ) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let p := (chart r s).symm 0
    let e (i : Fin 4) := field r s (parameterBasis i) p
    let A := paperCoefficients t ht.le χ
    let P := gramPolys v t ht.le
    let D := (P 0 0).det
    let coeff (n : ℕ) (z : Fin 4 → ℝ) := quotientCoeff (residual (movingChartPolynomial P z) D n) D
    let a := stationaryTilt (coeff 2)
    IsUnit (tiltHessian (coeff 2)).det ∧ ∃ C≥0, ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric, Realizes g s A ∧
      let u := fun z => curvatureNumerator g p (tiltedPair (e 0) (e 1) (e 2) (e 3) z).first (tiltedPair (e 0) (e 1) (e 2) (e 3) z).second
      ∃ m ∈ closedBall 0 δ, IsMinOn u (closedBall 0 δ) m ∧
        |u m-(s^2*coeff 2 a+s^3*(coeff 3 a+conformalResponse t ht.le 0 χ (e 0) (e 1)))| ≤ C*s^4 := by
  intro r s p e A P D coeff a
  let graph (φ : Scalar) := graphCoefficient (paperCoefficients t ht.le φ) (e 0) (e 1) (e 2) (e 3)
  have raw (n : ℕ) : graph 0 n = coeff n := funext (fun z => graphCoefficient_eq_chartPolynomial v t ht.le z n)
  have q : graph χ 2 = coeff 2 := (graph_cubic_correction t ht.le 0 χ (e 0) (e 1) (e 2) (e 3)).1.trans (raw 2)
  have cub : graph χ 3 = fun z => coeff 3 z + conformalResponse t ht.le 0 χ (e 0) (e 1) := by
    funext z
    have h := graph_conformal_response t ht.le 0 χ (e 0) (e 1) (e 2) (e 3) z
    change graph χ 3 z-graph 0 3 z = _ at h
    rw [raw 3] at h
    linarith only [h]
  obtain ⟨inv,C,hC,win⟩ := regular_graph_minimum v reg t ht χ hδ
  refine ⟨by rw [←q]; exact inv,C,hC,?_⟩
  filter_upwards [win] with h wh
  obtain ⟨g,hg,m,hm,min,est⟩ := wh
  refine ⟨g,hg,m,hm,min,?_⟩
  change |_- (h^2*graph χ 2 (stationaryTilt (graph χ 2))+h^3*graph χ 3 (stationaryTilt (graph χ 2)))| ≤ C*h^4 at est
  rw [q,cub] at est
  exact est


/-- Canonical longitude-height input of the rational curvature verifier. Its columns
are the three fixed axes in the frame based at the first sphere point. -/
def verifierFrame (v : FlatLocus.Representative) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![v.val.2.1.val,v.val.1.val ⨯₃ v.val.2.1.val,v.val.1.val]

theorem verifierFrame_rotation (v : FlatLocus.Representative) :
    (verifierFrame v)*(verifierFrame v)ᵀ=1 ∧ (verifierFrame v).det=1 := by
  let n := v.val.1.val
  let p := v.val.2.1.val
  let w := n ⨯₃ p
  have pn : p ⬝ᵥ n=0 := (dotProduct_comm p n).trans v.property.1
  have ww : w ⬝ᵥ w=1 := by rw [show w ⬝ᵥ w = _ from cross_dot_cross n p n p,v.property.1,v.val.1.property,v.val.2.1.property]; ring
  have lhs (i j : Fin 3) : (verifierFrame v*(verifierFrame v)ᵀ) i j = (verifierFrame v i) ⬝ᵥ (verifierFrame v j) := rfl
  constructor
  · ext i j
    rw [lhs]
    fin_cases i <;> fin_cases j <;> simp [verifierFrame,dotProduct_comm (_ ⨯₃ _) _,show v.val.1.val ⬝ᵥ v.val.1.val=1 from v.val.1.property,show v.val.2.1.val ⬝ᵥ v.val.2.1.val=1 from v.val.2.1.property,
      v.property.1,show v.val.2.1.val ⬝ᵥ v.val.1.val=0 from pn,show (v.val.1.val ⨯₃ v.val.2.1.val) ⬝ᵥ (v.val.1.val ⨯₃ v.val.2.1.val)=1 from ww]
  · change Matrix.det ![p,w,n]=1
    rw [←triple_product_eq_det]
    dsimp only [w]
    rw [←cross_anticomm n (n ⨯₃ p),cross_cross_eq_smul_sub_smul',v.property.1,v.val.1.property]
    simpa only [zero_smul,one_smul,zero_sub,neg_neg] using (show p ⬝ᵥ p=1 from v.val.2.1.property)

/-- Every positively oriented regular separation has the verifier's positive
half-angle parameter. This identifies the sign of every square-root entry. -/
theorem verifier_separation (x : FlatLocus.Plane) (reg : x∈FlatLocus.regular) :
    let v := FlatLocus.oriented x
    let p := v.val.2.1.val
    let q := v.val.2.2.val
    let w := v.val.1.val ⨯₃ p
    ∃ r : ℝ, 0<r ∧ p ⬝ᵥ q=(1-r^2)/(1+r^2) ∧ w ⬝ᵥ q=2*r/(1+r^2) ∧
      Real.sqrt (1-(p ⬝ᵥ q)^2)=2*r/(1+r^2) ∧ q=((1-r^2)/(1+r^2)) • p+(2*r/(1+r^2)) • w := by
  intro v p q w
  let u := p ⬝ᵥ q
  let s := w ⬝ᵥ q
  have mapped : Set.rangeFactorization FlatLocus.forgetOrientation v=x := Subtype.ext (FlatLocus.oriented_spec x).1
  have hu : |u|<1 := sep_regular v (mapped ▸ reg)
  have circle : u^2+s^2=1 := separation_circle v
  have nonneg : 0≤s := by
    have eq : s=v.val.1.val ⬝ᵥ (p ⨯₃ q) := (dotProduct_comm w q).trans (triple_product_permutation q v.val.1.val p)
    rw [eq]; exact (FlatLocus.oriented_spec x).2
  have pos : 0<s := nonneg.lt_of_ne' (by intro h; rw [h] at circle; nlinarith only [circle,(sq_lt_one_iff_abs_lt_one u).mpr hu])
  have d : 0<1+u := by linarith only [(abs_lt.mp hu).1]
  let r := s/(1+u)
  have den : 0<1+r^2 := by positivity
  have co : u=(1-r^2)/(1+r^2) := by
    apply (eq_div_iff den.ne').mpr
    dsimp only [r]
    field_simp [d.ne']
    linear_combination (1+u)*circle
  have si : s=2*r/(1+r^2) := by
    apply (eq_div_iff den.ne').mpr
    dsimp only [r]
    field_simp [d.ne']
    linear_combination circle
  have sq : sqrt (1-u^2)=s := by rw [show 1-u^2=s^2 by linarith only [circle],sqrt_sq nonneg]
  refine ⟨r,div_pos pos d,co,si,sq.trans si,?_⟩
  rw [←co,←si]
  let L := align _ _ v.property.1
  let X := WithLp.toLp 2 q
  have coord : (L.symm X).ofLp = ![u,s,0] := by
    rw [show (L.symm X).ofLp = _ from align_coordinates _ _ v.property.1 X,v.property.2]
  have eq := align_apply _ _ v.property.1 (L.symm X).ofLp
  change (L (L.symm X)).ofLp= _ at eq
  rw [L.apply_symm_apply,coord] at eq
  simpa using eq

end
end LocalHopf.SphereProduct.JetChart
