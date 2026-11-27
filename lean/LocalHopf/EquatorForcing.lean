import LocalHopf.EquatorJetData
import LocalHopf.EquatorConformal
import LocalHopf.ChartConvergence

/-! # Rotation of the equatorial cubic in the longitude-height calculation

The raw numerator table comes from the full metric with a symbolic rotation of the
axes. Homogenizing the two half-angle parameters includes the missing points of
both rational parametrizations. Identifying these chart jets with the intrinsic
Levi-Civita calculation is a separate geometric obligation. -/
namespace LocalHopf.EquatorJet
open Real Function
open scoped ContDiff Topology Filter
noncomputable section

private def evalRow (t : ℝ) (v : List ℤ) := v.foldr (fun a b => (a:ℝ) + t*b) 0

private def homog (t x y : ℝ) : List (List ℤ) → ℝ
  | [] => 0
  | a :: l => evalRow t a * x^l.length + y * homog t x y l

private def raw (i : Fin 7) (t x y : ℝ) := homog t x y (data i)

private def denom (t x y : ℝ) :=
  10000 * (1+2*t)^2 * (x^2+y^2)^5 * (y^2+(1+2*t)*x^2)^2 * ((1+2*t)*y^2+x^2)^2

-- An integer polynomial identity on the raw jet table, before either angular substitution.
set_option maxHeartbeats 3000000 in
private theorem weighted_raw (t x y : ℝ) :
    5*raw 0 t x y + raw 2 t x y + raw 4 t x y + 5*raw 6 t x y =
      4 * (x^2+y^2)^5 * (y^2+(1+2*t)*x^2)^2 * ((1+2*t)*y^2+x^2)^2 := by
  norm_num [raw,data,homog,evalRow,List.foldr]
  ring

private theorem scale (t x y c : ℝ) (v : List ℤ) (l : List (List ℤ)) :
    homog t (c*x) (c*y) (v::l) = c^l.length * homog t x y (v::l) := by
  induction l generalizing v with
  | nil => simp [homog]
  | cons w l ih =>
    change evalRow t v*(c*x)^(l.length+1) + c*y*homog t (c*x) (c*y) (w::l) =
      c^(l.length+1)*(evalRow t v*x^(l.length+1)+y*homog t x y (w::l))
    rw [mul_pow,ih w,pow_succ c]
    ring

private theorem raw_neg (i : Fin 7) (t x y : ℝ) : raw i t (-x) (-y) = raw i t x y := by
  have size : (data i).length = 19 := by fin_cases i <;> decide
  unfold raw
  cases h : data i with
  | nil => rfl
  | cons v l =>
    rw [h,List.length_cons] at size
    have hl : l.length = 18 := by omega
    simpa [hl,show (-1:ℝ)^18 = 1 by norm_num] using scale t x y (-1) v l

private theorem denom_pos (t : ℝ) (ht : 0 ≤ t) (x y : ℝ) (circle : x^2+y^2 = 1) :
    0 < denom t x y := by
  have hx : 0 < y^2 + (1+2*t)*x^2 := by nlinarith [mul_nonneg ht (sq_nonneg x)]
  have hy : 0 < (1+2*t)*y^2+x^2 := by nlinarith [mul_nonneg ht (sq_nonneg y)]
  unfold denom; rw [circle]; positivity

private def weights (t d : ℝ) (i : Fin 7) :=
  raw i t (cos (d/2)) (sin (d/2)) / denom t (cos (d/2)) (sin (d/2))

private theorem weights_mean (t : ℝ) (ht : 0 ≤ t) (d : ℝ) :
    (5*weights t d 0 + weights t d 2 + weights t d 4 + 5*weights t d 6)/16 = Profiles.mu t := by
  let x := cos (d/2)
  let y := sin (d/2)
  have circ : x^2+y^2=1 := cos_sq_add_sin_sq _
  have hd := (denom_pos t ht x y circ).ne'
  have hh := (Profiles.hh_pos ht).ne'
  change (5*(raw 0 t x y/denom t x y) + raw 2 t x y/denom t x y + raw 4 t x y/denom t x y +
    5*(raw 6 t x y/denom t x y))/16 = _
  rw [show Profiles.mu t = 1/(40000*(1+2*t)^2) from Profiles.cubic_mean_eq t]
  have h : 1+2*t ≠ 0 := hh
  calc
    _ = (5*raw 0 t x y + raw 2 t x y + raw 4 t x y + 5*raw 6 t x y)/(16*denom t x y) := by field_simp [hd]
    _ = _ := (div_eq_div_iff (mul_ne_zero (by norm_num) hd) (by positivity)).mpr (by
      rw [weighted_raw]; dsimp [denom]; ring)

private def sextic (p : Fin 7 → ℝ) (x y : ℝ) :=
  p 0*x^6 + p 1*x^5*y + p 2*x^4*y^2 + p 3*x^3*y^3 + p 4*x^2*y^4 + p 5*x*y^5 + p 6*y^6

private def angular (p : Fin 7 → ℝ) (m : ℝ) := sextic p (cos (m/2)) (sin (m/2))

private def modes (p : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![(5*p 0+p 2+p 4+5*p 6)/16,(15*p 0+p 2-p 4-15*p 6)/32,(5*p 1+3*p 3+5*p 5)/32,
    (6*p 0-2*p 2-2*p 4+6*p 6)/32,(p 1-p 5)/8,(p 0-p 2+p 4-p 6)/32,(p 1-p 3+p 5)/32]

private theorem harmonics (p : Fin 7 → ℝ) (m : ℝ) :
    angular p m = trig3 (modes p 0) (modes p 1) (modes p 2) (modes p 3) (modes p 4)
      (modes p 5) (modes p 6) m := by
  let x := cos (m/2)
  let y := sin (m/2)
  let a := modes p
  let L := x^2+y^2
  have circle : L = 1 := cos_sq_add_sin_sq _
  have c : cos m = x*x-y*y := by
    conv_lhs => rw [show m=m/2+m/2 by ring,cos_add]
  have s : sin m = y*x+x*y := by
    conv_lhs => rw [show m=m/2+m/2 by ring,sin_add]
  have eq : angular p m =
      a 0*L^3 + (a 1*cos m+a 2*sin m)*L^2 + (a 3*cos (2*m)+a 4*sin (2*m))*L +
      a 5*cos (3*m)+a 6*sin (3*m) := by
    rw [show 3*m=2*m+m by ring,cos_add,sin_add,show 2*m=m+m by ring,cos_add,sin_add,c,s]
    dsimp [angular,sextic,a,modes,L,x,y]
    ring
  rw [eq,circle]
  simp only [one_pow,mul_one,trig3,a]; ring

/-- Cubic numerator exported from the longitude-height chart, including coincident
and antipodal longitudes. Rotating the points by alpha rotates the axes by -alpha
in the chart normalized to first longitude zero. -/
def forcing (t : ℝ) (p : ℝ × ℝ) := angular (weights t (p.2-p.1)) (-p.1)


/-- The verifier table evaluated at the two signed half-angle parameters. -/
def rationalForcing (t r x y : ℝ) :=
  sextic (fun i => raw i t 1 r) x y / (denom t 1 r*(x^2+y^2)^3)

private theorem raw_scale (i : Fin 7) (t x y c : ℝ) :
    raw i t (c*x) (c*y) = c^18 * raw i t x y := by
  have size : (data i).length=19 := by fin_cases i <;> decide
  unfold raw
  cases eq : data i with
  | nil => simp [eq] at size
  | cons h l =>
    rw [eq,List.length_cons] at size
    have e : l.length=18 := by omega
    simpa [e] using scale t x y c h l

private theorem weights_rational (t δ : ℝ) (hn : cos (δ/2)≠0) (i : Fin 7) :
    weights t δ i = raw i t 1 (tan (δ/2)) / denom t 1 (tan (δ/2)) := by
  let x := cos (δ/2)
  let r := tan (δ/2)
  have hnx : x≠0 := hn
  have xy : x*r=sin (δ/2) := by dsimp [x,r]; rw [tan_eq_sin_div_cos]; field_simp
  have h (i : Fin 7) : raw i t x (sin (δ/2))=x^18*raw i t 1 r := by simpa only [mul_one,xy] using raw_scale i t 1 r x
  have hd : denom t x (sin (δ/2))=x^18*denom t 1 r := by rw [←xy]; unfold denom; ring
  change raw i t x (sin (δ/2))/denom t x (sin (δ/2))=_
  rw [h,hd,mul_div_mul_left _ _ (pow_ne_zero _ hnx)]

/-- On the rational chart this is exactly the unhomogenized cubic in the
script, with rotation angle minus the first longitude and signed separation. -/
theorem forcing_rational (t α β : ℝ) (hd : cos ((β-α)/2)≠0) (ha : cos (-α/2)≠0) :
    forcing t (α,β)=rationalForcing t (tan ((β-α)/2)) 1 (tan (-α/2)) := by
  let x := cos (-α/2)
  let a := tan (-α/2)
  let r := tan ((β-α)/2)
  have y : sin (-α/2)=x*a := by dsimp only [x,a]; rw [tan_eq_sin_div_cos,mul_comm,div_mul_cancel₀ _ ha]
  have circ := cos_sq_add_sin_sq (-α/2)
  rw [y] at circ
  change x^2+(x*a)^2=1 at circ
  have norm : x^6*(1+a^2)^3=1 := by
    calc
      _ = (x^2+(x*a)^2)^3 := by ring
      _ = 1 := by rw [circ]; norm_num
  have hn : 1+a^2≠0 := by positivity
  let L := denom t 1 r
  let W (i : Fin 7) := raw i t 1 r
  have eq : weights t (β-α) = fun i => W i/L := funext (weights_rational t (β-α) hd)
  change sextic (weights t (β-α)) x (sin (-α/2))=sextic W 1 a / (L*((1:ℝ)^2+a^2)^3)
  rw [one_pow]
  rw [eq,y]
  calc
    _ = (sextic W 1 a/L)*x^6 := by unfold sextic; simp only [div_eq_mul_inv]; ring
    _ = _ := by
      rw [div_mul_eq_div_div,eq_div_iff (pow_ne_zero _ hn),mul_assoc,norm,mul_one]

/-- At the omitted rotation longitude the highest rotation coefficient survives. -/
theorem forcing_at_rotation_pole (t α β : ℝ) (hd : cos ((β-α)/2)≠0) (ha : cos (-α/2)=0) :
    forcing t (α,β)=rationalForcing t (tan ((β-α)/2)) 0 1 := by
  have c := cos_sq_add_sin_sq (-α/2)
  rw [ha] at c; simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_add] at c
  have sn : sin (-α/2)^6=1 := by rw [show (6:ℕ)=2*3 by decide,pow_mul,c,one_pow]
  change sextic (weights t (β-α)) (cos (-α/2)) (sin (-α/2))=_
  simp [rationalForcing,sextic,ha,sn,weights_rational t (β-α) hd]

private theorem weights_period (t d : ℝ) : weights t (d+2*π) = weights t d := by
  funext i
  simp only [weights,show (d+2*π)/2=d/2+π by ring,cos_add_pi,sin_add_pi,raw_neg,denom,neg_sq]

private theorem angular_period (p : Fin 7 → ℝ) (m : ℝ) : angular p (m+2*π) = angular p m := by
  simp only [angular,show (m+2*π)/2=m/2+π by ring,cos_add_pi,sin_add_pi,sextic]
  ring

private theorem smooth_weights (t : ℝ) (ht : 0 ≤ t) (i : Fin 7) : ContDiff ℝ ∞ (fun d => weights t d i) := by
  let x := fun d : ℝ => cos (d/2)
  let y := fun d : ℝ => sin (d/2)
  have smooth (l : List (List ℤ)) : ContDiff ℝ ∞ (fun d => homog t (x d) (y d) l) := by
    induction l with
    | nil => exact contDiff_const
    | cons a l ih =>
      exact (contDiff_const.mul ((show ContDiff ℝ ∞ x by dsimp [x]; fun_prop).pow _)).add
        ((show ContDiff ℝ ∞ y by dsimp [y]; fun_prop).mul ih)
  apply (smooth (data i)).div
  · dsimp [denom,x,y]; fun_prop
  · exact fun d => (denom_pos t ht _ _ (cos_sq_add_sin_sq (d/2))).ne'

private theorem smooth_forcing (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (forcing t) := by
  have coeff (i : Fin 7) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => weights t (q.2-q.1) i) :=
    (smooth_weights t ht i).comp (contDiff_snd.sub contDiff_fst)
  change ContDiff ℝ ∞ (fun q : ℝ × ℝ => forcing t q)
  dsimp only [forcing,angular,sextic]
  fun_prop (disch := exact coeff _)

/-- Degree and constant Fourier coefficient of the exported curvature forcing
along every rotation orbit, including the exceptional separations. -/
theorem rotation (t : ℝ) (ht : 0 ≤ t) (d : ℝ) :
    ∃ a b c e j k : ℝ, ∀ m, forcing t (m+d,m-d) = trig3 (Profiles.mu t) a b c e j k m := by
  let w := weights t (-2*d)
  let a := modes w
  let A (i : Fin 7) (l : Fin 7) (x : ℝ) := a i*cos x - a l*sin x
  let B (i : Fin 7) (l : Fin 7) (x : ℝ) := -(a i*sin x + a l*cos x)
  refine ⟨A 1 2 d,B 1 2 d,A 3 4 (2*d),B 3 4 (2*d),A 5 6 (3*d),B 5 6 (3*d),fun m => ?_⟩
  have h : a 0 = Profiles.mu t := weights_mean t ht (-2*d)
  change angular (weights t (m-d-(m+d))) (-(m+d)) = _
  rw [show m-d-(m+d) = -2*d by ring,harmonics]
  change trig3 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (-(m+d)) = _
  simp only [trig3,h,mul_neg,mul_add,cos_neg,sin_neg,cos_add,sin_add,A,B]
  ring

theorem four_point_mean (t : ℝ) (ht : 0 ≤ t) (d : ℝ) :
    let V := fun m => forcing t (m+d,m-d)
    (V 0 + V (π/2) + V π + V (3*π/2))/4 = Profiles.mu t := by
  obtain ⟨a,b,c,e,j,k,h⟩ := rotation t ht d
  simp only [h,trig3_four_point_mean]

/-- A smooth potential on the actual sphere product for the exported cubic
forcing. Its tangential second-derivative contribution corrects that forcing
to the prescribed constant at every longitude. -/
theorem corrected_forcing (t : ℝ) (ht : 0 ≤ t) :
    ∃ χ : SphereProduct.Scalar,
      (∀ d, (∫ m in (0:ℝ)..2*π, χ (SphereProduct.equatorPoint (m+d),SphereProduct.equatorPoint (m-d))) = 0) ∧
      (∀ m d, let C := SphereProduct.equatorCoefficient (SphereProduct.thirdOrderTensor t ht χ)
        forcing t (m+d,m-d) + (deriv (fun x => deriv (C 0 1 x) d) m -
          (iteratedDeriv 2 (fun x => C 1 1 x d) m + iteratedDeriv 2 (C 0 0 m) d)/2) = Profiles.mu t) ∧
      ∀ᶠ s in 𝓝 (0:ℝ), ∃ g : SphereProduct.SmoothMetric, SphereProduct.Realizes g s (SphereProduct.paperCoefficients t ht χ) := by
  have p₁ (b : ℝ) : Periodic (fun a => forcing t (a,b)) (2*π) := by
    intro a
    have sep := weights_period t (b-(a+2*π))
    rw [show b-(a+2*π)+2*π = b-a by ring] at sep
    have ang := angular_period (weights t (b-a)) (-(a+2*π))
    rw [show -(a+2*π)+2*π = -a by ring] at ang
    exact (congrArg (fun p => angular p (-(a+2*π))) sep.symm).trans ang.symm
  have p₂ (a : ℝ) : Periodic (fun b => forcing t (a,b)) (2*π) := by
    intro b
    change angular (weights t (b+2*π-a)) (-a) = _
    rw [show b+2*π-a=b-a+2*π by ring,weights_period]
    rfl
  obtain ⟨χ,zero,lap,_,met⟩ := SphereProduct.exists_torus_correction t ht (forcing t)
    (smooth_forcing t ht) p₁ p₂ (fun d => by
      obtain ⟨a,b,c,e,j,k,h⟩ := rotation t ht d; exact ⟨_,a,b,c,e,j,k,h⟩) (four_point_mean t ht)
  refine ⟨χ,zero,fun m d => ?_,met⟩
  dsimp only
  rw [SphereProduct.equator_conformal_second,lap]
  ring

/-- On any sequence of backgrounds approaching zero, there are genuine smooth
metrics realizing the exported torus correction and converging after scaling.
The tangential second-derivative identity holds at every separation. -/
theorem corrected_sequence (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (ht₀ : Filter.Tendsto t Filter.atTop (𝓝 0)) :
    ∃ (χ : ℕ → SphereProduct.Scalar) (s : ℕ → ℝ) (g : ℕ → SphereProduct.SmoothMetric),
      (∀ n, 0 < s n) ∧ Filter.Tendsto s Filter.atTop (𝓝[>] 0) ∧
      (∀ n, SphereProduct.Realizes (g n) (s n) (SphereProduct.paperCoefficients (t n) (ht n) (χ n))) ∧
      (∀ n m d, let C := SphereProduct.equatorCoefficient (SphereProduct.thirdOrderTensor (t n) (ht n) (χ n))
        forcing (t n) (m+d,m-d) + (deriv (fun x => deriv (C 0 1 x) d) m -
          (iteratedDeriv 2 (fun x => C 1 1 x d) m + iteratedDeriv 2 (C 0 0 m) d)/2) = Profiles.mu (t n)) ∧
      SphereProduct.ConvergesToRound (fun n => SphereProduct.twiceMetric (g n)) := by
  choose χ _ corrected available using fun n => corrected_forcing (t n) (ht n)
  obtain ⟨s,g,positive,limit,real,converges⟩ := SphereProduct.diagonal_paper_metrics t ht ht₀ χ
    (fun _ _ _ => True) (fun n => ((available n).filter_mono nhdsWithin_le_nhds).mono
      (fun _ ⟨g,h⟩ => ⟨g,h,trivial⟩))
  exact ⟨χ,s,g,positive,limit,fun n => (real n).1,corrected,converges⟩

end
end LocalHopf.EquatorJet
