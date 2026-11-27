import LocalHopf.ChartCometric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Spatial Taylor data of the longitude-height chart used in the curvature computation. -/
namespace LocalHopf.SphereProduct.LongitudeHeight
open Real Filter Set Matrix
open scoped ContDiff Topology
noncomputable section

/-- Constant, linear and quadratic Taylor coefficients along a coordinate line. -/
structure SpatialJet (f : ℝ → ℝ) (a b c : ℝ) : Prop where
  smooth : ContDiffAt ℝ ∞ f 0
  value : f 0 = a
  first : deriv f 0 = b
  second : iteratedDeriv 2 f 0 = 2*c

theorem jet_const (a : ℝ) : SpatialJet (fun _ => a) a 0 0 :=
  ⟨contDiffAt_const,rfl,by simp,by simp [iteratedDeriv_const]⟩

private theorem jet_id : SpatialJet id 0 1 0 :=
  ⟨contDiffAt_id,rfl,by simp,by simp [iteratedDeriv_id]⟩

theorem jet_add {f g : ℝ → ℝ} {a b c A B C : ℝ} (x : SpatialJet f a b c) (y : SpatialJet g A B C) :
    SpatialJet (fun z => f z+g z) (a+A) (b+B) (c+C) where
  smooth := x.smooth.add y.smooth
  value := by rw [x.value,y.value]
  first := by rw [deriv_fun_add (x.smooth.differentiableAt (by simp)) (y.smooth.differentiableAt (by simp)),x.first,y.first]
  second := by
    change iteratedDeriv 2 (f+g) 0 = _
    rw [iteratedDeriv_add (x.smooth.of_le (by simp)) (y.smooth.of_le (by simp)),x.second,y.second]; ring

theorem jet_mul {f g : ℝ → ℝ} {a b c A B C : ℝ} (x : SpatialJet f a b c) (y : SpatialJet g A B C) :
    SpatialJet (fun z => f z*g z) (a*A) (b*A+a*B) (c*A+b*B+a*C) where
  smooth := x.smooth.mul y.smooth
  value := by rw [x.value,y.value]
  first := by rw [deriv_fun_mul (x.smooth.differentiableAt (by simp)) (y.smooth.differentiableAt (by simp)),x.first,y.first,x.value,y.value]
  second := by
    change iteratedDeriv 2 (f*g) 0 = _
    rw [iteratedDeriv_mul (x.smooth.of_le (by simp)) (y.smooth.of_le (by simp))]
    norm_num [Finset.sum_range_succ,iteratedDeriv_one,x.value,y.value,x.first,y.first,x.second,y.second]
    ring

theorem jet_neg {f : ℝ → ℝ} {a b c : ℝ} (x : SpatialJet f a b c) :
    SpatialJet (fun z => -f z) (-a) (-b) (-c) := by simpa using jet_mul (jet_const (-1)) x

theorem jet_sub {f g : ℝ → ℝ} {a b c A B C : ℝ} (x : SpatialJet f a b c) (y : SpatialJet g A B C) :
    SpatialJet (fun z => f z-g z) (a-A) (b-B) (c-C) := by simpa only [sub_eq_add_neg] using jet_add x (jet_neg y)

theorem jet_scale (a : ℝ) {f : ℝ → ℝ} {x y z : ℝ} (h : SpatialJet f x y z) :
    SpatialJet (fun q => a*f q) (a*x) (a*y) (a*z) := by simpa using jet_mul (jet_const a) h

theorem SpatialJet.congr {f g : ℝ → ℝ} {a b c : ℝ} (j : SpatialJet f a b c) (e : g =ᶠ[𝓝 0] f) :
    SpatialJet g a b c :=
  ⟨j.smooth.congr_of_eventuallyEq e,e.self_of_nhds.trans j.value,e.deriv_eq.trans j.first,(e.iteratedDeriv_eq (n := 2)).trans j.second⟩

private theorem jet_of_smooth (f : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0) :
    SpatialJet f (f 0) (deriv f 0) (iteratedDeriv 2 f 0/2) := ⟨hf,rfl,rfl,by ring⟩

private theorem jet_unique {f g : ℝ → ℝ} {a b c A B C : ℝ} (x : SpatialJet f a b c) (y : SpatialJet g A B C)
    (h : f =ᶠ[𝓝 0] g) : a=A ∧ b=B ∧ c=C := by
  exact ⟨x.value.symm.trans (h.self_of_nhds.trans y.value),x.first.symm.trans (h.deriv_eq.trans y.first),by
    linarith only [x.second,y.second,h.iteratedDeriv_eq (n := 2)]⟩

/-- The radial factor, its reciprocal contribution to the longitude, and the
round inverse metric in the height variable match the script to degree two. -/
theorem height_jets (h : ℝ) :
    SpatialJet (fun z => sqrt (1-(h*z)^2)) 1 0 (-(h^2)/2) ∧
    SpatialJet (fun z => h*z/sqrt (1-(h*z)^2)) 0 h 0 ∧
    SpatialJet (fun z => (1-(h*z)^2)⁻¹) 1 0 (h^2) := by
  let Z := fun z : ℝ => h*z
  let S := fun z : ℝ => 1-(Z z)^2
  let R := fun z => sqrt (S z)
  have z : SpatialJet Z 0 h 0 := by simpa [Z] using jet_scale h jet_id
  have s : SpatialJet S 1 0 (-(h^2)) := by simpa [S,sq] using jet_sub (jet_const 1) (jet_mul z z)
  have pos : ∀ᶠ x in 𝓝 0, 0 < S x := s.smooth.continuousAt.eventually_const_lt (s.value ▸ zero_lt_one)
  have reg : ContDiffAt ℝ ∞ R 0 := s.smooth.sqrt (by rw [s.value]; norm_num)
  have R0 : R 0 = 1 := by simp [R,s.value]
  have r := jet_of_smooth R reg
  have sqeq : (fun z => R z * R z) =ᶠ[𝓝 0] S := by filter_upwards [pos] with x hx using (by simpa [R,sq] using sq_sqrt hx.le)
  obtain ⟨_,d₁,d₂⟩ := jet_unique (jet_mul r r) s sqeq
  rw [R0] at d₁ d₂
  have d : deriv R 0 = 0 := by linarith
  rw [d] at d₂
  have jr : SpatialJet R 1 0 (-(h^2)/2) := ⟨reg,R0,d,by linarith⟩
  let W := fun x => Z x/R x
  have jw := jet_of_smooth W (z.smooth.div reg (by rw [R0]; norm_num))
  have ew : (fun x => W x*R x) =ᶠ[𝓝 0] Z := by
    filter_upwards [pos] with x hx using div_mul_cancel₀ _ (sqrt_pos.mpr hx).ne'
  obtain ⟨w₀,w₁,w₂⟩ := jet_unique (jet_mul jw jr) z ew
  have wz : W 0 = 0 := by simpa using w₀
  let I := fun x => (S x)⁻¹
  have ji := jet_of_smooth I (s.smooth.inv (by rw [s.value]; norm_num))
  have ei : (fun x => I x*S x) =ᶠ[𝓝 0] (fun _ => 1) := by
    filter_upwards [pos] with x hx using inv_mul_cancel₀ hx.ne'
  obtain ⟨i₀,i₁,i₂⟩ := jet_unique (jet_mul ji s) (jet_const 1) ei
  have iv : I 0 = 1 := by simpa using i₀
  exact ⟨jr,⟨jw.smooth,wz,by simpa using w₁,by rw [wz] at w₂; linarith⟩,
    ⟨ji.smooth,iv,by simpa using i₁,by rw [iv] at i₂; linarith⟩⟩

private theorem trig_jets (a A : ℝ) :
    SpatialJet (fun z => cos (a+A*z)) (cos a) (-A*sin a) (-A^2*cos a/2) ∧
    SpatialJet (fun z => sin (a+A*z)) (sin a) (A*cos a) (-A^2*sin a/2) := by
  let f := fun z : ℝ => a + A*z
  have df (z : ℝ) : HasDerivAt f A z := by
    simpa [f] using (((hasDerivAt_id' z).const_mul A).const_add a)
  have dc : deriv (fun z => cos (f z)) = fun z => -sin (f z)*A := funext fun z => (df z).cos.deriv
  have ds : deriv (fun z => sin (f z)) = fun z => cos (f z)*A := funext fun z => (df z).sin.deriv
  change SpatialJet (fun z => cos (f z)) _ _ _ ∧ SpatialJet (fun z => sin (f z)) _ _ _
  have reg : ContDiffAt ℝ ∞ f 0 := by dsimp [f]; fun_prop
  constructor
  · refine ⟨reg.cos,by simp [f],by rw [dc]; simp [f]; ring,?_⟩
    have hd : HasDerivAt (fun z => -sin (f z)*A) (-(cos (f 0)*A)*A) 0 := ((df 0).sin.neg).mul_const A
    rw [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,dc,hd.deriv]
    simp [f]; ring
  · refine ⟨reg.sin,by simp [f],by rw [ds]; simp [f]; ring,?_⟩
    rw [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,ds,
      ((df 0).cos.mul_const A).deriv]
    simp [f]; ring

/-- Exact angular and vertical second jets of an ambient rotation. The linear and
quadratic coefficients include the mixed angle-height term. -/
theorem rotation_jets (w : R3) (a A h : ℝ) :
    let q := cos a*w 0+sin a*w 1
    let d := sin a*w 0-cos a*w 1
    let lon := fun z => w 2-(h*z/sqrt (1-(h*z)^2))*(cos (a+A*z)*w 0+sin (a+A*z)*w 1)
    let vert := fun z => sqrt (1-(h*z)^2)*(sin (a+A*z)*w 0-cos (a+A*z)*w 1)
    SpatialJet lon (w 2) (-h*q) (h*A*d) ∧
    SpatialJet vert d (A*q) (-((A^2+h^2)/2)*d) ∧
    ∀ᶠ z in 𝓝 0, w ⨯₃ (point (a+A*z,h*z)).val.ofLp =
      lon z • lonVector (a+A*z) (h*z) + vert z • heightVector (a+A*z) (h*z) := by
  intro q d lon vert
  obtain ⟨c,s⟩ := trig_jets a A
  obtain ⟨rad,zr,_⟩ := height_jets h
  have cosPart := jet_add (jet_mul c (jet_const (w 0))) (jet_mul s (jet_const (w 1)))
  have sinPart := jet_sub (jet_mul s (jet_const (w 0))) (jet_mul c (jet_const (w 1)))
  refine ⟨?_,?_,?_⟩
  · convert jet_sub (jet_const (w 2)) (jet_mul zr cosPart) using 1 <;> (try dsimp [q,d]) <;> ring
  · convert jet_mul rad sinPart using 1 <;> dsimp [q,d] <;> ring
  · have near : ∀ᶠ z in 𝓝 (0:ℝ), |h*z| < 1 :=
      (continuous_abs.comp (continuous_const.mul continuous_id)).continuousAt.eventually_lt_const (by simp)
    filter_upwards [near] with z hz using rotation_components w _ _ hz

/-- The Cartesian entries of the actual sphere parametrization have exactly
the two-jet used by the coordinate curvature calculation. -/
theorem point_jets (a A h : ℝ) :
    let p := fun z : ℝ => (point (a+A*z,h*z)).val.ofLp
    SpatialJet (fun z => p z 0) (cos a) (-A*sin a) (-((A^2+h^2)/2)*cos a) ∧
    SpatialJet (fun z => p z 1) (sin a) (A*cos a) (-((A^2+h^2)/2)*sin a) ∧
    SpatialJet (fun z => p z 2) 0 h 0 := by
  intro p
  obtain ⟨c,s⟩ := trig_jets a A
  have r := (height_jets h).1
  have near : ∀ᶠ z in 𝓝 (0:ℝ), |h*z| < 1 :=
    (continuous_abs.comp (continuous_const.mul continuous_id)).continuousAt.eventually_lt_const (by simp)
  have same {f g : ℝ → ℝ} {a b c : ℝ} (H : SpatialJet f a b c) (e : g =ᶠ[𝓝 0] f) : SpatialJet g a b c :=
    ⟨H.smooth.congr_of_eventuallyEq e,e.self_of_nhds.trans H.value,e.deriv_eq.trans H.first,
      (e.iteratedDeriv_eq (n := 2)).trans H.second⟩
  have coord (z : ℝ) (hz : |h*z| < 1) : p z =
      ![sqrt (1-(h*z)^2)*cos (a+A*z),sqrt (1-(h*z)^2)*sin (a+A*z),h*z] := by
    change ![cos (arcsin (h*z))*cos _,cos (arcsin (h*z))*sin _,sin (arcsin (h*z))] = _
    rw [cos_arcsin,sin_arcsin (abs_lt.mp hz).1.le (abs_lt.mp hz).2.le]
  constructor
  · apply same (f := fun z => sqrt (1-(h*z)^2)*cos (a+A*z))
    · convert jet_mul r c using 1 <;> ring
    · filter_upwards [near] with z hz using congrFun (coord z hz) 0
  constructor
  · apply same (f := fun z => sqrt (1-(h*z)^2)*sin (a+A*z))
    · convert jet_mul r s using 1 <;> ring
    · filter_upwards [near] with z hz using congrFun (coord z hz) 1
  · apply same (f := fun z => h*z)
    · simpa using jet_scale h jet_id
    · filter_upwards [near] with z hz using congrFun (coord z hz) 2

/-- Each of the sixteen entries of the unit round inverse metric has the
quadratic truncation initialized by the verifier in x,y,z₁,z₂ coordinates. -/
theorem round_inverse_jets (h k : ℝ) (i j : Fin 4) :
    let C : Matrix (Fin 4) (Fin 4) ℝ := ![![1/2,0,0,0],![0,1/2,0,0],![0,0,1,0],![0,0,0,1]]
    let m := (h^2+k^2)/4
    let d := (k^2-h^2)/4
    let D : Matrix (Fin 4) (Fin 4) ℝ := ![![m,d,0,0],![d,m,0,0],![0,0,-h^2,0],![0,0,0,-k^2]]
    SpatialJet (fun z => JetChart.roundInverse (h*z) (k*z) i j) (C i j) 0 (D i j) := by
  intro C m d D
  have height (a : ℝ) : SpatialJet (fun z : ℝ => 1-(a*z)^2) 1 0 (-a^2) := by
    have z := jet_scale a jet_id
    simpa [sq] using jet_sub (jet_const 1) (jet_mul z z)
  have A := (height_jets h).2.2
  have B := (height_jets k).2.2
  have M := jet_mul (jet_add A B) (jet_const (1/4))
  have N := jet_mul (jet_sub B A) (jet_const (1/4))
  fin_cases i <;> fin_cases j
  all_goals try first | exact jet_const 0 | exact height h | exact height k
  all_goals dsimp [C,D,m,d,JetChart.roundInverse]
  all_goals first | (solve | convert M using 1 <;> first | (funext z; ring) | ring) | (convert N using 1 <;> first | (funext z; ring) | ring)

end
end LocalHopf.SphereProduct.LongitudeHeight
