import LocalHopf.TiltedCurvature

/-! # Exact polynomial division for moving-plane curvature

Along an affine tilt both spanning vectors vary linearly. Spatial derivatives
act on the coefficient fields of the tensor and leave the polynomial weights
alone. The resulting numerator has the same Gram determinant as a fixed plane.
-/
namespace LocalHopf.SphereProduct
open Polynomial Matrix Bundle FiberBundle Filter
open scoped Topology Manifold ContDiff
noncomputable section

private abbrev Regular (p : Base) (f : Base → ℝ) :=
  ∀ᶠ q in 𝓝 p, ContMDiffAt productModel 𝓘(ℝ,ℝ) ∞ f q

private inductive SpatialPoly (p : Base)
  | atom (f : Base → ℝ) (hf : Regular p f)
  | add (a b : SpatialPoly p)
  | scale (w : ℝ[X]) (a : SpatialPoly p)

private def SpatialPoly.atPoint {p : Base} : SpatialPoly p → Base → ℝ[X]
  | .atom f _, q => C (f q)
  | .add a b, q => a.atPoint q + b.atPoint q
  | .scale w a, q => w * a.atPoint q

private def SpatialPoly.differentiate {p : Base} (V : Field) (hV : ∀ᶠ q in 𝓝 p, FieldSmoothAt V q) :
    SpatialPoly p → SpatialPoly p
  | .atom f hf => .atom (directional V f) (by filter_upwards [hV,hf] with q hv h using directional_smoothAt hv h)
  | .add a b => .add (a.differentiate V hV) (b.differentiate V hV)
  | .scale w a => .scale w (a.differentiate V hV)

private theorem SpatialPoly.regular {p : Base} (a : SpatialPoly p) (s : ℝ) :
    Regular p (fun q => (a.atPoint q).eval s) := by
  induction a with
  | atom f h => simpa [SpatialPoly.atPoint] using h
  | add a b ha hb =>
    filter_upwards [ha,hb] with q h k
    simp only [SpatialPoly.atPoint,eval_add]
    exact h.add k
  | scale w a ha =>
    filter_upwards [ha] with q h
    simp only [SpatialPoly.atPoint,eval_mul]
    exact (contMDiffAt_const (c := w.eval s)).mul h

private theorem SpatialPoly.eval_derivative {p : Base} (V : Field) (hv : ∀ᶠ q in 𝓝 p, FieldSmoothAt V q)
    (a : SpatialPoly p) (s : ℝ) :
    directional V (fun q => (a.atPoint q).eval s) =ᶠ[𝓝 p] fun q => ((a.differentiate V hv).atPoint q).eval s := by
  induction a with
  | atom f h => simp [SpatialPoly.atPoint,SpatialPoly.differentiate]
  | add a b ha hb =>
    filter_upwards [ha,hb,a.regular s,b.regular s] with q ea eb ra rb
    simp only [SpatialPoly.differentiate,SpatialPoly.atPoint,eval_add]
    rw [← ea,← eb]
    exact directional_add V (ra.mdifferentiableAt (by simp)) (rb.mdifferentiableAt (by simp))
  | scale w a ha =>
    filter_upwards [ha,a.regular s] with q ea ra
    simp only [SpatialPoly.differentiate,SpatialPoly.atPoint,eval_mul]
    rw [← ea]
    exact directional_mul_const V _ (ra.mdifferentiableAt (by simp))

/-- Initial vector and velocity of an affine tilt in a single tangent space. -/
abbrev AffineTangent (p : Base) := Tangent p × Tangent p

private def affineVal {p : Base} (a : AffineTangent p) (s : ℝ) := a.1+s • a.2

private theorem extend_affine {p : Base} (a : AffineTangent p) (s : ℝ) :
    ∀ᶠ q in 𝓝 p, extend Coordinates (affineVal a s) q = extend Coordinates a.1 q + s • extend Coordinates a.2 q := by
  let e := trivializationAt Coordinates (TangentSpace productModel : Base → Type) p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt' p
  filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
  let L := (e.symmL ℝ q).comp (e.continuousLinearMapAt ℝ p)
  have hl (v : Tangent p) : L v = extend Coordinates v q := by
    simp [L,e.continuousLinearMapAt_apply_of_mem ℝ hp,e.symmL_apply hq,extend,e]
  simp only [← hl,affineVal,map_add,map_smul]

private def SpatialPoly.along {p : Base} (v : AffineTangent p) (a : SpatialPoly p) : SpatialPoly p :=
  .add (a.differentiate _ (extend_smooth_near v.1)) (.scale X (a.differentiate _ (extend_smooth_near v.2)))

private def Models {p : Base} (a : SpatialPoly p) (s : ℝ) (f : Base → ℝ) :=
  f =ᶠ[𝓝 p] fun q => (a.atPoint q).eval s

private theorem Models.along {p : Base} {a : SpatialPoly p} {s f} (h : Models a s f) (v : AffineTangent p) :
    Models (a.along v) s (directional (extend Coordinates (affineVal v s)) f) := by
  filter_upwards [h.eventuallyEq_nhds,extend_affine v s,
    a.eval_derivative _ (extend_smooth_near v.1) s,a.eval_derivative _ (extend_smooth_near v.2) s] with q eq ev e₀ e₁
  rw [directional_congr eq]
  simp only [SpatialPoly.along,SpatialPoly.atPoint,eval_add,eval_mul,eval_X,← e₀,← e₁,directional,ev,map_add,map_smul,smul_eq_mul]

private def basisPair {p : Base} (A : AmbientTensor) (x y : Tangent p) : SpatialPoly p :=
  .atom (ambientPair A (extend Coordinates x) (extend Coordinates y))
    (by filter_upwards [extend_smooth_near x,extend_smooth_near y] with q hx hy using ambientPair_smooth A hx hy)

private def affinePair {p : Base} (A : AmbientTensor) (a b : AffineTangent p) : SpatialPoly p :=
  .add (.add (basisPair A a.1 b.1) (.scale X (.add (basisPair A a.2 b.1) (basisPair A a.1 b.2))))
    (.scale (X^2) (basisPair A a.2 b.2))

private theorem affinePair_models {p : Base} (A : AmbientTensor) (a b : AffineTangent p) (s : ℝ) :
    Models (affinePair A a b) s (ambientPair A (extend Coordinates (affineVal a s)) (extend Coordinates (affineVal b s))) := by
  filter_upwards [extend_affine a s,extend_affine b s] with q ea eb
  simp [affinePair,basisPair,SpatialPoly.atPoint,ambientPair,ea,eb]
  ring

private theorem Models.add {p : Base} {a b : SpatialPoly p} {s f g} (h : Models a s f) (k : Models b s g) :
    Models (.add a b) s (f+g) := by
  filter_upwards [h,k] with q eq er
  simp [SpatialPoly.atPoint,eq,er]

private theorem Models.scale {p : Base} {a : SpatialPoly p} {s f} (h : Models a s f) (c : ℝ) :
    Models (.scale (C c) a) s (c • f) := by
  filter_upwards [h] with q eq
  simp [SpatialPoly.atPoint,eq]

private def gammaPoly {p : Base} (A : AmbientTensor) (u v w : AffineTangent p) : ℝ[X] :=
  ((((affinePair A v w).along u).add ((affinePair A u w).along v)).atPoint p -
    ((affinePair A u v).along w).atPoint p) * C (1/2)

private theorem eval_gammaPoly {p : Base} (A : AmbientTensor) (u v w : AffineTangent p) (s : ℝ) :
    (gammaPoly A u v w).eval s = ambientGamma A (affineVal u s) (affineVal v s) (affineVal w s) := by
  simp only [gammaPoly,SpatialPoly.atPoint,eval_mul,eval_sub,eval_add,eval_C,ambientGamma,
    ← ((affinePair_models A v w s).along u).self_of_nhds,← ((affinePair_models A u w s).along v).self_of_nhds,
    ← ((affinePair_models A u v s).along w).self_of_nhds]
  ring

private def secondPoly {p : Base} (A : AmbientTensor) (u v : AffineTangent p) : ℝ[X] :=
  let f := ((affinePair A v u).along v).add (((affinePair A v v).along u).scale (C (-1/2)))
  let g := ((affinePair A u u).along v).scale (C (1/2))
  (f.along u).atPoint p - (g.along v).atPoint p

private theorem eval_secondPoly {p : Base} (A : AmbientTensor) (u v : AffineTangent p) (s : ℝ) :
    (secondPoly A u v).eval s = ambientSecond A (affineVal u s) (affineVal v s) := by
  have f := (((affinePair_models A v u s).along v).add (((affinePair_models A v v s).along u).scale (-1/2))).along u
  have g := (((affinePair_models A u u s).along v).scale (1/2)).along v
  simp only [secondPoly,eval_sub,← f.self_of_nhds,← g.self_of_nhds,ambientSecond]
  congr 2 <;> funext q <;> simp <;> ring

private def tensorCubic (a : Fin 4 → ℝ[X]) := a 0 + X*a 1 + X^2*a 2 + X^3*a 3

private theorem eval_tensorCubic (a : Fin 4 → ℝ[X]) (s : ℝ) :
    (tensorCubic a).eval s = cubicValue s (fun i => (a i).eval s) := by simp [tensorCubic,cubicValue]

/-- Cleared curvature numerator along simultaneous affine tilts of the two
generators. Its spatial inputs are metric coefficients and their first two
directional derivatives, evaluated at the one base point. -/
def affineNumeratorPolynomial {p : Base} (A : Fin 4 → AmbientTensor) (u v : AffineTangent p) : ℝ[X] :=
  let b := coordinateFrame p
  let G := metricPolynomial A b
  let J (x y : AffineTangent p) (i : Fin 4) := tensorCubic (fun k => gammaPoly (A k) x y (b i,0))
  tensorCubic (fun k => secondPoly (A k) u v) * G.det +
    J u v ⬝ᵥ G.adjugate *ᵥ J u v - J u u ⬝ᵥ G.adjugate *ᵥ J v v

theorem affineNumerator_eval {p : Base} (A : Fin 4 → AmbientTensor) (u v : AffineTangent p) (s : ℝ) :
    (affineNumeratorPolynomial A u v).eval s = (numeratorPolynomial A (coordinateFrame p)
      (u.1+s • u.2) (v.1+s • v.2)).eval s := by
  rw [eval_numeratorPolynomial]
  simp [affineNumeratorPolynomial,dotProduct,mulVec,eval_finsetSum,eval_tensorCubic,
    eval_gammaPoly,eval_secondPoly,affineVal]

private theorem id_mul_deriv {g : ℝ → ℝ} (n : ℕ) (hg : ContDiffAt ℝ (↑(n+1) : ℕ∞ω) g 0) :
    iteratedDeriv (n+1) (fun x => x*g x) 0 = (n+1)*iteratedDeriv n g 0 := by
  have h := iteratedDeriv_fun_mul (x := (0:ℝ)) (n := n+1)
    (f := fun x : ℝ => x^1) (g := g) (by fun_prop) hg
  simp only [pow_one] at h
  rw [h, Finset.sum_eq_single 1]
  · simp
  · intro i _ hi
    have hz : iteratedDeriv i (fun x : ℝ => x) 0 = 0 := by
      rcases i with _ | i
      · simp
      have hi : 1 < i+1 := by omega
      simpa only [pow_one] using (show iteratedDeriv (i+1) (fun x : ℝ => x^1) 0 = 0 by
        rw [iteratedDeriv_pow,Nat.descFactorial_eq_zero_iff_lt.mpr hi]; simp)
    simp [hz]
  · simp

/-- The coefficient produced by exact division equals the normalized
derivative of the rational curvature expression at every order. -/
theorem quotientCoeff_eq_derivative (N D : ℝ[X]) (hd : D.eval 0 ≠ 0) (n : ℕ) :
    iteratedDeriv n (fun s => N.eval s / D.eval s) 0 / n.factorial =
      quotientCoeff (residual N D n) D := by
  have hD : D.coeff 0 ≠ 0 := by simpa [coeff_zero_eq_eval_zero] using hd
  have shift (M : ℝ[X]) (j : ℕ) : residual (quotientNext M D) D j = residual M D (j+1) := by
    induction j with
    | zero => rfl
    | succ j ih => exact congrArg (fun z => quotientNext z D) ih
  induction n generalizing N with
  | zero => simp [quotientCoeff,residual,coeff_zero_eq_eval_zero]
  | succ n ih =>
    let B := quotientNext N D
    let f (s : ℝ) := B.eval s / D.eval s
    have smooth (P : ℝ[X]) : ContDiff ℝ ∞ (fun s => P.eval s) := by
      induction P using Polynomial.induction_on' with
      | add f g h k => simpa only [eval_add] using h.add k
      | monomial i x => simp only [eval_monomial]; exact contDiff_const.mul (contDiff_id.pow _)
    have hf : ContDiffAt ℝ (↑(n+1) : ℕ∞ω) f 0 :=
      (((smooth B).contDiffAt.div (smooth D).contDiffAt hd).of_le (by simp))
    have eq : (fun s => N.eval s / D.eval s) =ᶠ[𝓝 0] fun s => quotientCoeff N D + s*f s := by
      filter_upwards [D.continuous.continuousAt.eventually_ne hd] with s hs
      have e := congrArg (Polynomial.eval s) (quotient_step N D hD)
      simp only [eval_add,eval_mul,eval_C,eval_X] at e
      dsimp [f,B]
      field_simp
      linarith only [e]
    rw [eq.iteratedDeriv_eq,iteratedDeriv_const_add (Nat.succ_pos n),id_mul_deriv n hf,← shift]
    have h := ih B
    change iteratedDeriv n f 0 / _ = _ at h
    rw [← h,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    field_simp

/-- The moving-plane coefficients from the minimum theorem, expressed by
finite polynomial division along the chosen four-coordinate ray. -/
theorem graph_coeff_eq_quotient (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) (p : Base)
    (U V N₁ N₂ : Tangent p) (z : Fin 4 → ℝ) (n : ℕ) :
    let A := paperCoefficients t ht χ
    let D := (metricPolynomial A (coordinateFrame p)).det
    let N := affineNumeratorPolynomial A (U,z 0 • N₁ + z 1 • N₂) (V,z 2 • N₁ + z 3 • N₂)
    UniformTube.coeff (graphNumerator A U V N₁ N₂) n 0 z = quotientCoeff (residual N D n) D := by
  intro A D N
  have hd : D.eval 0 ≠ 0 := by
    have h := ((evalRingHom (0:ℝ)).map_det (metricPolynomial A (coordinateFrame p))).trans
      (congrArg det (eval_metricPolynomial_zero A (coordinateFrame p)))
    have e : ambientGram (A 0) (coordinateFrame p) = gramMatrix (backgroundMetric t ht) (coordinateFrame p) := rfl
    exact (h.trans (congrArg det e)).trans_ne (gram_isUnit _ _).ne_zero
  have eq : (fun s : ℝ => graphNumerator A U V N₁ N₂ (0,s • z,s)) =
      fun s => N.eval s / D.eval s := by
    funext s
    simp only [graphNumerator,tiltedPair,TangentPair.numerator,N,affineNumerator_eval,
      Pi.smul_apply,smul_eq_mul,smul_add,smul_smul,add_assoc,D]
  change iteratedDeriv n (fun s : ℝ => graphNumerator A U V N₁ N₂ (0,s • z,s)) 0 / _ = _
  rw [eq]
  exact quotientCoeff_eq_derivative N D hd n

/-- Zero tilt recovers the previously computed fixed-plane coefficients. -/
theorem graph_coeff_zero_tilt (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) {p : Base}
    (U V N₁ N₂ : Tangent p) (n : ℕ) :
    let A := paperCoefficients t ht χ
    UniformTube.coeff (graphNumerator A U V N₁ N₂) n 0 0 = sectionalCoeff A (coordinateFrame p) U V n := by
  intro A
  rw [graph_coeff_eq_quotient]
  have h : affineNumeratorPolynomial A (U,0) (V,0) = numeratorPolynomial A (coordinateFrame p) U V := by
    apply Polynomial.funext
    intro s
    simpa using affineNumerator_eval A (U,0) (V,0) s
  simp only [Pi.zero_apply,zero_smul,add_zero,h,sectionalCoeff,A]

end
end LocalHopf.SphereProduct
