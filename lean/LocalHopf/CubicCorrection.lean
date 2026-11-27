import LocalHopf.GraphMinimum
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # The effect of changing the cubic metric tensor on a moving plane -/

namespace LocalHopf.SphereProduct
open Matrix Polynomial Filter
open scoped Topology ContDiff Manifold
noncomputable section

local instance (p : Base) : NormedAddCommGroup (Tangent p) :=
  inferInstanceAs (NormedAddCommGroup Coordinates)
local instance (p : Base) : NormedSpace ℝ (Tangent p) := inferInstanceAs (NormedSpace ℝ Coordinates)

private def curve (k s : ℝ) : ℝ × ℝ := (s,k*s^3)

private theorem cubic_chain (F : ℝ × ℝ → ℝ) (hf : ContDiffAt ℝ 3 F (0,0)) :
    iteratedDeriv 2 (F ∘ curve 1) 0 = iteratedDeriv 2 (F ∘ curve 0) 0 ∧
    (iteratedDeriv 3 (F ∘ curve 1) 0 - iteratedDeriv 3 (F ∘ curve 0) 0)/6 =
      deriv (fun r => F (0,r)) 0 := by
  have first (k : ℝ) : deriv (curve k) = fun s => (1,k*(3*s^2)) := by
    funext s
    change deriv (fun r : ℝ => (r,k*r^3)) s = _
    simpa using ((hasDerivAt_id' s).prodMk (((hasDerivAt_id' s).pow 3).const_mul k)).deriv
  have second (k : ℝ) : iteratedDeriv 2 (curve k) = fun s => (0,k*(6*s)) := by
    rw [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,first]
    funext s
    rw [show deriv (fun r : ℝ => ((1:ℝ),k*(3*r^2))) s = _ from
      ((hasDerivAt_const s (1:ℝ)).prodMk ((((hasDerivAt_id' s).pow 2).const_mul 3).const_mul k)).deriv]
    congr 1; ring
  have third (k : ℝ) : iteratedDeriv 3 (curve k) = fun _ => (0,k*6) := by
    rw [show 3=2+1 by rfl,iteratedDeriv_succ,second]
    funext s
    simpa using ((hasDerivAt_const s (0:ℝ)).prodMk (((hasDerivAt_id' s).const_mul 6).const_mul k)).deriv
  have reg (k : ℝ) : ContDiffAt ℝ 3 (curve k) 0 := by unfold curve; fun_prop
  have atzero (k : ℝ) : curve k 0 = (0,0) := by simp [curve]
  have r (k : ℝ) : ContDiffAt ℝ 3 F (curve k 0) := atzero k ▸ hf
  constructor
  · rw [iteratedDeriv_vcomp_two ((r 1).of_le (by norm_num)) ((reg 1).of_le (by norm_num)),
      iteratedDeriv_vcomp_two ((r 0).of_le (by norm_num)) ((reg 0).of_le (by norm_num))]
    simp [first,second,atzero]
  · rw [iteratedDeriv_vcomp_three (r 1) (reg 1),iteratedDeriv_vcomp_three (r 0) (reg 0)]
    have ed := ((hf.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      ((hasDerivAt_const (0:ℝ) (0:ℝ)).prodMk (hasDerivAt_id' (0:ℝ)))).deriv
    rw [show deriv (fun r => F (0,r)) 0 = _ from ed]
    simp only [first,second,third,atzero,zero_pow (by decide : 2 ≠ 0),mul_zero,one_mul,zero_mul,
      show ((0,0) : ℝ × ℝ) = 0 from rfl,map_zero,add_zero]
    rw [show ((0,6) : ℝ × ℝ) = (6:ℝ) • (0,1) by simp,map_smul]
    simp only [smul_eq_mul]
    ring

private def weightedJet {p : Base} (L : (AmbientTensor → ℝ) → ℝ) (u v : Tangent p) : ℝ :=
  let b := coordinateFrame p
  let G : Matrix (Fin 4) (Fin 4) ℝ := fun i j => L (fun H => ambientGram H b i j)
  let J (x y : Tangent p) (i : Fin 4) := L (fun H => ambientGamma H x y (b i))
  (L (fun H => ambientSecond H u v)*G.det + J u v ⬝ᵥ G.adjugate *ᵥ J u v -
    J u u ⬝ᵥ G.adjugate *ᵥ J v v)/G.det

private def ordinary (A : Fin 4 → AmbientTensor) (s : ℝ) (f : AmbientTensor → ℝ) :=
  cubicValue s (fun i => f (A i))

private theorem ordinary_eq {p : Base} (A : Fin 4 → AmbientTensor) (s : ℝ) (u v : Tangent p) :
    weightedJet (ordinary A s) u v = (TangentPair.mk p u v).numerator A s := by
  let b := coordinateFrame p
  let G := metricPolynomial A b
  have e : G.map (evalRingHom s) = fun i j => ordinary A s (fun H => ambientGram H b i j) := by
    ext i j
    let v := fun k => ambientGram (A k) b i j
    change (C (v 0) + X*C (v 1) + X^2*C (v 2) + X^3*C (v 3)).eval s = cubicValue s v
    simp [cubicValue]; ring
  have hd := (evalRingHom s).map_det G
  have ha := (evalRingHom s).map_adjugate G
  simp only [RingHom.mapMatrix_apply] at hd ha
  change _ = (numeratorPolynomial A b u v).eval s / G.det.eval s
  rw [eval_numeratorPolynomial]
  unfold weightedJet
  change _ = (_*G.det.eval s + _ ⬝ᵥ G.adjugate.map (evalRingHom s) *ᵥ _ -
    _ ⬝ᵥ G.adjugate.map (evalRingHom s) *ᵥ _)/G.det.eval s
  rw [show G.det.eval s = _ from hd,ha,e]
  rfl

private def mixed (A B : Fin 4 → AmbientTensor) (q : ℝ × ℝ) (f : AmbientTensor → ℝ) :=
  ordinary A q.1 f + q.2*(f (B 3)-f (A 3))

private theorem mixed_reg (A B : Fin 4 → AmbientTensor) {p : Base} (u v du dv : Tangent p)
    (hd : (ambientGram (A 0) (coordinateFrame p)).det ≠ 0) :
    ContDiffAt ℝ 3 (fun q : ℝ × ℝ => weightedJet (mixed A B q) (u+q.1 • du) (v+q.1 • dv)) (0,0) := by
  let b := coordinateFrame p
  let L := mixed A B
  let G (q : ℝ × ℝ) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => L q (fun H => ambientGram H b i j)
  have smoothL (f : AmbientTensor → ℝ × ℝ → ℝ) (hf : ∀ H, ContDiff ℝ ∞ (f H)) :
      ContDiff ℝ ∞ (fun q => L q (fun H => f H q)) := by
    dsimp [L,mixed,ordinary,cubicValue]
    fun_prop (disch := exact hf _)
  have g (i j : Fin 4) : ContDiff ℝ ∞ (fun q => G q i j) := smoothL _ (fun _ => contDiff_const)
  have smoothDet {n : Type} [Fintype n] [DecidableEq n] (M : ℝ × ℝ → Matrix n n ℝ)
      (hM : ∀ i j, ContDiff ℝ ∞ (fun q => M q i j)) : ContDiff ℝ ∞ (fun q => (M q).det) := by
    simp only [Matrix.det_apply']
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)
  have adj (i j : Fin 4) : ContDiff ℝ ∞ (fun q => (G q).adjugate i j) := by
    simp only [adjugate_fin_succ_eq_det_submatrix]
    exact contDiff_const.mul (smoothDet (fun q => (G q).submatrix j.succAbove i.succAbove) (fun a c => g _ _))
  let J (X Y : ℝ × ℝ → Tangent p) (i : Fin 4) (q : ℝ × ℝ) := L q (fun H => ambientGamma H (X q) (Y q) (b i))
  have sj {X Y : ℝ × ℝ → Tangent p} (hx : ContDiff ℝ ∞ X) (hy : ContDiff ℝ ∞ Y) (i : Fin 4) :
      ContDiff ℝ ∞ (J X Y i) := smoothL _ (fun H => smooth_ambientGamma (p := p) H hx hy (contDiff_const (c := b i)))
  let pair (a b : Fin 4 → ℝ × ℝ → ℝ) (q : ℝ × ℝ) := (fun i => a i q) ⬝ᵥ (G q).adjugate *ᵥ (fun j => b j q)
  have sp {a b : Fin 4 → ℝ × ℝ → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i)) (hb : ∀ i, ContDiff ℝ ∞ (b i)) :
      ContDiff ℝ ∞ (pair a b) := by
    unfold pair dotProduct mulVec
    exact ContDiff.sum fun i _ => (ha i).mul (ContDiff.sum fun j _ => (adj i j).mul (hb j))
  let X (q : ℝ × ℝ) := u+q.1 • du
  let Y (q : ℝ × ℝ) := v+q.1 • dv
  have sx : ContDiff ℝ ∞ X := by dsimp [X]; fun_prop
  have sy : ContDiff ℝ ∞ Y := by dsimp [Y]; fun_prop
  have hS := smoothL (fun H q => ambientSecond H (X q) (Y q)) (fun H => smooth_ambientSecond (p := p) H sx sy)
  have hD := smoothDet G g
  have he : G (0,0) = ambientGram (A 0) b := by ext; simp [G,L,mixed,ordinary,cubicValue]
  have hn : (G (0,0)).det ≠ 0 := by rw [he]; exact hd
  have result := (((hS.mul hD).add (sp (sj sx sy) (sj sx sy))).sub (sp (sj sx sx) (sj sy sy))).contDiffAt.div
    hD.contDiffAt hn
  exact result.of_le (by simp)

private theorem graph_cubic_variation (t : ℝ) (ht : 0 ≤ t) (χ ψ : Scalar) {p : Base}
    (U V N₁ N₂ : Tangent p) :
    let A := paperCoefficients t ht χ
    let B := paperCoefficients t ht ψ
    let Q := fun H => graphCoefficient H U V N₁ N₂
    Q B 2 = Q A 2 ∧ ∀ z, Q B 3 z - Q A 3 z =
      deriv (fun r => weightedJet (mixed A B (0,r)) U V) 0 := by
  intro A B Q
  have atTilt (z : Fin 4 → ℝ) :
      Q B 2 z = Q A 2 z ∧ Q B 3 z - Q A 3 z =
        deriv (fun r => weightedJet (mixed A B (0,r)) U V) 0 := by
    let du := z 0 • N₁ + z 1 • N₂
    let dv := z 2 • N₁ + z 3 • N₂
    let F (q : ℝ × ℝ) := weightedJet (mixed A B q) (U+q.1 • du) (V+q.1 • dv)
    have m₀ (s : ℝ) : mixed A B (curve 0 s) = ordinary A s := by
      funext f; simp [mixed,curve]
    have m₁ (s : ℝ) : mixed A B (curve 1 s) = ordinary B s := by
      funext f
      change cubicValue s (fun i => f (A i)) + 1*s^3*(f (B 3)-f (A 3)) = cubicValue s (fun i => f (B i))
      dsimp [cubicValue,A,B,paperCoefficients]
      ring
    let ray (H : Fin 4 → AmbientTensor) (s : ℝ) := graphNumerator H U V N₁ N₂ (0,s • z,s)
    have eq₀ : F ∘ curve 0 = ray A := by
      funext s
      change weightedJet (mixed A B (curve 0 s)) (U+s • du) (V+s • dv) = _
      rw [m₀,ordinary_eq]
      simp only [ray,graphNumerator,tiltedPair,du,dv,Pi.smul_apply,smul_eq_mul,smul_add,smul_smul,add_assoc]
    have eq₁ : F ∘ curve 1 = ray B := by
      funext s
      change weightedJet (mixed A B (curve 1 s)) (U+s • du) (V+s • dv) = _
      rw [m₁,ordinary_eq]
      simp only [ray,graphNumerator,tiltedPair,du,dv,Pi.smul_apply,smul_eq_mul,smul_add,smul_smul,add_assoc]
    have coeff (φ : Scalar) (n : ℕ) : Q (paperCoefficients t ht φ) n z =
        iteratedDeriv n (ray (paperCoefficients t ht φ)) 0 / n.factorial :=
      (graph_coeff_eq_quotient t ht φ p U V N₁ N₂ z n).symm
    obtain ⟨h₂,h₃⟩ := cubic_chain F (mixed_reg A B U V du dv (gram_isUnit (backgroundMetric t ht) _).ne_zero)
    rw [eq₀,eq₁] at h₂ h₃
    have vert : (fun r => F (0,r)) = fun r => weightedJet (mixed A B (0,r)) U V := by
      funext r; simp [F]
    rw [vert] at h₃
    constructor
    · exact (coeff ψ 2).trans ((congrArg (· / ((2:ℕ).factorial : ℝ)) h₂).trans (coeff χ 2).symm)
    · rw [coeff ψ 3,coeff χ 3]
      norm_num [Nat.factorial] at h₃ ⊢
      linarith
  exact ⟨funext fun z => (atTilt z).1,fun z => (atTilt z).2⟩

/-- Linear conformal variation, represented in the same four coefficient slots
as the cubic paper metrics. -/
def conformalPencil (t : ℝ) (ht : 0 ≤ t) (φ : Scalar) : Fin 4 → AmbientTensor :=
  ![backgroundTensor t ht,thirdOrderTensor t ht φ,thirdOrderTensor t ht 0,thirdOrderTensor t ht 0]

theorem conformalPencil_realized (t : ℝ) (ht : 0 ≤ t) (φ : Scalar) :
    ∀ᶠ r in 𝓝 (0:ℝ), ∃ g : SmoothMetric, Realizes g r (conformalPencil t ht φ) := by
  filter_upwards [eventually_exists_perturbedMetric t ht (thirdOrderTensor t ht φ)
    (thirdOrderTensor t ht 0) (thirdOrderTensor t ht 0)] with r h
  obtain ⟨g,hg⟩ := h
  refine ⟨g,fun p x y => ?_⟩
  rw [hg]
  change backgroundPair p t ht _ _ + _ + _ + _ = ambientBackground t p _ _ + _ + _ + _
  rw [ambientBackground_apply p ht]
  rfl

/-- Changing the cubic potential from zero to φ has the first-order effect of
the actual linear conformal pencil on the fixed plane, independently of the tilt. -/
theorem graph_cubic_pencil (t : ℝ) (ht : 0 ≤ t) (φ : Scalar) {p : Base}
    (U V N₁ N₂ : Tangent p) (z : Fin 4 → ℝ) :
    graphCoefficient (paperCoefficients t ht φ) U V N₁ N₂ 3 z -
      graphCoefficient (paperCoefficients t ht 0) U V N₁ N₂ 3 z =
        deriv ((TangentPair.mk p U V).numerator (conformalPencil t ht φ)) 0 := by
  refine ((graph_cubic_variation t ht 0 φ U V N₁ N₂).2 z).trans ?_
  apply congrArg (fun F : ℝ → ℝ => deriv F 0)
  funext r
  rw [← ordinary_eq]
  let Z := thirdOrderTensor t ht 0
  have zero (q : Base) (X Y : Cheeger.V) : Z.form q X Y = 0 := by
    change (2*Profiles.hh t*(0:Scalar) q)*_ = 0
    simp
  have zp (X Y : Field) : ambientPair Z X Y = fun _ => 0 := funext fun _ => zero _ _ _
  have dir (X : Field) : directional X (fun _ => (0:ℝ)) = fun _ => 0 := by
    funext q
    simp [directional,mvfderiv_const]
  have zg (x y w : Tangent p) : ambientGamma Z x y w = 0 := by simp [ambientGamma,zp,dir]
  have zs : ambientSecond Z U V = 0 := by simp [ambientSecond,zp,dir]
  have val (f : AmbientTensor → ℝ) (hf : f Z = 0) :
      mixed (paperCoefficients t ht 0) (paperCoefficients t ht φ) (0,r) f =
        ordinary (conformalPencil t ht φ) r f := by
    change cubicValue 0 _ + r*(f (thirdOrderTensor t ht φ)-f Z) = cubicValue r _
    simp [cubicValue,paperCoefficients,conformalPencil,Z] at hf ⊢
    rw [hf]; ring
  unfold weightedJet
  let b := coordinateFrame p
  have gram (i j : Fin 4) := val (fun H => ambientGram H b i j) (zero _ _ _)
  have gam (x y : Tangent p) (i : Fin 4) := val (fun H => ambientGamma H x y (b i)) (zg x y _)
  have sec := val (fun H => ambientSecond H U V) zs
  dsimp only
  simp only [gram,gam,sec,b]

/-- Changing the cubic metric tensor has the same cubic effect at every tilt.
The entire quadratic polynomial in the tilt, hence its stationary point, is unchanged. -/
theorem graph_cubic_correction (t : ℝ) (ht : 0 ≤ t) (χ ψ : Scalar) {p : Base}
    (U V N₁ N₂ : Tangent p) :
    let A := paperCoefficients t ht χ
    let B := paperCoefficients t ht ψ
    let Q := fun H => graphCoefficient H U V N₁ N₂
    Q B 2 = Q A 2 ∧ ∀ z, Q B 3 z - Q A 3 z =
      sectionalCoeff B (coordinateFrame p) U V 3 - sectionalCoeff A (coordinateFrame p) U V 3 := by
  intro A B Q
  obtain ⟨same,atTilt⟩ := graph_cubic_variation t ht χ ψ U V N₁ N₂
  refine ⟨same,fun z => ?_⟩
  have zero (φ : Scalar) : Q (paperCoefficients t ht φ) 3 0 =
      sectionalCoeff (paperCoefficients t ht φ) (coordinateFrame p) U V 3 :=
    (graph_coeff_eq_quotient t ht φ p U V N₁ N₂ 0 3).symm.trans (graph_coeff_zero_tilt t ht φ U V N₁ N₂ 3)
  exact (atTilt z).trans ((atTilt 0).symm.trans (congrArg₂ (· - ·) (zero ψ) (zero χ)))

/-- Linearized fixed-plane numerator for the prescribed change of potential.
The three kinds of terms come from the scalar second derivatives, the two
first-kind symbols, and the inverse Gram matrix. -/
def conformalResponse (t : ℝ) (ht : 0 ≤ t) (χ ψ : Scalar) {p : Base} (U V : Tangent p) : ℝ :=
  let A := backgroundTensor t ht
  let B := thirdOrderTensor t ht χ
  let C := thirdOrderTensor t ht ψ
  let b := coordinateFrame p
  let J (H : AmbientTensor) (x y : Tangent p) (i : Fin 4) := ambientGamma H x y (b i)
  let K (x y : Tangent p) := J C x y - J B x y
  let H := (ambientGram A b)⁻¹
  let k := 2*Profiles.hh t*(ψ p-χ p)
  let change (x y z w : Tangent p) := K x y ⬝ᵥ H *ᵥ J A z w +
    J A x y ⬝ᵥ H *ᵥ K z w - k*(J A x y ⬝ᵥ H *ᵥ J A z w)
  ambientSecond C U V - ambientSecond B U V + change U V U V - change U U V V

/-- On the concrete sphere product, changing the cubic conformal perturbation
has this explicit spatial two-jet response, for every tilt at every base point. -/
theorem graph_conformal_response (t : ℝ) (ht : 0 ≤ t) (χ ψ : Scalar) {p : Base}
    (U V N₁ N₂ : Tangent p) (z : Fin 4 → ℝ) :
    graphCoefficient (paperCoefficients t ht ψ) U V N₁ N₂ 3 z -
      graphCoefficient (paperCoefficients t ht χ) U V N₁ N₂ 3 z = conformalResponse t ht χ ψ U V := by
  let A := paperCoefficients t ht χ
  let B := paperCoefficients t ht ψ
  let b := coordinateFrame p
  let G := ambientGram (A 0) b
  let H := G⁻¹
  let k := 2*Profiles.hh t*(ψ p-χ p)
  let J (x y : Tangent p) (i : Fin 4) := ambientGamma (A 0) x y (b i)
  let D (x y : Tangent p) (i : Fin 4) := ambientGamma (B 3) x y (b i) - ambientGamma (A 3) x y (b i)
  let L (r : ℝ) := mixed A B (0,r)
  let pair (a d : Fin 4 → ℝ) := a ⬝ᵥ H *ᵥ d
  let T (r : ℝ) (x y : Tangent p) := J x y + r • D x y
  let coeff (r : ℝ) (x y z w : Tangent p) := pair (T r x y) (T r z w)
  have gram (φ : Scalar) (i j : Fin 4) : ambientGram (thirdOrderTensor t ht φ) b i j =
      (2*Profiles.hh t*φ p)*G i j := by rfl
  have G_eq (r : ℝ) : (fun i j : Fin 4 => L r (fun F => ambientGram F b i j)) = (1+r*k) • G := by
    ext i j
    simp only [L,mixed,ordinary,cubicValue,zero_smul,zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 3 ≠ 0),add_zero]
    change G i j + r*(ambientGram (thirdOrderTensor t ht ψ) b i j -
      ambientGram (thirdOrderTensor t ht χ) b i j) = (1+r*k)*G i j
    rw [gram,gram]; dsimp only [k]; ring
  let S := ambientSecond (A 0) U V
  let dS := ambientSecond (B 3) U V - ambientSecond (A 3) U V
  let f (r : ℝ) := S + r*dS + (coeff r U V U V - coeff r U U V V)/(1+r*k)
  have det : G.det ≠ 0 := (gram_isUnit (backgroundMetric t ht) b).ne_zero
  have eq : (fun r => weightedJet (L r) U V) =ᶠ[𝓝 0] f := by
    have nz : ∀ᶠ r in 𝓝 (0:ℝ), 1+r*k ≠ 0 :=
      (show ContinuousAt (fun r : ℝ => 1+r*k) 0 by fun_prop).eventually_ne (by norm_num)
    filter_upwards [nz] with r hr
    have sym (x y : Tangent p) : (fun i => L r (fun F => ambientGamma F x y (b i))) = T r x y := by
      funext i; simp [L,mixed,ordinary,cubicValue,T,D,J]
    have sec : L r (fun F => ambientSecond F U V) = S + r*dS := by simp [L,mixed,ordinary,cubicValue,S,dS]
    unfold weightedJet
    dsimp only
    rw [G_eq,sym,sym,sym,sec,det_smul,adjugate_smul]
    simp only [f,coeff,pair,H,Matrix.inv_def,Ring.inverse_eq_inv,smul_mulVec,dotProduct_smul,
      smul_eq_mul,Fintype.card_fin]
    norm_num only [Nat.reduceSub]
    field_simp; ring
  have pj (a b d e : Fin 4 → ℝ) (r : ℝ) :
      pair (a + r • d) (b + r • e) = pair a b + r*(pair d b + pair a e) + r^2*pair d e := by
    simp only [pair,mulVec_add,mulVec_smul,add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    ring
  have dp (x y z w : Tangent p) : HasDerivAt (fun r => coeff r x y z w)
      (pair (D x y) (J z w) + pair (J x y) (D z w)) 0 := by
    simp only [coeff,T,pj]
    convert (((hasDerivAt_const (0:ℝ) (pair (J x y) (J z w))).add
      ((hasDerivAt_id' (0:ℝ)).mul_const _)).add (((hasDerivAt_id' (0:ℝ)).pow 2).mul_const _)) using 1; simp
  have df := ((hasDerivAt_const (0:ℝ) S).add ((hasDerivAt_id' (0:ℝ)).mul_const dS)).add
    (((dp U V U V).sub (dp U U V V)).div ((hasDerivAt_const (0:ℝ) (1:ℝ)).add
      ((hasDerivAt_id' (0:ℝ)).mul_const k)) (by simp))
  rw [(graph_cubic_variation t ht χ ψ U V N₁ N₂).2 z,eq.deriv_eq]
  change deriv f 0 = _
  rw [show deriv f 0 = _ from df.deriv]
  simp only [Pi.add_apply,Pi.sub_apply,coeff,T,zero_smul,add_zero,zero_add,one_mul,zero_mul,mul_one,one_pow,div_one]
  change _ = dS + (pair (D U V) (J U V) + pair (J U V) (D U V) - k * pair (J U V) (J U V)) -
    (pair (D U U) (J V V) + pair (J U U) (D V V) - k * pair (J U U) (J V V))
  ring


end
end LocalHopf.SphereProduct
