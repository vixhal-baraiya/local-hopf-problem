import LocalHopf.ChartRotations
import LocalHopf.InverseJet

/-! All sixteen second-order jets of the intrinsic background inverse Gram
matrix in the verifier's longitude-height coordinates. -/
namespace LocalHopf.SphereProduct.JetChart
open LongitudeHeight Real Filter Matrix
open scoped Topology ContDiff
noncomputable section

/-- A straight line in the script's x,y,z₁,z₂ coordinates. -/
def line (a b h k z : ℝ) : Params := ((a*z,b*z),h*z,k*z)

private def pack (u v h k : ℝ) : Fin 4 → ℝ := ![(u+v)/2,(v-u)/2,h,k]

/-- The rotation coordinate jets at the center. Row 0 is the value, row 1 is
the linear coefficient and row 2 is half the second derivative. -/
def rotationTaylor (U V : R3) (a b h k : ℝ) : Fin 3 → Fin 4 → ℝ :=
  let l := a-b
  let m := a+b
  ![pack (U 2) (V 2) (-(U 1)) (-(V 1)),
    pack (-h*U 0) (-k*V 0) (l*U 0) (m*V 0),
    pack (-h*l*U 1) (-k*m*V 1) ((l^2+h^2)/2*U 1) ((m^2+k^2)/2*V 1)]

theorem rotationCoordinate_jet (U V : R3) (a b h k : ℝ) (i : Fin 4) :
    let T := rotationTaylor U V a b h k
    SpatialJet (fun z => parameterBasis.equivFun (rotationCoordinates U V (line a b h k z)) i)
      (T 0 i) (T 1 i) (T 2 i) := by
  intro T
  let l := a-b
  let m := a+b
  have p := rotation_jets U 0 l h
  have q := rotation_jets V 0 m k
  let l₁ := fun z => longitudeSpeed U (l*z) (h*z)
  let l₂ := fun z => longitudeSpeed V (m*z) (k*z)
  let h₁ := fun z => heightSpeed U (l*z) (h*z)
  let h₂ := fun z => heightSpeed V (m*z) (k*z)
  have pl : SpatialJet l₁ (U 2) (-h*U 0) (-h*l*U 1) := by
    simpa [l₁,longitudeSpeed,neg_mul] using p.1
  have ql : SpatialJet l₂ (V 2) (-k*V 0) (-k*m*V 1) := by
    simpa [l₂,longitudeSpeed,neg_mul] using q.1
  have ph : SpatialJet h₁ (-(U 1)) (l*U 0) ((l^2+h^2)/2*U 1) := by
    simpa [h₁,heightSpeed] using p.2.1
  have qh : SpatialJet h₂ (-(V 1)) (m*V 0) ((m^2+k^2)/2*V 1) := by
    simpa [h₂,heightSpeed] using q.2.1
  have val (z : ℝ) : parameterBasis.equivFun (rotationCoordinates U V (line a b h k z)) =
      pack (l₁ z) (l₂ z) (h₁ z) (h₂ z) := by
    rw [parameterBasis_coordinates]
    simp only [rotationCoordinates,line,l₁,l₂,h₁,h₂,l,m,sub_mul,add_mul,pack]
  simp only [val]
  fin_cases i
  · change SpatialJet (fun z => (l₁ z+l₂ z)/2) _ _ _
    simpa [T,rotationTaylor,pack,div_eq_mul_inv,mul_comm _ (2:ℝ)⁻¹,l,m] using jet_scale (1/2) (jet_add pl ql)
  · change SpatialJet (fun z => (l₂ z-l₁ z)/2) _ _ _
    simpa [T,rotationTaylor,pack,div_eq_mul_inv,mul_comm _ (2:ℝ)⁻¹,l,m] using jet_scale (1/2) (jet_sub ql pl)
  · exact ph
  · exact qh

/-- The full calculation uses the components of each fixed axis in the two
oriented sphere frames. This also covers parallel and antiparallel sphere points. -/
theorem rotationEntry_jet (v : FlatLocus.Representative) (a b h k : ℝ) (i : Fin 4) (j : Fin 3) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let axis := WithLp.toLp 2 (Pi.single j (1:ℝ))
    let T := rotationTaylor (r.symm axis).ofLp (s.symm axis).ofLp a b h k
    SpatialJet (fun z => rotationEntry r s (line a b h k z) i j) (T 0 i) (T 1 i) (T 2 i) := by
  intro r s axis T
  have sl : Continuous (line a b h k) := by unfold line; fun_prop
  have zero : line a b h k 0 = 0 := by simp [line]
  have near := sl.continuousAt.preimage_mem_nhds ((coreChart v).open_target.mem_nhds
    (show line a b h k 0 ∈ (coreChart v).target from zero ▸ (center v).1))
  apply (rotationCoordinate_jet (r.symm axis).ofLp (s.symm axis).ofLp a b h k i).congr
  filter_upwards [near] with z hz using rotationEntry_adapted v hz i j

private def unitInverse : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1/2,0,0,0],![0,1/2,0,0],![0,0,1,0],![0,0,0,1]]

private def heightTerm (h k : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let m := (h^2+k^2)/4
  let d := (k^2-h^2)/4
  ![![m,d,0,0],![d,m,0,0],![0,0,-h^2,0],![0,0,0,-k^2]]

/-- The three matrix coefficients of the spatial inverse used by the verifier.
The quadratic term includes the product of the two linear rotation terms. -/
def inverseTaylor (v : FlatLocus.Representative) (t a b h k : ℝ) :
    Fin 3 → Matrix (Fin 4) (Fin 4) ℝ :=
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let T (l : Fin 3) :=
    let axis := WithLp.toLp 2 (Pi.single l (1:ℝ))
    rotationTaylor (r.symm axis).ofLp (s.symm axis).ofLp a b h k
  ![fun i j => 2*(unitInverse i j + t*∑ l, T l 0 i*T l 0 j),
    fun i j => 2*(t*∑ l, (T l 1 i*T l 0 j+T l 0 i*T l 1 j)),
    fun i j => 2*(heightTerm h k i j + t*∑ l, (T l 2 i*T l 0 j+T l 1 i*T l 1 j+T l 0 i*T l 2 j))]

theorem jet_sum {ι : Type*} [Fintype ι] {f : ι → ℝ → ℝ} {a b c : ι → ℝ}
    (j : ∀ i, SpatialJet (f i) (a i) (b i) (c i)) :
    SpatialJet (fun z => ∑ i, f i z) (∑ i, a i) (∑ i,b i) (∑ i,c i) := by
  classical
  have h (s : Finset ι) : SpatialJet (fun z => ∑ i ∈ s, f i z) (∑ i ∈ s,a i) (∑ i ∈ s,b i) (∑ i ∈ s,c i) := by
    induction s using Finset.induction_on with
    | empty => simpa using jet_const 0
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using jet_add (j i) ih
  exact h Finset.univ

theorem inverseGram_jet (v : FlatLocus.Representative) (t : ℝ) (ht : 0 ≤ t) (a b h k : ℝ) (i j : Fin 4) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let G (z : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := fun m n =>
      coefficient r s (backgroundMetric t ht) (parameterBasis m) (parameterBasis n) (line a b h k z)
    let T := inverseTaylor v t a b h k
    SpatialJet (fun z => (G z)⁻¹ i j) (T 0 i j) (T 1 i j) (T 2 i j) := by
  intro r s G T
  have round := round_inverse_jets h k i j
  have rot := jet_sum (fun l => jet_mul (rotationEntry_jet v a b h k i l) (rotationEntry_jet v a b h k j l))
  have jet := jet_scale 2 (jet_add round (jet_scale t rot))
  have sl : Continuous (line a b h k) := by unfold line; fun_prop
  have zero : line a b h k 0 = 0 := by simp [line]
  have near := sl.continuousAt.preimage_mem_nhds ((coreChart v).open_target.mem_nhds
    (show line a b h k 0 ∈ (coreChart v).target from zero ▸ (center v).1))
  apply SpatialJet.congr (by simpa [T,inverseTaylor,unitInverse,heightTerm] using jet)
  filter_upwards [near] with z hz using explicit_cometric r s hz t ht i j


private abbrev FourMatrix := Matrix (Fin 4) (Fin 4) ℝ

private def MatrixJet (G : ℝ → FourMatrix) (A B C : FourMatrix) :=
  ∀ i j, SpatialJet (fun z => G z i j) (A i j) (B i j) (C i j)

private theorem jet_product {f g : ℝ → FourMatrix} {A B C U V W : FourMatrix}
    (hf : MatrixJet f A B C) (hg : MatrixJet g U V W) :
    MatrixJet (fun z => f z * g z) (A*U) (B*U+A*V) (C*U+B*V+A*W) := by
  intro i j
  simpa only [Matrix.mul_apply,Matrix.add_apply,Finset.sum_add_distrib] using jet_sum (fun k => jet_mul (hf i k) (hg k j))

private theorem solve_inverse_jet {G : ℝ → FourMatrix} {P Q R : FourMatrix}
    (inv : MatrixJet (fun z => (G z)⁻¹) P Q R)
    (regular : ∀ i j, ContDiffAt ℝ ∞ (fun z => G z i j) 0) (invert : ∀ᶠ z in 𝓝 0, IsUnit (G z).det) :
    let B := G 0
    MatrixJet G B (-(B*Q*B)) (B*Q*B*Q*B-B*R*B) := by
  intro B
  let L : FourMatrix := fun i j => deriv (fun z => G z i j) 0
  let H : FourMatrix := fun i j => iteratedDeriv 2 (fun z => G z i j) 0 / 2
  have js : MatrixJet G B L H := fun i j => ⟨regular i j,rfl,rfl,by dsimp [H]; ring⟩
  have h := jet_product js inv
  have solve (i j : Fin 4) : (L*P+B*Q) i j=0 ∧ (H*P+L*Q+B*R) i j=0 := by
    have eq : (fun _ : ℝ => (1 : FourMatrix) i j) =ᶠ[𝓝 0] fun z => (G z*(G z)⁻¹) i j := by
      filter_upwards [invert] with z hz
      rw [mul_nonsing_inv _ hz]
    have c := (h i j).congr eq
    exact ⟨c.first.symm.trans (jet_const _).first, by linarith only [c.second,(jet_const ((1:FourMatrix) i j)).second]⟩
  have l : L*P+B*Q=0 := Matrix.ext fun i j => (solve i j).1
  have q : H*P+L*Q+B*R=0 := Matrix.ext fun i j => (solve i j).2
  have p : P = (G 0)⁻¹ := Matrix.ext fun i j => (inv i j).value.symm
  have pi : P*B=1 := p ▸ nonsing_inv_mul _ invert.self_of_nhds
  have lin := congrArg (fun m : FourMatrix => m*B) l
  have quad := congrArg (fun m : FourMatrix => m*B) q
  simp only [add_mul,mul_assoc L P,mul_assoc H P,pi,mul_one,zero_mul] at lin quad
  have e : L = -(B*Q*B) := eq_neg_of_add_eq_zero_left lin
  rw [e] at quad
  have f : H = B*Q*B*Q*B-B*R*B := by
    simp only [neg_mul] at quad
    calc
      H = (H + -(B*Q*B*Q*B) + B*R*B) + (B*Q*B*Q*B-B*R*B) := by abel
      _ = _ := by rw [quad,zero_add]
  rwa [←e,←f]

/-- The two-jet of the actual covariant background matrix, with its constant
matrix given by `metric_at_center`. It includes every mixed spatial derivative
by polarization of the arbitrary direction (a,b,h,k). -/
theorem metricGram_jet (v : FlatLocus.Representative) (t : ℝ) (ht : 0 ≤ t) (a b h k : ℝ) (i j : Fin 4) :
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let G (z : ℝ) : FourMatrix := fun m n =>
      coefficient r s (backgroundMetric t ht) (parameterBasis m) (parameterBasis n) (line a b h k z)
    let B := G 0
    let Q := inverseTaylor v t a b h k 1
    let R := inverseTaylor v t a b h k 2
    SpatialJet (fun z => G z i j) (B i j) (-(B*Q*B) i j) ((B*Q*B*Q*B-B*R*B) i j) := by
  intro r s G B Q R
  have smooth : ContDiff ℝ ∞ (line a b h k) := by unfold line; fun_prop
  have zero : line a b h k 0=0 := by simp [line]
  have inside : line a b h k 0 ∈ (chart r s).target := zero ▸ (center v).1
  have near := smooth.continuous.continuousAt.preimage_mem_nhds ((chart r s).open_target.mem_nhds inside)
  have reg (i j : Fin 4) : ContDiffAt ℝ ∞ (fun z => G z i j) 0 :=
    (tensor_smooth r s (backgroundTensor t ht) (parameterBasis i) (parameterBasis j) inside).comp
      (f := line a b h k) 0 smooth.contDiffAt
  have unit : ∀ᶠ z in 𝓝 0, IsUnit (G z).det := by
    filter_upwards [near] with z hz
    obtain ⟨frame,base,_⟩ := chart_cometric r s hz t ht
    have e : G z = gramMatrix (backgroundMetric t ht) frame := by
      ext i j
      change _ = (backgroundMetric t ht).inner _ (frame i) (frame j)
      rw [base,base]; rfl
    rw [e]; exact gram_isUnit _ _
  exact solve_inverse_jet (G := G) (inverseGram_jet v t ht a b h k) reg unit i j

private def relative (c s : ℝ) (x : R3) : R3 :=
  ![c*x 0+s*x 1,-s*x 0+c*x 1,x 2]

theorem align_coordinates (n p : FlatLocus.UnitVector) (hn : n.val ⬝ᵥ p.val = 0) (x : E3) :
    ((align n p hn).symm x).ofLp = ![p.val ⬝ᵥ x.ofLp,(n.val ⨯₃ p.val) ⬝ᵥ x.ofLp,n.val ⬝ᵥ x.ofLp] := by
  have coord (i : Fin 3) : ((align n p hn).symm x).ofLp i = (axes n p i).ofLp ⬝ᵥ x.ofLp := by
    have E := (axesBasis n p hn).repr_apply_apply x i
    have A : axesBasis n p hn i = axes n p i := (OrthonormalBasis.repr_symm_single ..).symm.trans (axesBasis_apply n p hn i)
    rw [A,EuclideanSpace.inner_eq_star_dotProduct] at E
    simpa only [align,LinearIsometryEquiv.symm_symm,RCLike.star_def,star_trivial,dotProduct_comm x.ofLp] using E
  ext i
  fin_cases i <;> exact coord _

private theorem relative_coordinates (v : FlatLocus.Representative) (x : E3) :
    let n := v.val.1.val
    let p := v.val.2.1.val
    let q := v.val.2.2.val
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    (s.symm x).ofLp = relative (p ⬝ᵥ q) ((n ⨯₃ p) ⬝ᵥ q) (r.symm x).ofLp := by
  intro n p q r s
  let B := n ⨯₃ p
  let c := p ⬝ᵥ q
  let w := B ⬝ᵥ q
  have Q : q = c • p + w • B := by
    have e := align_apply _ _ v.property.1 (r.symm (WithLp.toLp 2 q)).ofLp
    rw [show r (WithLp.toLp 2 (r.symm (WithLp.toLp 2 q)).ofLp) = WithLp.toLp 2 q from r.apply_symm_apply _] at e
    rw [show (r.symm (WithLp.toLp 2 q)).ofLp = _ from align_coordinates _ _ v.property.1 _] at e
    change q = c • p + w • B + (n ⬝ᵥ q) • n at e
    rwa [v.property.2,zero_smul,add_zero] at e
  have NB : n ⨯₃ B = -p := by
    rw [show B = n ⨯₃ p from rfl,cross_cross_eq_smul_sub_smul',v.property.1,v.val.1.property,zero_smul,one_smul,zero_sub]
  have NQ : n ⨯₃ q = c • B - w • p := by
    calc n ⨯₃ q = n ⨯₃ (c • p+w • B) := congrArg (n ⨯₃ ·) Q
         _ = _ := by rw [map_add,map_smul,map_smul,NB,smul_neg,← sub_eq_add_neg]
  rw [show (s.symm x).ofLp = _ from align_coordinates _ _ v.property.2 x,
    show (r.symm x).ofLp = _ from align_coordinates _ _ v.property.1 x]
  change ![q ⬝ᵥ x.ofLp,(n ⨯₃ q) ⬝ᵥ x.ofLp,n ⬝ᵥ x.ofLp] = relative c w ![p ⬝ᵥ x.ofLp,B ⬝ᵥ x.ofLp,n ⬝ᵥ x.ofLp]
  rw [NQ, show q ⬝ᵥ x.ofLp = _ from congrArg (· ⬝ᵥ x.ofLp) Q]
  simp [relative,add_dotProduct,sub_dotProduct,smul_dotProduct]
  ring

private abbrev axis (i : Fin 3) : E3 := WithLp.toLp 2 (Pi.single i (1:ℝ))

private theorem contraction_invariant (r : E3 ≃ₗᵢ[ℝ] E3) (L M : E3 →ₗ[ℝ] ℝ) :
    ∑ i, L (r.symm (axis i))*M (r.symm (axis i)) = ∑ i, L (axis i)*M (axis i) := by
  let X := (InnerProductSpace.toDual ℝ E3).symm L.toContinuousLinearMap
  let Y := (InnerProductSpace.toDual ℝ E3).symm M.toContinuousLinearMap
  have eval (w : E3) : L w = inner ℝ X w ∧ M w = inner ℝ w Y := by
    constructor
    · exact (InnerProductSpace.toDual_symm_apply (x := w) (y := L.toContinuousLinearMap)).symm
    · rw [real_inner_comm Y w]
      exact (InnerProductSpace.toDual_symm_apply (x := w) (y := M.toContinuousLinearMap)).symm
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have basis (i) : b i = axis i := EuclideanSpace.basisFun_apply (Fin 3) ℝ i
  have sum (B : OrthonormalBasis (Fin 3) ℝ E3) : ∑ i, L (B i)*M (B i) = inner ℝ X Y := by
    simpa only [fun i => (eval (B i)).1,fun i => (eval (B i)).2] using B.sum_inner_mul_inner X Y
  simpa only [OrthonormalBasis.map_apply,basis] using (sum (b.map r.symm)).trans (sum b).symm

private def rotationFunctional (c s a b h k : ℝ) (m : Fin 3) (i : Fin 4) : E3 →ₗ[ℝ] ℝ where
  toFun x := rotationTaylor x.ofLp (relative c s x.ofLp) a b h k m i
  map_add' x y := by
    fin_cases m <;> fin_cases i <;> simp [rotationTaylor,pack,relative] <;> ring
  map_smul' u x := by
    fin_cases m <;> fin_cases i <;> simp [rotationTaylor,pack,relative] <;> ring

/-- The ambient contraction in the cometric two-jet is independent of the
orientation of the chosen sphere pair. -/
private theorem rotation_contraction (v : FlatLocus.Representative) (a b h k : ℝ)
    (m o : Fin 3) (i j : Fin 4) :
    let n := v.val.1.val
    let p := v.val.2.1.val
    let q := v.val.2.2.val
    let r := align _ _ v.property.1
    let s := align _ _ v.property.2
    let T (l : Fin 3) := rotationTaylor (r.symm (axis l)).ofLp (s.symm (axis l)).ofLp a b h k
    let U (l : Fin 3) := rotationTaylor (axis l).ofLp (relative (p ⬝ᵥ q) ((n ⨯₃ p) ⬝ᵥ q) (axis l).ofLp) a b h k
    ∑ l, T l m i*T l o j = ∑ l, U l m i*U l o j := by
  intro n p q r s T U
  have pair (l m i) : T l m i = rotationFunctional (p ⬝ᵥ q) ((n ⨯₃ p) ⬝ᵥ q) a b h k m i (r.symm (axis l)) := by
    change rotationTaylor _ (s.symm (axis l)).ofLp _ _ _ _ _ _ = _
    rw [show (s.symm (axis l)).ofLp = _ from relative_coordinates v (axis l)]
    rfl
  simp_rw [pair]
  exact contraction_invariant r (rotationFunctional _ _ a b h k m i) (rotationFunctional _ _ a b h k o j)


/-- First three cometric coefficients in terms of the signed separation and
the longitude difference and height velocities. The common longitude cancels. -/
def separationJet (t c w b h k : ℝ) : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ :=
  let e := (1+t)*(h^2+k^2)/2
  let f := c*h*k*t
  let d := (1+t)*(k^2-h^2)/2
  let x := 2*b*c*k*t
  let y := 2*b*c*h*t
  let z := -c*t*(4*b^2+h^2+k^2)
  ![![![1+2*t,0,0,0],![0,1,0,0],![0,0,2*(1+t),2*c*t],![0,0,2*c*t,2*(1+t)]],
    ![![0,0,k*t*w,-h*t*w],![0,0,k*t*w,h*t*w],![k*t*w,k*t*w,0,-4*b*t*w],![-h*t*w,h*t*w,-4*b*t*w,0]],
    ![![e+f,d,x,-y],![d,e-f,x,y],![x,x,-2*h^2*(1+t),z],![-y,y,z,-2*k^2*(1+t)]]]

theorem separation_circle (v : FlatLocus.Representative) :
    let p := v.val.2.1.val
    let q := v.val.2.2.val
    (p ⬝ᵥ q)^2+((v.val.1.val ⨯₃ p) ⬝ᵥ q)^2=1 := by
  intro p q
  let r := align _ _ v.property.1
  let x := WithLp.toLp 2 q
  have E := r.symm.inner_map_map x x
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] at E
  rw [show (r.symm x).ofLp = _ from align_coordinates _ _ v.property.1 x] at E
  change (![p ⬝ᵥ q,(v.val.1.val ⨯₃ p) ⬝ᵥ q,v.val.1.val ⬝ᵥ q] : R3) ⬝ᵥ _ = q ⬝ᵥ q at E
  rw [v.property.2,v.val.2.2.property] at E
  simpa [dotProduct,Fin.sum_univ_three,sq] using E

set_option maxHeartbeats 900000 in
/-- All 48 entries of the adapted inverse Gram two-jet depend only on the
signed separation, also at the two singular separations. -/
theorem inverseTaylor_eq_separationJet (v : FlatLocus.Representative) (t a b h k : ℝ) :
    let p := v.val.2.1.val
    let q := v.val.2.2.val
    inverseTaylor v t a b h k = separationJet t (p ⬝ᵥ q) ((v.val.1.val ⨯₃ p) ⬝ᵥ q) b h k := by
  intro p q
  let c := p ⬝ᵥ q
  let w := (v.val.1.val ⨯₃ p) ⬝ᵥ q
  let r := align _ _ v.property.1
  let s := align _ _ v.property.2
  let T (l : Fin 3) := rotationTaylor (r.symm (axis l)).ofLp (s.symm (axis l)).ofLp a b h k
  let U (l : Fin 3) := rotationTaylor (axis l).ofLp (relative c w (axis l).ofLp) a b h k
  let model : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ :=
    ![fun i j => 2*(unitInverse i j + t*∑ l, U l 0 i*U l 0 j),
      fun i j => 2*(t*∑ l, (U l 1 i*U l 0 j+U l 0 i*U l 1 j)),
      fun i j => 2*(heightTerm h k i j + t*∑ l, (U l 2 i*U l 0 j+U l 1 i*U l 1 j+U l 0 i*U l 2 j))]
  have gram (m o i j) : ∑ l, T l m i*T l o j = ∑ l, U l m i*U l o j := rotation_contraction v a b h k m o i j
  have eq : inverseTaylor v t a b h k = model := by
    funext n i j
    fin_cases n
    · change 2*(unitInverse i j + t*∑ l, T l 0 i*T l 0 j) = _
      rw [gram]; rfl
    · change 2*(t*∑ l, (T l 1 i*T l 0 j+T l 0 i*T l 1 j)) = 2*(t*∑ l, (U l 1 i*U l 0 j+U l 0 i*U l 1 j))
      simp only [Finset.sum_add_distrib,gram]
    · change 2*(heightTerm h k i j+t*∑ l, (T l 2 i*T l 0 j+T l 1 i*T l 1 j+T l 0 i*T l 2 j)) =
        2*(heightTerm h k i j+t*∑ l, (U l 2 i*U l 0 j+U l 1 i*U l 1 j+U l 0 i*U l 2 j))
      simp only [Finset.sum_add_distrib,gram]
  rw [eq]
  change model = separationJet t c w b h k
  have hw : w^2=1-c^2 := by linarith only [show c^2+w^2=1 from separation_circle v]
  generalize hc : c = C at *; generalize hs : w = S at *
  clear_value c w
  funext n i j
  fin_cases n <;> fin_cases i <;> fin_cases j <;>
    simp [model,U,rotationTaylor,pack,relative,Pi.single_apply,Fin.sum_univ_three,unitInverse,heightTerm,separationJet,hc,hs] <;>
    ring_nf
  all_goals try rw [hw]
  all_goals try simp
  all_goals ring


end
end LocalHopf.SphereProduct.JetChart
