import LocalHopf.BackgroundComparison

/-! The finite curvature contraction agrees with the exported background operator, giving (Z) intrinsically. -/
namespace LocalHopf.SphereProduct.JetChart
open Matrix Real
noncomputable section

private abbrev V4 := Fin 4 → ℝ
private abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ
private abbrev co := parameterBasis.equivFun
private def I0 (t c : ℝ) : M4 := ![![1+2*t,0,0,0],![0,1,0,0],![0,0,2*(1+t),2*t*c],![0,0,2*t*c,2*(1+t)]]
private def B0 (t c : ℝ) : M4 := metricTaylor t c 0 0 0
private def Q1 (t c w : ℝ) (d : Params) : M4 := separationJet t c w d.1.2 d.2.1 d.2.2 1
private def R2 (t c w : ℝ) (d : Params) : M4 := separationJet t c w d.1.2 d.2.1 d.2.2 2

private theorem symm_dot (M : M4) (h : Mᵀ=M) (x y : V4) : x ⬝ᵥ M *ᵥ y = (M *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec,←vecMul_transpose,h]

private def dualCoords (x : Params) : V4 := ![x.1.1,x.1.2,x.2.1/2,x.2.2/2]

private theorem gram_dual (t c : ℝ) (ht : 0≤t) (hc : c^2≤1) (u : Params) :
    B0 t c *ᵥ co (pullCoordinates t c u) = dualCoords u := by
  have hd := (Profiles.D_pos ht hc).ne'
  have hh : 1+2*t ≠ 0 := by linarith
  change B0 t c *ᵥ parameterBasis.equivFun _ = _
  rw [parameterBasis_coordinates]
  ext i; fin_cases i <;> simp [B0,metricTaylor,pullCoordinates,dualCoords,mulVec,dotProduct,Fin.sum_univ_four] <;>
    field_simp [hd,hh] <;> unfold Profiles.D <;> ring

private theorem inverse_blocks (t c : ℝ) (ht : 0≤t) (hc : c^2≤1) : I0 t c*B0 t c=1 := by
  have hd := (Profiles.D_pos ht hc).ne'
  have hh : 1+2*t ≠ 0 := by linarith
  ext i j; rw [Matrix.mul_apply]; fin_cases i <;> fin_cases j <;> norm_num [I0,B0,metricTaylor,Fin.sum_univ_four] <;>
    field_simp [hd,hh] <;> unfold Profiles.D <;> ring

private def entryPair (G : M4) (a b : Params) := ∑ i, ∑ j, (co a i*co b j)*G i j

private theorem entry_dot (G : M4) (a b : Params) : entryPair G a b = co a ⬝ᵥ G *ᵥ co b := by
  unfold entryPair mulVec dotProduct
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _; ring

private theorem gram_symm (t c : ℝ) : (B0 t c)ᵀ = B0 t c := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem Q_symm (t c w : ℝ) (d : Params) : (Q1 t c w d)ᵀ = Q1 t c w d := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem linear_entry (t c w : ℝ) (d u v : Params) :
    entryPair (metricTaylor t c w d 1) u v =
    -(B0 t c *ᵥ co u) ⬝ᵥ Q1 t c w d *ᵥ (B0 t c *ᵥ co v) := by
  rw [entry_dot]
  change co u ⬝ᵥ (-(B0 t c*Q1 t c w d*B0 t c)) *ᵥ co v = _
  rw [neg_mulVec,dotProduct_neg,neg_dotProduct,←mulVec_mulVec,←mulVec_mulVec,symm_dot _ (gram_symm ..)]

private theorem quadratic_entry (t c w : ℝ) (d u v : Params) :
    let B := B0 t c
    let Q := Q1 t c w d
    let x := B *ᵥ co u
    let y := B *ᵥ co v
    entryPair (metricTaylor t c w d 2) u v =
      (Q *ᵥ x) ⬝ᵥ B *ᵥ (Q *ᵥ y) - x ⬝ᵥ R2 t c w d *ᵥ y := by
  intro B Q x y
  rw [entry_dot]
  change co u ⬝ᵥ (B*Q*B*Q*B-B*R2 t c w d*B) *ᵥ co v = _
  simp only [sub_mulVec,dotProduct_sub,←mulVec_mulVec]
  rw [symm_dot B (gram_symm ..),symm_dot B (gram_symm ..),symm_dot Q (Q_symm ..)]

/-- A contraction in which the covariant Gram matrix occurs only linearly.
Multiplication by the common background denominator therefore clears it. -/
private def modelCurvature (t c w mass : ℝ) (B : M4) (x y : Params) : ℝ :=
  let I := I0 t c
  let Q := Q1 t c w
  let U := dualCoords x
  let V := dualCoords y
  let a := pullCoordinates t c x
  let b := pullCoordinates t c y
  let q (d : Params) (X Y : V4) := (Q d *ᵥ X) ⬝ᵥ B *ᵥ (Q d *ᵥ Y) - mass*(X ⬝ᵥ R2 t c w d *ᵥ Y)
  let K (a b : Params) (X Y : V4) := -(Q a *ᵥ Y + Q b *ᵥ X)
  let W (X Y : V4) (i : Fin 4) := X ⬝ᵥ Q (parameterBasis i) *ᵥ Y
  let H (k z l v : V4) := (k ⬝ᵥ B *ᵥ l + mass*(k ⬝ᵥ v + z ⬝ᵥ l + z ⬝ᵥ I *ᵥ v))/4
  q (a+b) V U-q a V U-q b V U-q a V V-q b U U +
    H (K a b U V) (W U V) (K a b U V) (W U V) -
    H (K a a U U) (W U U) (K b b V V) (W V V)


def reducedCurvature (t c w : ℝ) (x y : Params) : ℝ := modelCurvature t c w 1 (B0 t c) x y

private def kVec (t c w : ℝ) (a b : Params) (X Y : V4) :=
  -(Q1 t c w a *ᵥ Y + Q1 t c w b *ᵥ X)
private def wVec (t c w : ℝ) (X Y : V4) (i : Fin 4) := X ⬝ᵥ Q1 t c w (parameterBasis i) *ᵥ Y

private theorem conn (t c w : ℝ) (a b : Params) :
    let B := B0 t c
    let X := B *ᵥ co a
    let Y := B *ᵥ co b
    let first (d u v : Params) := entryPair (metricTaylor t c w d 1) u v
    (fun i => (first a b (parameterBasis i)+first b (parameterBasis i) a-first (parameterBasis i) a b)/2) =
      (1/2 : ℝ) • (B *ᵥ kVec t c w a b X Y + wVec t c w X Y) := by
  intro B X Y first
  have e (i : Fin 4) : co (parameterBasis i) = Pi.single i (1:ℝ) := by
    funext j
    simp [co,Pi.single_apply,eq_comm]
  have right (N : M4) (hn : Nᵀ=N) (Y : V4) (i : Fin 4) :
      Y ⬝ᵥ N *ᵥ (B *ᵥ co (parameterBasis i)) = (B *ᵥ (N *ᵥ Y)) i := by
    rw [symm_dot N hn,symm_dot B (gram_symm ..),e,dotProduct_single,mul_one]
  have left (Z : V4) (i : Fin 4) : (B *ᵥ co (parameterBasis i)) ⬝ᵥ Z = (B *ᵥ Z) i := by
    rw [← symm_dot B (gram_symm ..),e,single_dotProduct,one_mul]
  funext i
  simp only [first,linear_entry,neg_dotProduct]
  change (-(Y ⬝ᵥ Q1 t c w a *ᵥ (B *ᵥ co (parameterBasis i))) -
    ((B *ᵥ co (parameterBasis i)) ⬝ᵥ (Q1 t c w b *ᵥ X)) -
    -(X ⬝ᵥ Q1 t c w (parameterBasis i) *ᵥ Y))/2 = _
  rw [right _ (Q_symm ..),left]
  simp [kVec,wVec,mulVec_neg,mulVec_add,Pi.add_apply]
  ring

private theorem pair_symbols (t c : ℝ) (ht : 0≤t) (hc : c^2≤1) (k z l v : V4) :
    let B := B0 t c
    let I := I0 t c
    ((1/2:ℝ) • (B *ᵥ k+z)) ⬝ᵥ I *ᵥ ((1/2:ℝ) • (B *ᵥ l+v)) =
    (k ⬝ᵥ B *ᵥ l + k ⬝ᵥ v + z ⬝ᵥ l + z ⬝ᵥ I *ᵥ v)/4 := by
  intro B I
  have SI : Iᵀ=I := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  have cancel (X : V4) : I *ᵥ (B *ᵥ X) = X := by rw [mulVec_mulVec,inverse_blocks t c ht hc,one_mulVec]
  simp only [mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,mulVec_add,cancel,add_dotProduct,dotProduct_add]
  rw [symm_dot I SI,cancel,←symm_dot B (gram_symm ..)]
  ring

/-- The same sectional numerator in the inverse Cheeger frame, expressed
using a single occurrence of the covariant Gram matrix in each product. -/
theorem curvature_in_pull_coordinates (t c w : ℝ) (ht : 0 ≤ t) (hc : c^2≤1) (x y : Params) :
    backgroundNumerator t c w (pullCoordinates t c x) (pullCoordinates t c y) = reducedCurvature t c w x y := by
  let B := B0 t c
  let I := I0 t c
  let a := pullCoordinates t c x
  let b := pullCoordinates t c y
  let q (d u v : Params) := entryPair (metricTaylor t c w d 2) u v
  let first (d u v : Params) := entryPair (metricTaylor t c w d 1) u v
  let Γ (u v : Params) (i : Fin 4) := (first u v (parameterBasis i)+first v (parameterBasis i) u-first (parameterBasis i) u v)/2
  change q (a+b) b a-q a b a-q b b a-q a b b-q b a a + Γ a b ⬝ᵥ I *ᵥ Γ a b - Γ a a ⬝ᵥ I *ᵥ Γ b b = _
  have gam (A C : Params) : Γ A C = (1/2:ℝ) • (B *ᵥ kVec t c w A C (B *ᵥ co A) (B *ᵥ co C) +
      wVec t c w (B *ᵥ co A) (B *ᵥ co C)) := conn t c w A C
  have pair (k z l v : V4) :
      ((1/2:ℝ) • (B *ᵥ k+z)) ⬝ᵥ I *ᵥ ((1/2:ℝ) • (B *ᵥ l+v)) =
      (k ⬝ᵥ B *ᵥ l + k ⬝ᵥ v + z ⬝ᵥ l + z ⬝ᵥ I *ᵥ v)/4 := pair_symbols t c ht hc k z l v
  simp only [gam,pair,q,quadratic_entry]
  change _ = reducedCurvature t c w x y
  dsimp only [a,b,B]
  simp only [gram_dual t c ht hc]
  simp only [reducedCurvature,modelCurvature,kVec,one_mul,add_assoc]
  rfl



private def den (t c : ℝ) := 2*(1+2*t)*Profiles.D t c
private def scaledGram (t c : ℝ) : M4 :=
  let h := 1+2*t
  let a := h*(1+t)
  let b := -(h*t*c)
  ![![2*Profiles.D t c,0,0,0],![0,den t c,0,0],![0,0,a,b],![0,0,b,a]]

private theorem scaledGram_eq (t c : ℝ) (ht : 0≤t) (hc : c^2≤1) :
    scaledGram t c = den t c • B0 t c := by
  have hd := (Profiles.D_pos ht hc).ne'
  have hh : 1+2*t ≠ 0 := by linarith
  ext i j; rw [Matrix.smul_apply,smul_eq_mul]; fin_cases i <;> fin_cases j <;> simp [scaledGram,den,B0,metricTaylor] <;> field_simp [hd,hh]

private theorem clear_denominator (t c w : ℝ) (ht : 0≤t) (hc : c^2≤1) (x y : Params) :
    den t c*reducedCurvature t c w x y = modelCurvature t c w (den t c) (scaledGram t c) x y := by
  rw [scaledGram_eq t c ht hc]
  simp only [reducedCurvature,modelCurvature,smul_mulVec,dotProduct_smul,smul_eq_mul,one_mul]
  ring


open BackgroundGrowth Certificate

private theorem dot4 (x y : V4) : x ⬝ᵥ y = x 0*y 0+x 1*y 1+x 2*y 2+x 3*y 3 := by
  simp [dotProduct,Fin.sum_univ_four]
private theorem mv4 (M : M4) (v : V4) (i : Fin 4) :
    (M *ᵥ v) i = M i 0*v 0+M i 1*v 1+M i 2*v 2+M i 3*v 3 := dot4 (M i) v

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 8000 in
private theorem checkTable (t c w : ℝ) (hw : w^2=1-c^2) (x y : Params) :
    2*modelCurvature t c w (den t c) (scaledGram t c) x y =
      curvatureNum t c (minors (co x) (co y)) := by
  obtain ⟨⟨x₀,x₁⟩,x₂,x₃⟩ := x
  obtain ⟨⟨y₀,y₁⟩,y₂,y₃⟩ := y
  change _ = curvatureNum t c (minors (parameterBasis.equivFun _) (parameterBasis.equivFun _))
  rw [parameterBasis_coordinates,parameterBasis_coordinates]
  simp only [modelCurvature,dot4,mv4,Pi.neg_apply,Pi.add_apply]
  norm_num [Q1,R2,I0,scaledGram,den,separationJet,dualCoords,pullCoordinates,parameterBasis_apply,
    curvatureNum,curvatureEntries,eval₂,horner,Profiles.D,minors]
  ring_nf
  rw [hw]
  ring


/-- The complete curvature table agrees with the intrinsic numerator after
applying the inverse Cheeger endomorphism to both spanning vectors. -/
theorem pulledCurvature_eq_intrinsic (t c w : ℝ) (ht : 0 ≤ t) (circle : c^2+w^2=1) (x y : Params) :
    pulledCurvature t c (parameterBasis.equivFun x) (parameterBasis.equivFun y) =
      2*backgroundNumerator t c w (pullCoordinates t c x) (pullCoordinates t c y) := by
  have hc : c^2≤1 := by nlinarith only [circle,sq_nonneg w]
  have hp : 0<den t c := by unfold den; exact mul_pos (by linarith) (Profiles.D_pos ht hc)
  rw [curvature_in_pull_coordinates t c w ht hc]
  change curvatureNum t c (minors (co x) (co y))/(2*(1+2*t)*((1+t)^2-(t*c)^2)) = _
  rw [mul_pow]
  change curvatureNum t c (minors (co x) (co y))/den t c = _
  rw [div_eq_iff hp.ne',← checkTable t c w (by linarith only [circle]) x y,← clear_denominator t c w ht hc]
  ring

/-- Inequality (Z) for the Levi-Civita curvature of the actual Cheeger metric
on all tangent pairs of the sphere product, for every nonnegative parameter. -/
theorem intrinsic_background_comparison (t : ℝ) (ht : 0≤t) : BackgroundGrowth.Transverse.backgroundComparison t ht :=
  comparison_of_separation_bound t ht fun c w circle x y => (pulledCurvature_eq_intrinsic t c w ht circle x y).le

end
end LocalHopf.SphereProduct.JetChart
