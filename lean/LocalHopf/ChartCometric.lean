import LocalHopf.BackgroundCometric
import LocalHopf.ChartJet

/-! The undeformed inverse Gram and the three rotation terms in the actual
longitude-height chart, in the coordinate order x,y,z₁,z₂. -/
namespace LocalHopf.SphereProduct.JetChart
open Matrix
noncomputable section

private def components : Params ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v := ![v.1.1,v.1.2,v.2.1,v.2.2]
  invFun c := ((c 0,c 1),(c 2,c 3))
  left_inv _ := rfl
  right_inv c := by funext i; fin_cases i <;> rfl
  map_add' a b := by funext i; fin_cases i <;> rfl
  map_smul' c a := by funext i; fin_cases i <;> rfl

def parameterBasis : Module.Basis (Fin 4) ℝ Params := Module.Basis.ofEquivFun components

theorem parameterBasis_coordinates (a : Params) :
    parameterBasis.equivFun a = ![a.1.1,a.1.2,a.2.1,a.2.2] := by
  simp only [parameterBasis,Module.Basis.equivFun_ofEquivFun]
  rfl

theorem parameterBasis_apply (i : Fin 4) : parameterBasis i =
    (![ ((1,0),0),((0,1),0),(0,(1,0)),(0,(0,1)) ] : Fin 4 → Params) i := by
  simp only [parameterBasis,Module.Basis.coe_ofEquivFun]
  let e := (Pi.single i (1:ℝ) : Fin 4 → ℝ)
  change ((e 0,e 1),e 2,e 3) = _
  fin_cases i <;> norm_num [e,Pi.single_apply]

/-- Contravariant coefficients of the unit round product at arbitrary heights. -/
def roundInverse (z w : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let Z := 1-z^2
  let W := 1-w^2
  let m := (Z⁻¹+W⁻¹)/4
  let d := (W⁻¹-Z⁻¹)/4
  ![![m,d,0,0],![d,m,0,0],![0,0,Z,0],![0,0,0,W]]

private theorem dot_rotation (r : E3 ≃ₗᵢ[ℝ] E3) (a b : R3) :
    (r (WithLp.toLp 2 a)).ofLp ⬝ᵥ (r (WithLp.toLp 2 b)).ofLp = a ⬝ᵥ b := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,RCLike.star_def,star_trivial] using r.inner_map_map (WithLp.toLp 2 b) (WithLp.toLp 2 a)

private theorem round_chart (r s : E3 ≃ₗᵢ[ℝ] E3) {y : Params} (hy : y ∈ (chart r s).target) (a b : Params) :
    let Z := 1-y.2.1^2
    let W := 1-y.2.2^2
    2*coefficient r s (backgroundMetric 0 le_rfl) a b y =
      (a.1.1-a.1.2)*(b.1.1-b.1.2)*Z+(a.1.1+a.1.2)*(b.1.1+b.1.2)*W + a.2.1*b.2.1/Z + a.2.2*b.2.2/W := by
  rw [background_coefficient r s hy,zero_mul,sub_zero,chart_velocity r s hy,chart_velocity r s hy]
  have form (L H : R3) (Z c d e f : ℝ) (ll : L ⬝ᵥ L = Z) (lh : L ⬝ᵥ H = 0) (hh : H ⬝ᵥ H = 1/Z) :
      (c • L+d • H) ⬝ᵥ (e • L+f • H) = c*e*Z + d*f/Z := by
    simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,
      dotProduct_comm H L,lh,ll,hh]; ring
  obtain ⟨ll,lh,hh⟩ := LongitudeHeight.round_gram (y.1.1-y.1.2) y.2.1 hy.2.1.1.2
  obtain ⟨ll',lh',hh'⟩ := LongitudeHeight.round_gram (y.1.1+y.1.2) y.2.2 hy.2.2.1.2
  dsimp only [gprod]
  rw [dot_rotation,dot_rotation,form _ _ _ _ _ _ _ ll lh hh,form _ _ _ _ _ _ _ ll' lh' hh']
  ring

/-- The true inverse of the undeformed background (one half the unit round
product). No height truncation has been made. -/
theorem inverse_at_zero (r s : E3 ≃ₗᵢ[ℝ] E3) {y : Params} (hy : y ∈ (chart r s).target) :
    let G : Matrix (Fin 4) (Fin 4) ℝ := fun i j => coefficient r s (backgroundMetric 0 le_rfl) (parameterBasis i) (parameterBasis j) y
    G⁻¹ = (2:ℝ) • roundInverse y.2.1 y.2.2 := by
  intro G
  let Z := 1-y.2.1^2
  let W := 1-y.2.2^2
  have nz : Z ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by
    have h : |y.2.1| < 1 := hy.2.1.1.2
    exact (sq_lt_one_iff_abs_lt_one _).mpr h))
  have nw : W ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by
    have h : |y.2.2| < 1 := hy.2.2.1.2
    exact (sq_lt_one_iff_abs_lt_one _).mpr h))
  let R : Matrix (Fin 4) (Fin 4) ℝ :=
    ![![Z+W,W-Z,0,0],![W-Z,Z+W,0,0],![0,0,Z⁻¹,0],![0,0,0,W⁻¹]]
  have eq (i j : Fin 4) : 2*coefficient r s (backgroundMetric 0 le_rfl) (parameterBasis i) (parameterBasis j) y =
      R i j := by
    rw [round_chart r s hy]
    fin_cases i <;> fin_cases j <;> simp [parameterBasis_apply,R,Z,W]
  let B := roundInverse y.2.1 y.2.2
  have inv : R*B=1 := by
    ext i j
    change (∑ k : Fin 4, R i k*B k j) = if i=j then 1 else 0
    rw [Fin.sum_univ_four]
    have Bval : B = ![![(Z⁻¹+W⁻¹)/4,(W⁻¹-Z⁻¹)/4,0,0],![(W⁻¹-Z⁻¹)/4,(Z⁻¹+W⁻¹)/4,0,0],
      ![0,0,Z,0],![0,0,0,W]] := rfl
    rw [Bval]
    fin_cases i <;> fin_cases j <;> simp [R] <;> field_simp <;> ring
  apply Matrix.inv_eq_right_inv
  ext i j
  have h := congrFun (congrFun inv i) j
  simp only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul] at h ⊢
  refine (Finset.sum_congr rfl fun k _ => ?_).trans h
  change coefficient r s (backgroundMetric 0 le_rfl) (parameterBasis i) (parameterBasis k) y * (2*B k j) = R i k*B k j
  rw [← eq]; ring

/-- The initial cometric used for spatial differentiation in the scripts. The
basis b consists of the four actual coordinate velocities at the chart point. -/
theorem chart_cometric (r s : E3 ≃ₗᵢ[ℝ] E3) {y : Params} (hy : y ∈ (chart r s).target)
    (t : ℝ) (ht : 0 ≤ t) :
    let p := (chart r s).symm y
    ∃ b : Frame p, (∀ i, b i = field r s (parameterBasis i) p) ∧ ∀ i j : Fin 4,
      (gramMatrix (backgroundMetric t ht) b)⁻¹ i j =
        2*(roundInverse y.2.1 y.2.2 i j + t * ∑ k : Fin 3,
          b.equivFun (rotationVector p (Pi.single k 1)) i*b.equivFun (rotationVector p (Pi.single k 1)) j) := by
  intro p
  obtain ⟨L,hL⟩ := field_equiv r s ((chart r s).map_target hy)
  let b : Frame p := parameterBasis.map L.toLinearEquiv
  have hb (i : Fin 4) : b i = field r s (parameterBasis i) p := by simpa [b] using hL (parameterBasis i)
  have eq : gramMatrix (backgroundMetric 0 le_rfl) b =
      fun i j => coefficient r s (backgroundMetric 0 le_rfl) (parameterBasis i) (parameterBasis j) y := by
    ext i j
    change (backgroundMetric 0 le_rfl).inner p (b i) (b j) = _
    rw [hb,hb]; rfl
  refine ⟨b,hb,fun i j => ?_⟩
  rw [cometric_entries,eq,inverse_at_zero r s hy]
  simp only [Matrix.smul_apply,smul_eq_mul]
  ring

/-- A column of the rotation matrix in the script's coordinates. Round duality
recovers its entries from the three ambient moments of the coordinate vectors. -/
def rotationEntry (r s : E3 ≃ₗᵢ[ℝ] E3) (y : Params) (i : Fin 4) (k : Fin 3) :=
  let p := ambientPoint ((chart r s).symm y)
  let L := fderiv ℝ (ambientPoint ∘ (chart r s).symm) y
  ∑ j, roundInverse y.2.1 y.2.2 i j * moment p.1 p.2 (L (parameterBasis j)) k

/-- Coordinates of the genuine rotation vector relative to any coordinate
frame. The equality applies throughout the open chart. -/
theorem rotationEntry_coordinates (r s : E3 ≃ₗᵢ[ℝ] E3) {y : Params} (hy : y ∈ (chart r s).target)
    (b : Frame ((chart r s).symm y)) (hb : ∀ i, b i=field r s (parameterBasis i) ((chart r s).symm y))
    (k : Fin 3) (i : Fin 4) :
    b.equivFun (rotationVector ((chart r s).symm y) (Pi.single k 1)) i = rotationEntry r s y i k := by
  let p := (chart r s).symm y
  let P := (ambientPoint p).1
  let Q := (ambientPoint p).2
  let g := backgroundMetric 0 le_rfl
  have mat (g : SmoothMetric) : gramMatrix g b =
      fun i j => coefficient r s g (parameterBasis i) (parameterBasis j) y := by
    ext i j
    change g.inner p (b i) (b j) = _
    rw [hb,hb]; rfl
  let V := rotationVector p (Pi.single k 1)
  let H := gramMatrix g b
  have cov : H *ᵥ b.equivFun V = frameCovector g b V := by
    funext j
    change (∑ l, g.inner p (b j) (b l)*b.equivFun V l) = g.inner p (b j) V
    conv_rhs => rw [← b.equivFun.symm_apply_apply V]
    simp only [b.equivFun_symm_apply,map_sum,map_smul,smul_eq_mul]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm ..)
  have solved : b.equivFun V = H⁻¹ *ᵥ frameCovector g b V := by
    rw [← cov,mulVec_mulVec,nonsing_inv_mul _ (gram_isUnit g b),one_mulVec]
  have moment_entry (j : Fin 4) : 2*frameCovector g b V j =
      moment P Q (fderiv ℝ (ambientPoint ∘ (chart r s).symm) y (parameterBasis j)) k := by
    change 2*(backgroundMetric 0 le_rfl).inner _ _ _ = _
    rw [twice_backgroundMetric_zero,roundPair_ambient]
    change gprod (ambientVelocityL p (b j)) (ambientVelocityL p V) = _
    rw [hb,ambient_field r s ((chart r s).map_target hy), (chart r s).right_inv hy,
      show ambientVelocityL p V = _ from ambient_rotationVector _ _,gprod_K_eq_moment,dotProduct_single,mul_one]
  change b.equivFun V i = _
  rw [solved,show H⁻¹ = (2:ℝ) • roundInverse y.2.1 y.2.2 from (congrArg Inv.inv (mat g)).trans (inverse_at_zero r s hy)]
  change (∑ j, (2*roundInverse _ _ i j)*frameCovector g b V j) = _
  unfold rotationEntry
  apply Finset.sum_congr rfl
  intro j _
  rw [← moment_entry j]; ring

/-- Complete contravariant background metric in the verifier's four coordinates,
using just the chart velocities, two heights and the Cheeger parameter. -/
theorem explicit_cometric (r s : E3 ≃ₗᵢ[ℝ] E3) {y : Params} (hy : y ∈ (chart r s).target)
    (t : ℝ) (ht : 0 ≤ t) :
    let G : Matrix (Fin 4) (Fin 4) ℝ := fun i j => coefficient r s (backgroundMetric t ht) (parameterBasis i) (parameterBasis j) y
    ∀ i j, G⁻¹ i j = 2*(roundInverse y.2.1 y.2.2 i j+
      t*∑ k, rotationEntry r s y i k * rotationEntry r s y j k) := by
  intro G
  let p := (chart r s).symm y
  obtain ⟨b,hb,entries⟩ := chart_cometric r s hy t ht
  have mat (g : SmoothMetric) : gramMatrix g b =
      fun i j => coefficient r s g (parameterBasis i) (parameterBasis j) y := by
    ext i j
    change g.inner p (b i) (b j) = _
    rw [hb,hb]; rfl
  have rot := rotationEntry_coordinates r s hy b hb
  intro i j
  have Gi : gramMatrix (backgroundMetric t ht) b = G := mat _
  rw [← Gi]
  refine (entries i j).trans ?_
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg₂ (· * ·) (rot k i) (rot k j)

/-- Ambient velocity of every coordinate vector at the adapted chart center. -/
theorem center_velocity (v : FlatLocus.Representative) (d : Params) :
    let n := v.val.1
    let p := v.val.2.1
    let q := v.val.2.2
    let r := (axesBasis n p v.property.1).repr.symm
    let s := (axesBasis n q v.property.2).repr.symm
    fderiv ℝ (ambientPoint ∘ (chart r s).symm) 0 d =
      ((d.1.1-d.1.2) • (n.val ⨯₃ p.val)+d.2.1 • n.val,
       (d.1.1+d.1.2) • (n.val ⨯₃ q.val)+d.2.2 • n.val) := by
  intro n p q r s
  let L := fderiv ℝ (ambientPoint ∘ (chart r s).symm) 0
  have vectors (n p : FlatLocus.UnitVector) (hp : n.val ⬝ᵥ p.val = 0) (a b : ℝ) :
      ((axesBasis n p hp).repr.symm (WithLp.toLp 2 (a • LongitudeHeight.lonVector 0 0 +
        b • LongitudeHeight.heightVector 0 0))).ofLp = a • (n.val ⨯₃ p.val)+b • n.val := by
    have l : WithLp.toLp 2 (LongitudeHeight.lonVector 0 0) = EuclideanSpace.single 1 (1:ℝ) := by
      ext i; fin_cases i <;> norm_num [LongitudeHeight.lonVector,EuclideanSpace.single]
      change Real.sqrt (1-(0:ℝ)^2) = 1
      norm_num
    have h : WithLp.toLp 2 (LongitudeHeight.heightVector 0 0) = EuclideanSpace.single 2 (1:ℝ) := by
      ext i; fin_cases i <;> norm_num [LongitudeHeight.heightVector,EuclideanSpace.single]
    rw [WithLp.toLp_add,WithLp.toLp_smul,WithLp.toLp_smul,l,h,map_add,map_smul,map_smul,axesBasis_apply,axesBasis_apply]
    rfl
  have vel (d : Params) : L d =
      ((d.1.1-d.1.2) • (n.val ⨯₃ p.val)+d.2.1 • n.val,
       (d.1.1+d.1.2) • (n.val ⨯₃ q.val)+d.2.2 • n.val) := by
    rw [show L d = _ from chart_velocity r s (center v).1 d]
    change (_,_) = _
    simp only [Prod.fst_zero,Prod.snd_zero,sub_zero,add_zero]
    exact Prod.ext (vectors n p v.property.1 ..) (vectors n q v.property.2 ..)
  exact vel d

private theorem rotation_at_center (v : FlatLocus.Representative) :
    let n := v.val.1
    let p := v.val.2.1
    let q := v.val.2.2
    let r := (axesBasis n p v.property.1).repr.symm
    let s := (axesBasis n q v.property.2).repr.symm
    ∀ i k, rotationEntry r s 0 i k = (![n.val,0,p.val ⨯₃ n.val,q.val ⨯₃ n.val] : Fin 4 → R3) i k := by
  intro n p q r s
  let L := fderiv ℝ (ambientPoint ∘ (chart r s).symm) 0
  have vel (d : Params) : L d =
      ((d.1.1-d.1.2) • (n.val ⨯₃ p.val)+d.2.1 • n.val,
       (d.1.1+d.1.2) • (n.val ⨯₃ q.val)+d.2.2 • n.val) := center_velocity v d
  have triple (P : FlatLocus.UnitVector) (hp : n.val ⬝ᵥ P.val = 0) :
      P.val ⨯₃ (n.val ⨯₃ P.val) = n.val := by
    rw [cross_cross_eq_smul_sub_smul',show P.val ⬝ᵥ P.val = 1 from P.property,
      hp,zero_smul,one_smul,sub_zero]
  have m (d : Params) : moment p.val q.val (L d) =
      (2*d.1.1) • n.val+d.2.1 • (p.val ⨯₃ n.val)+d.2.2 • (q.val ⨯₃ n.val) := by
    rw [vel,moment]
    simp only [map_add,map_smul,triple p v.property.1,triple q v.property.2]
    module
  intro i k
  unfold rotationEntry
  rw [(center v).2]
  change (∑ j, roundInverse 0 0 i j * moment p.val q.val (L (parameterBasis j)) k) = _
  simp_rw [m,parameterBasis_apply]
  fin_cases i <;> simp [roundInverse,Fin.sum_univ_four]
  ring

/-- The inverse background matrix at each common-normal frame, including both
singular orbits. The separation enters only through the two height coordinates. -/
theorem inverse_at_center (v : FlatLocus.Representative) (t : ℝ) (ht : 0 ≤ t) :
    let n := v.val.1
    let p := v.val.2.1
    let q := v.val.2.2
    let r := (axesBasis n p v.property.1).repr.symm
    let s := (axesBasis n q v.property.2).repr.symm
    let G : Matrix (Fin 4) (Fin 4) ℝ := fun i j => coefficient r s (backgroundMetric t ht) (parameterBasis i) (parameterBasis j) 0
    let c := p.val ⬝ᵥ q.val
    G⁻¹ = ![![1+2*t,0,0,0],![0,1,0,0],![0,0,2*(1+t),2*t*c],![0,0,2*t*c,2*(1+t)]] := by
  intro n p q r s G c
  let rot := (![n.val,0,p.val ⨯₃ n.val,q.val ⨯₃ n.val] : Fin 4 → R3)
  have H (i j : Fin 4) : G⁻¹ i j = 2*(roundInverse 0 0 i j+t*(rot i ⬝ᵥ rot j)) := by
    rw [show G⁻¹ i j = _ from explicit_cometric r s (center v).1 t ht i j]
    congr 2
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg₂ (· * ·) (rotation_at_center v i k) (rotation_at_center v j k)
  have dot (P Q : FlatLocus.UnitVector) (hp : n.val ⬝ᵥ P.val = 0) (hq : n.val ⬝ᵥ Q.val = 0) :
      (P.val ⨯₃ n.val) ⬝ᵥ (Q.val ⨯₃ n.val) = P.val ⬝ᵥ Q.val := by
    simp [cross_dot_cross,show n.val ⬝ᵥ n.val = 1 from n.property,hq]
  have orth (P : FlatLocus.UnitVector) : (P.val ⨯₃ n.val) ⬝ᵥ n.val = 0 :=
    (dotProduct_comm ..).trans (dot_cross_self ..)
  ext i j
  rw [H]
  fin_cases i <;> fin_cases j <;>
    simp [roundInverse,rot,dot p p v.property.1 v.property.1,dot q q v.property.2 v.property.2,
      dot p q v.property.1 v.property.2,dot q p v.property.2 v.property.1,
      orth p,orth q,show n.val ⬝ᵥ n.val=1 from n.property,show p.val ⬝ᵥ p.val=1 from p.property,
      show q.val ⬝ᵥ q.val=1 from q.property,dotProduct_comm q.val p.val,c] <;> ring

/-- The covariant starting matrix in the finite inverse series of the verifier. -/
theorem metric_at_center (v : FlatLocus.Representative) (t : ℝ) (ht : 0 ≤ t) :
    let n := v.val.1
    let p := v.val.2.1
    let q := v.val.2.2
    let r := (axesBasis n p v.property.1).repr.symm
    let s := (axesBasis n q v.property.2).repr.symm
    let G : Matrix (Fin 4) (Fin 4) ℝ := fun i j => coefficient r s (backgroundMetric t ht) (parameterBasis i) (parameterBasis j) 0
    let c := p.val ⬝ᵥ q.val
    let d := 2*Profiles.D t c
    G = ![![(1+2*t)⁻¹,0,0,0],![0,1,0,0],![0,0,(1+t)/d,-t*c/d],![0,0,-t*c/d,(1+t)/d]] := by
  intro n p q r s G c d
  let B : Matrix (Fin 4) (Fin 4) ℝ :=
    ![![1+2*t,0,0,0],![0,1,0,0],![0,0,2*(1+t),2*t*c],![0,0,2*t*c,2*(1+t)]]
  have eq : G⁻¹ = B := inverse_at_center v t ht
  have unit : IsUnit G.det := by
    by_contra hn
    have h := congrFun (congrFun (eq.symm.trans (nonsing_inv_apply_not_isUnit G hn)) 1) 1
    norm_num [B] at h
  have hc : |c| ≤ 1 := abs_le.mpr (FlatLocus.frame v).2.2.2.2
  have dh : 0 < d := mul_pos (by norm_num) (Profiles.D_pos ht ((sq_le_one_iff_abs_le_one _).mpr hc))
  have hp : 1+2*t ≠ 0 := by linarith
  rw [← nonsing_inv_nonsing_inv G unit,eq]
  apply Matrix.inv_eq_right_inv
  let M : Matrix (Fin 4) (Fin 4) ℝ := ![![(1+2*t)⁻¹,0,0,0],![0,1,0,0],![0,0,(1+t)/d,-t*c/d],![0,0,-t*c/d,(1+t)/d]]
  change B*M=1
  ext i j
  change (∑ l, B i l*M l j) = if i=j then 1 else 0
  rw [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [B,M,hp] <;> field_simp [dh.ne'] <;> dsimp [d,Profiles.D] <;> ring

end
end LocalHopf.SphereProduct.JetChart
