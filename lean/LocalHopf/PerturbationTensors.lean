import LocalHopf.MetricPerturbation
import LocalHopf.ChebyshevProfile
import LocalHopf.NormalProfiles
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-! # The tensor channels of §2 on the sphere product -/
namespace LocalHopf.SphereProduct

open Matrix Bundle Filter
open scoped Manifold ContDiff
open Profiles
noncomputable section

abbrev Scalar := C^∞⟮productModel, Base; ℝ⟯
abbrev Axis := C^∞⟮productModel, Base; 𝓘(ℝ,R3), R3⟯
abbrev OneForm := C^∞⟮productModel, Base; 𝓘(ℝ, Cheeger.V →L[ℝ] ℝ), Cheeger.V →L[ℝ] ℝ⟯

def scalar (c : ℝ) : Scalar := ⟨fun _ => c, contMDiff_const⟩
def axis (i : Fin 3) : Axis := ⟨fun _ => Pi.single i 1, contMDiff_const⟩
def point₁ : Axis := ⟨fun p => (ambientPoint p).1, (ContinuousLinearMap.fst ℝ R3 R3).contDiff.contMDiff.comp ambientPoint_smooth⟩
def point₂ : Axis := ⟨fun p => (ambientPoint p).2, (ContinuousLinearMap.snd ℝ R3 R3).contDiff.contMDiff.comp ambientPoint_smooth⟩

def component (a : Axis) (i : Fin 3) : Scalar :=
  ⟨fun p => a p i, (ContinuousLinearMap.proj i : R3 →L[ℝ] ℝ).contDiff.contMDiff.comp a.contMDiff⟩

/-- The pointDot inner product of the two sphere points. -/
def pointDot : Scalar :=
  ⟨fun p => point₁ p ⬝ᵥ point₂ p, by
    simp only [dotProduct, Fin.sum_univ_three]
    exact (((component point₁ 0).contMDiff.mul (component point₂ 0).contMDiff).add
      ((component point₁ 1).contMDiff.mul (component point₂ 1).contMDiff)).add
      ((component point₁ 2).contMDiff.mul (component point₂ 2).contMDiff)⟩

/-- Simultaneous rotation or rotation with opposite sign in the second factor. -/
def rotationField (opposite : Bool) (a : Axis) : C^∞⟮productModel, Base; 𝓘(ℝ,Cheeger.V), Cheeger.V⟯ := by
  let F := fun p => (a p ⨯₃ point₁ p, if opposite then -(a p ⨯₃ point₂ p) else a p ⨯₃ point₂ p)
  have h₁ := Cheeger.smooth_cross.contMDiff.comp (a.contMDiff.prodMk_space point₁.contMDiff)
  have h₂ := Cheeger.smooth_cross.contMDiff.comp (a.contMDiff.prodMk_space point₂.contMDiff)
  have hF : ContMDiff productModel 𝓘(ℝ,Cheeger.V) ∞ F := by
    cases opposite
    · exact h₁.prodMk_space h₂
    · exact h₁.prodMk_space h₂.neg
  exact ⟨F, hF⟩

def rotationFlat (t : ℝ) (ht : 0 ≤ t) (opposite : Bool) (a : Axis) : OneForm :=
  let F := rotationField opposite a
  ⟨fun p => ambientBackground t p (F p), (ambientBackground_smooth ht).clm_apply F.contMDiff⟩

def rotationNormSq (t : ℝ) (ht : 0 ≤ t) (opposite : Bool) (a : Axis) : Scalar :=
  let F := rotationField opposite a
  let α := rotationFlat t ht opposite a
  ⟨fun p => α p (F p), α.contMDiff.clm_apply F.contMDiff⟩

/-- The normalized symmetric product of two index-lowered fields. -/
def symmetricProduct (a b : OneForm) : AmbientTensor where
  form p := (1/2 : ℝ) • ((a p).smulRight (b p) + (b p).smulRight (a p))
  smooth := by
    intro p
    apply smoothAt_clm_of_apply
    intro X
    apply smoothAt_clm_of_apply
    intro Y
    exact (contMDiffAt_const (c := (1/2:ℝ))).mul
      ((((a.contMDiff p).clm_apply (contMDiffAt_const (c := X))).mul
        ((b.contMDiff p).clm_apply (contMDiffAt_const (c := Y)))).add
        (((b.contMDiff p).clm_apply (contMDiffAt_const (c := X))).mul
          ((a.contMDiff p).clm_apply (contMDiffAt_const (c := Y)))))
  symm p X Y := by
    change (1/2:ℝ) * (a p X * b p Y + b p X * a p Y) =
      (1/2:ℝ) * (a p Y * b p X + b p Y * a p X)
    ring

private def weighted (f : Scalar) (A : AmbientTensor) := A.weight f f.contMDiff

private def weightP (t : ℝ) (u : Scalar) : Scalar :=
  ⟨fun p => Pt t (u p), by
    have h : ContDiff ℝ ∞ (Pt t) := by unfold Pt P0; fun_prop
    exact h.contMDiff.comp u.contMDiff⟩

private def weightQ (u : Scalar) : Scalar :=
  ⟨fun p => Q (u p), by
    have h : ContDiff ℝ ∞ Q := by unfold Q; fun_prop
    exact h.contMDiff.comp u.contMDiff⟩

/-- All six symmetric products in the first-order perturbation of §2. -/
def firstOrderTensor (t : ℝ) (ht : 0 ≤ t) : AmbientTensor :=
  let k := rotationFlat t ht false
  let j := rotationFlat t ht true
  let v := point₁ + point₂
  let w := point₂ - point₁
  let ha := (weighted (weightP t (-pointDot)) (symmetricProduct (k v) (k (axis 0)))).add
    (weighted (weightQ (-pointDot)) (symmetricProduct (k w) (j (axis 0))))
  let hb := (weighted (weightP t pointDot) (symmetricProduct (k w) (k (axis 1)))).add
    (weighted (weightQ pointDot) (symmetricProduct (k v) (j (axis 1))))
  ((ha.add hb).add (weighted (scalar lamC) (symmetricProduct (k (axis 2)) (k (axis 2))))).add
    (weighted (scalar lamD) (symmetricProduct (k (axis 0)) (j (axis 2))))

/-- Conformal cubic correction for a smooth extension of the torus potential (§6). -/
def thirdOrderTensor (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) : AmbientTensor :=
  weighted (scalar (2 * hh t) * χ) (backgroundTensor t ht)

theorem abs_pointDot_le (p : Base) : |pointDot p| ≤ 1 := by
  have h := abs_real_inner_le_norm p.2.val p.1.val
  rw [mem_sphere_zero_iff_norm.mp p.1.property, mem_sphere_zero_iff_norm.mp p.2.property,
    mul_one] at h
  simpa [pointDot, point₁, point₂, ambientPoint, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm] using h

private def profileOnBase (f : ℝ → ℝ)
    (hf : ∀ u, |u| ≤ 1 → ContDiffAt ℝ ∞ f u) (u : Scalar) (hu : ∀ p, |u p| ≤ 1) : Scalar :=
  ⟨fun p => f (u p), fun p => (hf _ (hu p)).contMDiffAt.comp p (u.contMDiff p)⟩

/-- One of the two profile terms in the second-order tensor. -/
def profileChannel (t : ℝ) (ht : 0≤t) (i : Fin 3) (f : ℝ → ℝ)
    (hf : ∀ u, |u|≤1 → ContDiffAt ℝ ∞ f u) : AmbientTensor :=
  let k := rotationFlat t ht false (axis i)
  weighted (scalar 9 * profileOnBase f hf pointDot abs_pointDot_le) (symmetricProduct k k)

/-- The second-order tensor with the aa and bb profile amplitudes set to zero. -/
def rationalSecondOrderTensor (t : ℝ) (ht : 0 ≤ t) : AmbientTensor :=
  let u := pointDot
  let hu : ∀ p, |u p| ≤ 1 := abs_pointDot_le
  let hneg : ∀ p, |(-u) p| ≤ 1 := fun p => by simpa using hu p
  let k := rotationFlat t ht false
  let j := rotationFlat t ht true
  let kx := k (axis 0); let ky := k (axis 1); let kz := k (axis 2)
  let jx := j (axis 0); let jy := j (axis 1); let jz := j (axis 2)
  let v := point₁ + point₂; let w := point₂ - point₁
  let vx := component v 0; let vz := component v 2
  let wx := component w 0; let wz := component w 2
  let q := scalar 2 * u^2 - scalar 1
  let M := fun a ha => profileOnBase (normalM t) (fun _ h => (smooth_normal_profiles ht h).1) a ha
  let N := fun a ha => profileOnBase (normalN t) (fun _ h => (smooth_normal_profiles ht h).2.1) a ha
  let φ := profileOnBase (varphi t) (fun _ h => (smooth_normal_profiles ht h).2.2.1) u hu
  let ψ := profileOnBase (psi t) (fun _ h => (smooth_normal_profiles ht h).2.2.2) u hu
  let Δ (i l : Fin 3) := component point₂ i * component point₂ l - component point₁ i * component point₁ l
  let term := fun (c : Scalar) (a b : OneForm) => weighted c (symmetricProduct a b)
  let cc := term (rotationNormSq t ht false (axis 2)) kz kz
  let ac := term (scalar (1/20) * vz * (scalar (-5) - scalar 14*u + scalar 3*q)) kx kz
  let bc := term (scalar (1/20) * wz * (scalar (-5) + scalar 14*u + scalar 3*q)) ky kz
  let dd := term (scalar (1/(4*hh t)) * rotationNormSq t ht true (axis 0)) jz jz
  let ad := term (scalar (1/400)*wx*(scalar (-406)-scalar 92*u+scalar 18*q)) kx kz +
    term (scalar (1/200)*wz*(scalar (-823)+scalar 154*u+scalar 9*q)) kx kx +
    term (-(M u hu * wx)) jx jz + term (-(N u hu * wz)) jx jx
  let bd := term (scalar (1/400)*vx*(scalar (-406)+scalar 92*u+scalar 18*q)) ky kz +
    term (scalar (1/200)*vz*(scalar (-823)-scalar 154*u+scalar 9*q)) kx ky +
    term (-(M (-u) hneg * vx)) jy jz + term (-(N (-u) hneg * vz)) jy jx
  let cd := weighted (scalar (-1/4)) (term (φ * Δ 2 0) jz jz + term (ψ * Δ 2 2) jx jz)
  weighted (scalar (lamC^2)) cc + weighted (scalar (2*lamC)) (ac + bc) +
    weighted (scalar (lamD^2)) dd + weighted (scalar (2*lamD)) (ad + bd) +
    weighted (scalar (2*lamC*lamD)) cd

/-- All nine second-order channels of §2, including the two Chebyshev profiles. -/
def secondOrderTensor (t : ℝ) (ht : 0≤t) : AmbientTensor :=
  let aa := profileChannel t ht 0 (fun z => fbb (-z)) (fun z hz =>
    (smoothAt_fbb (u := -z) (by rw [abs_neg]; exact hz.trans_lt (by norm_num))).comp z contDiffAt_id.neg)
  let bb := profileChannel t ht 1 fbb (fun _ h => smoothAt_fbb (h.trans_lt (by norm_num)))
  aa + bb + rationalSecondOrderTensor t ht

/-- Actual small-parameter metrics with the prescribed first two perturbations and the
conformal cubic correction determined by a smooth potential. -/
theorem exists_paper_metric (t : ℝ) (ht : 0 ≤ t) (χ : Scalar) :
    ∀ᶠ s in nhds (0 : ℝ), ∃ g : SmoothMetric, ∀ (p : Base) (X Y : Tangent p),
      let x := ambientVelocityL p X
      let y := ambientVelocityL p Y
      g.inner p X Y = backgroundPair p t ht (X.1,X.2) (Y.1,Y.2) +
        s * (firstOrderTensor t ht).form p x y + s^2 * (secondOrderTensor t ht).form p x y +
        s^3 * (thirdOrderTensor t ht χ).form p x y :=
  eventually_exists_perturbedMetric t ht _ _ _


theorem firstOrderTensor_apply (t : ℝ) (ht : 0 ≤ t) (p : Base) (X Y : Cheeger.V) :
    let k := rotationFlat t ht false
    let j := rotationFlat t ht true
    let v := point₁+point₂
    let w := point₂-point₁
    let sym (a b : OneForm) := (a p X * b p Y + b p X * a p Y)/2
    (firstOrderTensor t ht).form p X Y =
      (Pt t (-(pointDot p)) * sym (k v) (k (axis 0)) +
       Q (-(pointDot p)) * sym (k w) (j (axis 0))) +
      (Pt t (pointDot p) * sym (k w) (k (axis 1)) +
       Q (pointDot p) * sym (k v) (j (axis 1))) +
      lamC * sym (k (axis 2)) (k (axis 2)) + lamD * sym (k (axis 0)) (j (axis 2)) := by
  dsimp only
  have hP (u : Scalar) : weightP t u p = Pt t (u p) := rfl
  have hQ (u : Scalar) : weightQ u p = Q (u p) := rfl
  have hC (c : ℝ) : scalar c p = c := rfl
  simp only [firstOrderTensor, AmbientTensor.add, weighted, AmbientTensor.weight,
    symmetricProduct, hP, hQ, hC, smul_apply,
    add_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    ContMDiffMap.coe_neg, Pi.neg_apply]
  ring


end
end LocalHopf.SphereProduct
