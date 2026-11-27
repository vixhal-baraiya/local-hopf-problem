/-
Copyright (c) 2026. Released under the MIT License (see ../../LICENSE).

# Vector identities of sections 1 and 4

Points of `M = S² × S²` are pairs `(p₁, p₂)` of unit vectors in `ℝ³`, and tangent
vectors are pairs `(ξ₁, ξ₂)`. This file proves the pointwise linear-algebra facts
about the Killing fields `K_ω` and the fields `J_ω` that PROOF.md uses:

* `gprod_K_K`        : `g_prod(K_ω, K_ω') = ⟨P_p ω, ω'⟩`            (§1, orbit tensor)
* `gprod_J_K`        : `J_b` is horizontal when `b ⊥ p₁, p₂`          (§1, flat locus)
* `orbit_of_perp`    : `P_p b = 2 b` when `b ⊥ p₁, p₂`                (§1)
* `cheeger_on_flat`  : `(I + t P_p) b = (1 + 2t) b`, so `C_t K_b = K_b / (1 + 2t)` (§1)
* `gprod_K_eq_a`     : `g_prod(ξ, K_ω) = ⟨a(ξ), ω⟩`, `a(ξ) = p₁ × ξ₁ + p₂ × ξ₂` (§4)
* `mixed_plane_flat_vectors` : the two spanning vectors of `π_{b,p}` are tangent and
  `g_prod`-orthonormal.

No hypothesis `p₁ ≠ ± p₂` is used anywhere, matching the remark after Lemma 4.1.
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

namespace LocalHopf

open Matrix

/-- Euclidean `ℝ³`, as Mathlib's cross product sees it. -/
abbrev R3 := Fin 3 → ℝ

/-- The product inner product on `T_p M ⊂ ℝ³ × ℝ³`. -/
def gprod (ξ η : R3 × R3) : ℝ := ξ.1 ⬝ᵥ η.1 + ξ.2 ⬝ᵥ η.2

/-- The Killing field `K_ω = (ω × p₁, ω × p₂)` of the diagonal `SO(3)` action. -/
def K (p₁ p₂ ω : R3) : R3 × R3 := (ω ⨯₃ p₁, ω ⨯₃ p₂)

/-- The field `J_ω = (ω × p₁, -ω × p₂)`. -/
def J (p₁ p₂ ω : R3) : R3 × R3 := (ω ⨯₃ p₁, -(ω ⨯₃ p₂))

/-- The orbit tensor `P_p ω = 2ω - ⟨p₁, ω⟩ p₁ - ⟨p₂, ω⟩ p₂`. -/
def orbit (p₁ p₂ ω : R3) : R3 := (2 : ℝ) • ω - (p₁ ⬝ᵥ ω) • p₁ - (p₂ ⬝ᵥ ω) • p₂

/-- `a(ξ) = p₁ × ξ₁ + p₂ × ξ₂`, the moment map of the diagonal action. -/
def moment (p₁ p₂ : R3) (ξ : R3 × R3) : R3 := p₁ ⨯₃ ξ.1 + p₂ ⨯₃ ξ.2

/-- `P_p` represents the product metric on Killing fields:
`g_prod(K_ω, K_ω') = ⟨P_p ω, ω'⟩` for unit `p₁, p₂`. -/
theorem gprod_K_K (p₁ p₂ ω ω' : R3) (h₁ : p₁ ⬝ᵥ p₁ = 1) (h₂ : p₂ ⬝ᵥ p₂ = 1) :
    gprod (K p₁ p₂ ω) (K p₁ p₂ ω') = orbit p₁ p₂ ω ⬝ᵥ ω' := by
  simp only [gprod, K, orbit, cross_dot_cross, sub_dotProduct, smul_dotProduct,
    smul_eq_mul, h₁, h₂]
  rw [dotProduct_comm ω p₁, dotProduct_comm ω p₂, dotProduct_comm p₁ ω',
    dotProduct_comm p₂ ω']
  ring

/-- `J_b` is horizontal (orthogonal to every Killing field) when `b ⊥ p₁, p₂`. -/
theorem gprod_J_K (p₁ p₂ b ω : R3) (h₁ : p₁ ⬝ᵥ p₁ = 1) (h₂ : p₂ ⬝ᵥ p₂ = 1)
    (hb₁ : b ⬝ᵥ p₁ = 0) (hb₂ : b ⬝ᵥ p₂ = 0) :
    gprod (J p₁ p₂ b) (K p₁ p₂ ω) = 0 := by
  simp only [gprod, J, K, neg_dotProduct, cross_dot_cross, h₁, h₂, hb₁, hb₂]
  ring

/-- `P_p b = 2 b` when `b ⊥ p₁, p₂`. -/
theorem orbit_of_perp (p₁ p₂ b : R3) (hb₁ : b ⬝ᵥ p₁ = 0) (hb₂ : b ⬝ᵥ p₂ = 0) :
    orbit p₁ p₂ b = (2 : ℝ) • b := by
  simp [orbit, dotProduct_comm p₁ b, dotProduct_comm p₂ b, hb₁, hb₂]

/-- `(I + t P_p) b = (1 + 2t) b` for `b ⊥ p₁, p₂`. Hence `(I + t P_p)⁻¹ b = b / (1 + 2t)`
and the Cheeger operator satisfies `C_t K_b = K_b / (1 + 2t)`: it fixes every plane of `Z`. -/
theorem cheeger_on_flat (p₁ p₂ b : R3) (t : ℝ) (hb₁ : b ⬝ᵥ p₁ = 0) (hb₂ : b ⬝ᵥ p₂ = 0) :
    b + t • orbit p₁ p₂ b = (1 + 2 * t) • b := by
  rw [orbit_of_perp p₁ p₂ b hb₁ hb₂, smul_smul, add_smul, one_smul, mul_comm]

/-- The moment map: `g_prod(ξ, K_ω) = ⟨a(ξ), ω⟩` at every point, regular or not. -/
theorem gprod_K_eq_moment (p₁ p₂ ω : R3) (ξ : R3 × R3) :
    gprod ξ (K p₁ p₂ ω) = moment p₁ p₂ ξ ⬝ᵥ ω := by
  simp only [gprod, K, moment, cross_apply, dotProduct, Fin.sum_univ_three]
  simp
  ring

/-- The cross product is orthogonal to its second argument. -/
theorem cross_dot_right (a p : R3) : (a ⨯₃ p) ⬝ᵥ p = 0 := by
  rw [dotProduct_comm]; exact dot_cross_self a p

/-- For a unit `b ⊥ p` with `p` unit, `b × p` is a unit vector orthogonal to `p`. -/
theorem cross_unit (b p : R3) (hb : b ⬝ᵥ b = 1) (hp : p ⬝ᵥ p = 1) (hbp : b ⬝ᵥ p = 0) :
    (b ⨯₃ p) ⬝ᵥ (b ⨯₃ p) = 1 ∧ (b ⨯₃ p) ⬝ᵥ p = 0 := by
  refine ⟨?_, cross_dot_right b p⟩
  rw [cross_dot_cross, hb, hp, dotProduct_comm p b, hbp]
  ring

/-- The plane `π_{b,p} = span{(b × p₁, 0), (0, b × p₂)}` of the flat locus `Z`:
its two spanning vectors are tangent to `S² × S²` and `g_prod`-orthonormal. -/
theorem mixed_plane_flat_vectors (p₁ p₂ b : R3) (h₁ : p₁ ⬝ᵥ p₁ = 1) (h₂ : p₂ ⬝ᵥ p₂ = 1)
    (hb : b ⬝ᵥ b = 1) (hb₁ : b ⬝ᵥ p₁ = 0) (hb₂ : b ⬝ᵥ p₂ = 0) :
    let X : R3 × R3 := (b ⨯₃ p₁, 0)
    let Y : R3 × R3 := (0, b ⨯₃ p₂)
    gprod X X = 1 ∧ gprod Y Y = 1 ∧ gprod X Y = 0 ∧
      X.1 ⬝ᵥ p₁ = 0 ∧ Y.2 ⬝ᵥ p₂ = 0 := by
  obtain ⟨u₁, -⟩ := cross_unit b p₁ hb h₁ hb₁
  obtain ⟨u₂, -⟩ := cross_unit b p₂ hb h₂ hb₂
  simp [gprod, u₁, u₂, cross_dot_right]

/-- `π_{b,p} = span{K_b, J_b}`: indeed `(K_b + J_b)/2 = (b × p₁, 0)` and
`(K_b - J_b)/2 = (0, b × p₂)`. -/
theorem K_add_J (p₁ p₂ b : R3) :
    K p₁ p₂ b + J p₁ p₂ b = ((2 : ℝ) • (b ⨯₃ p₁), 0) ∧
      K p₁ p₂ b - J p₁ p₂ b = (0, (2 : ℝ) • (b ⨯₃ p₂)) := by
  refine ⟨?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [K, J, cross_apply] <;> ring

end LocalHopf
