import LocalHopf.MetricRealization
import LocalHopf.Profiles
import Mathlib.Topology.Maps.Proper.Basic

/-! # The small-parameter metric window of §2

The background is positive even on the ambient vector space. Its minimum on the
compact family of ambient unit spheres controls perturbations uniformly in the base.
-/
namespace LocalHopf.SphereProduct

open Set Bundle Filter Matrix
open scoped Topology Manifold ContDiff
noncomputable section

/-- Smooth symmetric ambient two-tensors to be restricted to the tangent bundle. -/
structure AmbientTensor where
  form : Base → AmbientForm
  smooth : ContMDiff productModel 𝓘(ℝ, AmbientForm) ∞ form
  symm : ∀ p X Y, form p X Y = form p Y X

def AmbientTensor.add (A B : AmbientTensor) : AmbientTensor where
  form p := A.form p + B.form p
  smooth := A.smooth.add B.smooth
  symm p X Y := by simp [A.symm p X Y, B.symm p X Y]

instance : Add AmbientTensor := ⟨AmbientTensor.add⟩

def AmbientTensor.weight (A : AmbientTensor) (f : Base → ℝ)
    (hf : ContMDiff productModel 𝓘(ℝ, ℝ) ∞ f) : AmbientTensor where
  form p := f p • A.form p
  smooth := hf.smul A.smooth
  symm p X Y := by simp [A.symm p X Y]

def backgroundTensor (t : ℝ) (ht : 0 ≤ t) : AmbientTensor :=
  ⟨ambientBackground t, ambientBackground_smooth ht, fun p X Y => by
    rw [ambientBackground_apply p ht, ambientBackground_apply p ht, Cheeger.pairing_symm _ _ _ ht X Y]⟩

/-- The cubic polynomial in the perturbation parameter, including its constant term. -/
def perturbationTensor (t : ℝ) (ht : 0 ≤ t) (H₁ H₂ H₃ : AmbientTensor) (s : ℝ) : AmbientTensor :=
  (((backgroundTensor t ht).add (H₁.weight (fun _ => s) contMDiff_const)).add
    (H₂.weight (fun _ => s^2) contMDiff_const)).add (H₃.weight (fun _ => s^3) contMDiff_const)

theorem perturbationTensor_apply (t : ℝ) (ht : 0 ≤ t) (H₁ H₂ H₃ : AmbientTensor)
    (s : ℝ) (p : Base) (X Y : Cheeger.V) :
    (perturbationTensor t ht H₁ H₂ H₃ s).form p X Y =
      ambientBackground t p X Y + s * H₁.form p X Y + s^2 * H₂.form p X Y + s^3 * H₃.form p X Y := by
  simp [perturbationTensor, AmbientTensor.add, AmbientTensor.weight, backgroundTensor]

/-- A single window works for all base points and all directions, for fixed `t`. -/
theorem perturbation_window (t : ℝ) (ht : 0 ≤ t) (H₁ H₂ H₃ : AmbientTensor) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ (p : Base) (v : Cheeger.V), v ≠ 0 →
      0 < (perturbationTensor t ht H₁ H₂ H₃ s).form p v v := by
  let S := ↥(Metric.sphere (0 : Cheeger.V) 1)
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Cheeger.V) 1)
  let eval (A : AmbientTensor) (z : ℝ × (Base × S)) := A.form z.2.1 z.2.2.val z.2.2.val
  have hEval (A : AmbientTensor) : Continuous (eval A) := by
    have hv : Continuous (fun z : ℝ × (Base × S) => z.2.2.val) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact ((A.smooth.continuous.comp (continuous_fst.comp continuous_snd)).clm_apply hv).clm_apply hv
  let bad : Set (ℝ × (Base × S)) := {z |
    (perturbationTensor t ht H₁ H₂ H₃ z.1).form z.2.1 z.2.2.val z.2.2.val ≤ 0}
  have hc : IsClosed bad := by
    apply isClosed_le _ continuous_const
    simp only [perturbationTensor_apply]
    exact (((hEval (backgroundTensor t ht)).add (continuous_fst.mul (hEval H₁))).add
      ((continuous_fst.pow 2).mul (hEval H₂))).add ((continuous_fst.pow 3).mul (hEval H₃))
  have h0 : (0 : ℝ) ∈ (Prod.fst '' bad)ᶜ := by
    rintro ⟨⟨s, p, v⟩, hb, heq⟩
    change s = 0 at heq
    subst s
    change (perturbationTensor t ht H₁ H₂ H₃ 0).form p v.val v.val ≤ 0 at hb
    simp only [perturbationTensor_apply, zero_mul, zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 3 ≠ 0), add_zero] at hb
    rw [ambientBackground_apply p ht] at hb
    exact (not_le_of_gt (div_pos (Cheeger.pairing_pos _ _ _ ht (ne_zero_of_mem_unit_sphere v))
      (by norm_num))) hb
  filter_upwards [((isClosedMap_fst_of_compactSpace bad hc).isOpen_compl.mem_nhds h0)] with s hs
  intro p v hv
  let u : S := ⟨‖v‖⁻¹ • v, by simp [norm_smul, hv]⟩
  have hu : 0 < (perturbationTensor t ht H₁ H₂ H₃ s).form p u.val u.val := by
    by_contra! h
    exact hs ⟨(s,p,u), h, rfl⟩
  have hv' : v = ‖v‖ • u.val := by simp [u, smul_smul, hv]
  calc
    0 < ‖v‖ * (‖v‖ * (perturbationTensor t ht H₁ H₂ H₃ s).form p u.val u.val) :=
      mul_pos (norm_pos_iff.mpr hv) (mul_pos (norm_pos_iff.mpr hv) hu)
    _ = (perturbationTensor t ht H₁ H₂ H₃ s).form p v v := by
      conv_rhs => rw [hv']
      simp

/-- The perturbed smooth Riemannian metric exists throughout the window, with its
prescribed coefficients on every tangent pair. -/
theorem eventually_exists_perturbedMetric (t : ℝ) (ht : 0 ≤ t) (H₁ H₂ H₃ : AmbientTensor) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∃ g : SmoothMetric, ∀ (p : Base) (X Y : Tangent p),
      g.inner p X Y = backgroundPair p t ht (X.1,X.2) (Y.1,Y.2) +
        s * H₁.form p (ambientVelocityL p X) (ambientVelocityL p Y) +
        s^2 * H₂.form p (ambientVelocityL p X) (ambientVelocityL p Y) +
        s^3 * H₃.form p (ambientVelocityL p X) (ambientVelocityL p Y) := by
  filter_upwards [perturbation_window t ht H₁ H₂ H₃] with s hs
  let A := perturbationTensor t ht H₁ H₂ H₃ s
  refine ⟨metricOfAmbient A.form A.smooth A.symm (fun p X hX => hs p _ ?_), ?_⟩
  · exact fun h => hX ((ambientVelocityL_injective p) (h.trans (ambientVelocityL p).map_zero.symm))
  · intro p X Y
    change A.form p _ _ = _
    rw [perturbationTensor_apply, ambientBackground_apply p ht]
    rfl

end
end LocalHopf.SphereProduct
