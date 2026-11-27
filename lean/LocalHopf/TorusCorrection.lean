import LocalHopf.EquatorExtension
import LocalHopf.TorusPoisson
import LocalHopf.SectionalCoefficients
import LocalHopf.TorusFrame

namespace LocalHopf.SphereProduct
open Function Filter Real Matrix
open scoped Topology ContDiff
noncomputable section

private def longitudeVector (a : ℝ) : R3 := ![cos a,sin a,0]

private theorem equator_velocity (a : ℝ) :
    HasDerivAt longitudeVector ((Pi.single 2 1 : R3) ⨯₃ longitudeVector a) a := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [longitudeVector,crossProduct] using Real.hasDerivAt_cos a
  · simpa [longitudeVector,crossProduct] using Real.hasDerivAt_sin a
  · simpa [longitudeVector,crossProduct] using hasDerivAt_const a (0 : ℝ)

/-- The background induced on the equator in the exact coordinates used by
the Poisson equation. Both velocities differentiate the parameterization. -/
theorem equator_metric (t : ℝ) (ht : 0 ≤ t) (m d : ℝ) :
    let P := fun a b => (equatorPoint (a+b),equatorPoint (a-b))
    let U := deriv (fun a => ambientPoint (P a d)) m
    let V := deriv (fun b => ambientPoint (P m b)) d
    let g := ambientBackground t (P m d)
    g U U = 1 / Profiles.hh t ∧ g U V = 0 ∧ g V V = 1 := by
  intro P U V g
  let p := P m d
  let n := axis 2 p
  have hu : U = K (point₁ p) (point₂ p) n := by
    have first := (equator_velocity (m+d)).scomp m ((hasDerivAt_id' m).add_const d)
    have second := (equator_velocity (m-d)).scomp m ((hasDerivAt_id' m).sub_const d)
    change deriv (fun r : ℝ => (longitudeVector (r+d),longitudeVector (r-d))) m =
      ((Pi.single 2 1 : R3) ⨯₃ longitudeVector (m+d),(Pi.single 2 1 : R3) ⨯₃ longitudeVector (m-d))
    simpa only [one_smul,Function.comp_def] using (first.prodMk second).deriv
  have hv : V = J (point₁ p) (point₂ p) n := by
    have first := (equator_velocity (m+d)).scomp d ((hasDerivAt_id' d).const_add m)
    have second := (equator_velocity (m-d)).scomp d ((hasDerivAt_id' d).const_sub m)
    change deriv (fun r : ℝ => (longitudeVector (m+r),longitudeVector (m-r))) d =
      ((Pi.single 2 1 : R3) ⨯₃ longitudeVector (m+d),-((Pi.single 2 1 : R3) ⨯₃ longitudeVector (m-d)))
    simpa only [one_smul,neg_smul,Function.comp_def] using (first.prodMk second).deriv
  have hx : n ⬝ᵥ point₁ p = 0 := by
    change Pi.single 2 (1:ℝ) ⬝ᵥ longitudeVector (m+d) = 0
    simp [single_dotProduct,longitudeVector]
  have hy : n ⬝ᵥ point₂ p = 0 := by
    change Pi.single 2 (1:ℝ) ⬝ᵥ longitudeVector (m-d) = 0
    simp [single_dotProduct,longitudeVector]
  have hz : axis 2 p ⬝ᵥ n = 1 := by
    change Pi.single 2 (1:ℝ) ⬝ᵥ (Pi.single 2 1 : R3) = 1
    simp
  obtain ⟨uu,uv,_,vv⟩ := rotationFlat_longitude t ht p n hx hy (axis 2)
  rw [hz] at uu vv
  rw [hu,hv]
  exact ⟨uu,uv,vv⟩

/-- The §6 potential on the sphere product. The hypotheses specify the rotation degree and the four
sample values averaged in Proposition 6.1. -/
theorem exists_torus_correction (t : ℝ) (ht : 0 ≤ t) (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (h₁ : ∀ b, Periodic (fun a => f (a,b)) (2*π)) (h₂ : ∀ a, Periodic (fun b => f (a,b)) (2*π))
    (degree : ∀ d, ∃ w a b c e j k : ℝ, ∀ m, f (m+d,m-d) = trig3 w a b c e j k m)
    (samples : ∀ d, let V := fun m => f (m+d,m-d)
      (V 0 + V (π/2) + V π + V (3*π/2))/4 = Profiles.mu t) :
    ∃ χ : Scalar,
      let pull := fun m d => χ (equatorPoint (m+d),equatorPoint (m-d))
      (∀ d, (∫ m in (0:ℝ)..2*π, pull m d) = 0) ∧
      (∀ m d, Profiles.hh t * iteratedDeriv 2 (fun x => pull x d) m +
        iteratedDeriv 2 (pull m) d = f (m+d,m-d)-Profiles.mu t) ∧
      (∀ p : Base, let z := longitude (point₁ p); let w := longitude (point₂ p)
        1/2 ≤ Complex.normSq z → 1/2 ≤ Complex.normSq w →
          χ p = χ (equatorPoint z.arg,equatorPoint w.arg)) ∧
      ∀ᶠ s in 𝓝 (0:ℝ), ∃ g : SmoothMetric, Realizes g s (paperCoefficients t ht χ) := by
  obtain ⟨u,su,p₁,p₂,zero,lap⟩ := TorusPoisson.exists_potential _ _ (Profiles.hh_pos ht) f hf h₁ h₂ (fun d => by
    obtain ⟨w,a,b,c,e,j,k,h⟩ := degree d
    have hw := samples d
    dsimp only at hw
    simp only [h,trig3_four_point_mean] at hw
    exact ⟨a,b,c,e,j,k,hw ▸ h⟩)
  obtain ⟨χ,eq,band⟩ := extend_equator su p₁ p₂
  exact ⟨χ,by simpa only [eq] using zero,by simpa only [eq] using lap,
    by simpa only [eq] using band,paper_metrics_realize t ht χ⟩

-- A mixed longitude mode tests both periods and the opposite-rotation derivative.
example (t : ℝ) (ht : 0 ≤ t) : ∃ χ : Scalar,
    let u := fun m d => χ (equatorPoint (m+d),equatorPoint (m-d))
    ∀ m d, Profiles.hh t * iteratedDeriv 2 (fun x => u x d) m + iteratedDeriv 2 (u m) d =
      cos (m+3*d) := by
  let f (p : ℝ × ℝ) := Profiles.mu t + cos (2*p.1-p.2)
  have p₁ (y : ℝ) : Periodic (fun x => f (x,y)) (2*π) := by
    intro x; dsimp [f]
    rw [show 2*(x+2*π)-y = (2*x-y+2*π)+2*π by ring,cos_add_two_pi,cos_add_two_pi]
  have p₂ (x : ℝ) : Periodic (fun y => f (x,y)) (2*π) := by
    intro y; dsimp [f]
    rw [show 2*x-(y+2*π) = (2*x-y)-2*π by ring,cos_sub_two_pi]
  have angle (m d : ℝ) : 2*(m+d)-(m-d) = m+3*d := by ring
  have orbit (d m : ℝ) : f (m+d,m-d) =
      trig3 (Profiles.mu t) (cos (3*d)) (-sin (3*d)) 0 0 0 0 m := by
    simp [f,trig3,angle,cos_add]; ring
  obtain ⟨χ,_,lap,_⟩ := exists_torus_correction t ht f (by dsimp [f]; fun_prop) p₁ p₂
    (fun d => ⟨_,_,_,_,_,_,_,orbit d⟩) (fun d => by simp only [orbit,trig3_four_point_mean])
  exact ⟨χ,fun m d => by simpa [f,angle] using lap m d⟩

end
end LocalHopf.SphereProduct
