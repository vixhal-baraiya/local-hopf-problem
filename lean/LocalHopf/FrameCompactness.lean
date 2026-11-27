import LocalHopf.MovingPlanes

/-! # A compact set controlling orthonormal frames of the perturbed metrics

All comparisons use ambient velocities, which lie in fixed Euclidean spaces
even when the sphere pair varies. Every neighborhood of the background
orthonormal frames contains all perturbed orthonormal frames for small `s`.
-/
namespace LocalHopf.SphereProduct
open Set Filter Metric Matrix
open scoped Topology Manifold
noncomputable section

abbrev FrameCoordinates := Base × Cheeger.V × Cheeger.V

def TangentPair.toAmbient (w : TangentPair) : FrameCoordinates :=
  (w.point,ambientVelocityL w.point w.first,ambientVelocityL w.point w.second)

private def tangentVelocity (p : Base) (v : Cheeger.V) : Prop :=
  (ambientPoint p).1 ⬝ᵥ v.1 = 0 ∧ (ambientPoint p).2 ⬝ᵥ v.2 = 0

private theorem velocity_range (p : Base) (v : Cheeger.V) :
    (∃ X : Tangent p, ambientVelocityL p X = v) ↔ tangentVelocity p v := by
  have factor (q : Sphere) (w : R3) :
      (∃ X : TangentSpace (𝓡 2) q, (velocity q X).ofLp = w) ↔ q.val.ofLp ⬝ᵥ w = 0 := by
    obtain ⟨a,rfl⟩ := unitSphere.surjective q
    constructor
    · rintro ⟨X,h⟩
      exact (exists_velocity_iff a w).mp ⟨X, by rw [←h]⟩
    · intro h
      obtain ⟨X,hX⟩ := (exists_velocity_iff a w).mpr h
      exact ⟨X,congrArg WithLp.ofLp hX⟩
  constructor
  · rintro ⟨X,rfl⟩
    exact ⟨(factor p.1 _).mp ⟨X.1,rfl⟩,(factor p.2 _).mp ⟨X.2,rfl⟩⟩
  · rintro ⟨h₁,h₂⟩
    obtain ⟨x,hx⟩ := (factor p.1 v.1).mpr h₁
    obtain ⟨y,hy⟩ := (factor p.2 v.2).mpr h₂
    exact ⟨(x,y),Prod.ext hx hy⟩

private def productValue (A : Fin 4 → AmbientTensor) (s : ℝ) (p : Base) (v w : Cheeger.V) :=
  cubicValue s (fun i => (A i).form p v w)

private theorem continuous_value {T : Type*} [TopologicalSpace T] (A : Fin 4 → AmbientTensor)
    {s : T → ℝ} {p : T → Base} {v w : T → Cheeger.V}
    (hs : Continuous s) (hp : Continuous p) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun z => productValue A (s z) (p z) (v z) (w z)) := by
  have H (i : Fin 4) := (((A i).smooth.continuous.comp hp).clm_apply hv).clm_apply hw
  exact (((H 0).add (hs.mul (H 1))).add ((hs.pow 2).mul (H 2))).add ((hs.pow 3).mul (H 3))

private theorem value_scale (A : Fin 4 → AmbientTensor) (p : Base) (v : Cheeger.V) (r s : ℝ) :
    productValue A s p (r • v) (r • v) = r^2 * productValue A s p v v := by
  simp [productValue,cubicValue]
  ring

/-- Uniform ellipticity of the actual tensor polynomial on the ambient vector
space, for fixed background and arbitrary prescribed higher tensors. -/
theorem uniform_ellipticity (A : Fin 4 → AmbientTensor)
    (hpos : ∀ (p : Base) (v : Cheeger.V), v ≠ 0 → 0 < (A 0).form p v v) :
    ∃ c > 0, ∀ᶠ s in 𝓝 (0:ℝ), ∀ (p : Base) (v : Cheeger.V),
      c*‖v‖^2 ≤ cubicValue s (fun i => (A i).form p v v) := by
  let D := ↥(sphere (0:Cheeger.V) 1)
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_sphere ..)
  let eval (z : (ℝ × ℝ) × (Base × D)) :=
    productValue A z.1.1 z.2.1 z.2.2.val z.2.2.val
  have vv : Continuous (fun z : (ℝ × ℝ) × (Base × D) => z.2.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have he : Continuous eval := continuous_value A (continuous_fst.comp continuous_fst)
    (continuous_fst.comp continuous_snd) vv vv
  let bad := {z : (ℝ × ℝ) × (Base × D) | eval z ≤ z.1.2}
  have hc : IsClosed bad := isClosed_le he (by fun_prop)
  have hzero : ((0,0) : ℝ × ℝ) ∈ (Prod.fst '' bad)ᶜ := by
    rintro ⟨⟨⟨s,c⟩,p,v⟩,hb,h⟩
    have hs : s = 0 := congrArg Prod.fst h
    have hco : c = 0 := congrArg Prod.snd h
    subst s; subst c
    exact (not_le_of_gt (hpos p v.val (ne_zero_of_mem_unit_sphere v)))
      (by simpa [bad,eval,productValue,cubicValue] using hb)
  have h := (isClosedMap_fst_of_compactSpace bad hc).isOpen_compl.mem_nhds hzero
  rw [nhds_prod_eq,mem_prod_iff] at h
  obtain ⟨U,hU,V,hV,hUV⟩ := h
  have hV' : V ∈ 𝓝[>] (0:ℝ) := nhdsWithin_le_nhds hV
  obtain ⟨c,hcV,hc0⟩ := Filter.nonempty_of_mem (inter_mem hV' self_mem_nhdsWithin)
  refine ⟨c,hc0,?_⟩
  filter_upwards [hU] with s hs
  intro p v
  by_cases hv : v = 0
  · simp [hv,cubicValue]
  let u : D := ⟨‖v‖⁻¹ • v,by simp [norm_smul,hv]⟩
  have hu : c ≤ productValue A s p u.val u.val := by
    by_contra! hn
    exact hUV ⟨hs,hcV⟩ ⟨((s,c),p,u),hn.le,rfl⟩
  have he : ‖v‖ • u.val = v := by simp [u,smul_smul,hv]
  have hh := value_scale A p u.val ‖v‖ s
  rw [he] at hh
  change _ ≤ productValue A s p v v
  rw [hh,mul_comm c]
  exact mul_le_mul_of_nonneg_left hu (sq_nonneg _)

private def ortho (g : SmoothMetric) (w : TangentPair) : Prop :=
  g.inner w.point w.first w.first = 1 ∧ g.inner w.point w.second w.second = 1 ∧
  g.inner w.point w.first w.second = 0

/-- Ambient images of the genuine orthonormal tangent pairs of the background. -/
def backgroundFrames (t : ℝ) (ht : 0 ≤ t) : Set FrameCoordinates :=
  TangentPair.toAmbient '' {w | ortho (backgroundMetric t ht) w}

/-- The background Stiefel frames control every sufficiently small perturbation.
A neighborhood here is just an open subset of the fixed ambient coordinate space. -/
theorem orthonormal_frames_near_background (t : ℝ) (ht : 0 ≤ t) (χ : Scalar)
    (U : Set FrameCoordinates) (hopen : IsOpen U) (cover : backgroundFrames t ht ⊆ U) :
    ∀ᶠ s in 𝓝 (0:ℝ), ∀ (g : SmoothMetric), Realizes g s (paperCoefficients t ht χ) →
      ∀ (p : Base) (X Y : Tangent p), g.inner p X X = 1 → g.inner p Y Y = 1 → g.inner p X Y = 0 →
        (TangentPair.mk p X Y).toAmbient ∈ U := by
  let A := paperCoefficients t ht χ
  obtain ⟨c,hc,hbound⟩ := uniform_ellipticity A (fun p v hv => by
    change 0 < ambientBackground t p v v
    rw [ambientBackground_apply p ht]
    exact div_pos (Cheeger.pairing_pos _ _ _ ht hv) (by norm_num))
  let R := 1+1/c
  let B := ↥(closedBall (0 : Cheeger.V) R)
  let : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall ..)
  let S := Base × B × B
  let frame (z : S) : FrameCoordinates := (z.1,z.2.1.val,z.2.2.val)
  have hfr : Continuous frame := continuous_fst.prodMk
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  let V (z : ℝ × S) := productValue A z.1 z.2.1
  let v (z : ℝ × S) := z.2.2.1.val
  let w (z : ℝ × S) := z.2.2.2.val
  have hv : Continuous v := continuous_subtype_val.comp ((continuous_fst.comp continuous_snd).comp continuous_snd)
  have hw : Continuous w := continuous_subtype_val.comp ((continuous_snd.comp continuous_snd).comp continuous_snd)
  have hval {a b : ℝ × S → Cheeger.V} (ha : Continuous a) (hb : Continuous b) :
      Continuous (fun z => V z (a z) (b z)) :=
    continuous_value A continuous_fst (continuous_fst.comp continuous_snd) ha hb
  let tan (z : S) (v : Cheeger.V) := tangentVelocity z.1 v
  have htclosed (u : ℝ × S → Cheeger.V) (hu : Continuous u) : IsClosed {z : ℝ × S | tan z.2 (u z)} := by
    let p := fun z : ℝ × S => ambientPoint z.2.1
    have hp : Continuous p := ambientPoint_smooth.continuous.comp (continuous_fst.comp continuous_snd)
    exact (isClosed_eq (hp.fst.dotProduct hu.fst) continuous_const).inter
      (isClosed_eq (hp.snd.dotProduct hu.snd) continuous_const)
  let bad := {z : ℝ × S | frame z.2 ∉ U ∧ tan z.2 (v z) ∧ tan z.2 (w z) ∧
      V z (v z) (v z) = 1 ∧ V z (w z) (w z) = 1 ∧ V z (v z) (w z) = 0}
  have hbad : IsClosed bad := (hopen.isClosed_compl.preimage (hfr.comp continuous_snd)).inter
    ((htclosed v hv).inter ((htclosed w hw).inter ((isClosed_eq (hval hv hv) continuous_const).inter
      ((isClosed_eq (hval hw hw) continuous_const).inter (isClosed_eq (hval hv hw) continuous_const)))))
  have hzero : (0:ℝ) ∈ (Prod.fst '' bad)ᶜ := by
    rintro ⟨⟨s,z⟩,hb,hs⟩
    change s = 0 at hs
    subst s
    obtain ⟨hout,htv,htw,hv1,hw1,hov⟩ := hb
    obtain ⟨X,hX⟩ := (velocity_range z.1 _).mpr htv
    obtain ⟨Y,hY⟩ := (velocity_range z.1 _).mpr htw
    let b := TangentPair.mk z.1 X Y
    have he : b.toAmbient = frame z := Prod.ext rfl (Prod.ext hX hY)
    apply hout
    apply cover
    refine ⟨b,?_,he⟩
    have val (X Y : Tangent z.1) :
        (backgroundMetric t ht).inner z.1 X Y = V (0,z) (ambientVelocityL z.1 X) (ambientVelocityL z.1 Y) := by
      simp [V,productValue,cubicValue,A,paperCoefficients,backgroundTensor]
      rfl
    change _ ∧ _ ∧ _
    exact ⟨(val X X).trans (hX ▸ hv1),(val Y Y).trans (hY ▸ hw1),
      (val X Y).trans (by rw [hX,hY]; exact hov)⟩
  filter_upwards [hbound, (isClosedMap_fst_of_compactSpace bad hbad).isOpen_compl.mem_nhds hzero] with s hb hs
  intro g hg p X Y hX hY hXY
  let normed (Z : Tangent p) (hZ : g.inner p Z Z = 1) : B := by
    refine ⟨ambientVelocityL p Z,?_⟩
    have hh := hb p (ambientVelocityL p Z)
    rw [← hg p Z Z,hZ] at hh
    rw [mem_closedBall,dist_zero_right]
    have hn := norm_nonneg (ambientVelocityL p Z)
    apply le_of_not_gt
    intro h
    have hc' : 0 ≤ 1/c := by positivity
    have h1 : 1 < ‖ambientVelocityL p Z‖ := by dsimp [R] at h; linarith
    have h2 : 1/c < ‖ambientVelocityL p Z‖ := by dsimp [R] at h; linarith
    have h3 := (div_lt_iff₀ hc).mp h2
    nlinarith [mul_pos (sub_pos.mpr h1) (mul_pos hc (lt_trans zero_lt_one h1))]
  let z : S := (p,normed X hX,normed Y hY)
  by_contra hout
  apply hs
  refine ⟨(s,z),?_,rfl⟩
  refine ⟨hout,(velocity_range p _).mp ⟨X,rfl⟩,(velocity_range p _).mp ⟨Y,rfl⟩,?_,?_,?_⟩
  · exact (hg p X X).symm.trans hX
  · exact (hg p Y Y).symm.trans hY
  · exact (hg p X Y).symm.trans hXY

/-- A fixed open cover of the background frames suffices to establish positivity
on every orthonormal pair of the small perturbations. -/
theorem positive_metrics_of_background_cover {ι D P E : Type*} [Finite ι] [TopologicalSpace D]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (t : ℝ) (ht : 0 ≤ t) (χ : Scalar)
    (c : ι → NormalChart P E) (near : ∀ i, (c i).Estimates (paperCoefficients t ht χ))
    (far : D → TangentPair) (S : Set D) (hS : IsCompact S)
    (farCont : ∀ w ∈ S, ContinuousAt (fun q : D × ℝ =>
      (far q.1).numerator (paperCoefficients t ht χ) q.2) (w,0))
    (farPos : ∀ w ∈ S, 0 < (far w).numerator (paperCoefficients t ht χ) 0)
    (U : Set FrameCoordinates) (hopen : IsOpen U) (hbg : backgroundFrames t ht ⊆ U)
    (cover : ∀ w : TangentPair, w.toAmbient ∈ U → (∃ d ∈ S, far d = w) ∨
      ∃ i, ∃ x ∈ (c i).core, ∃ z : E, ‖z‖ ≤ (c i).radius ∧ (c i).frame (x,z) = w) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ g : SmoothMetric, Realizes g s (paperCoefficients t ht χ) ∧
      PositiveSectionalCurvature g := by
  apply positive_metrics_of_charts t ht χ c near far S hS farCont farPos
  filter_upwards [(orthonormal_frames_near_background t ht χ U hopen hbg).filter_mono
    nhdsWithin_le_nhds] with s hs
  exact fun g hg p X Y hx hy hxy => cover ⟨p,X,Y⟩ (hs g hg p X Y hx hy hxy)

end
end LocalHopf.SphereProduct
