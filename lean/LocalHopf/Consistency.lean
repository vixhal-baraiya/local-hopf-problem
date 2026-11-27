/-
Copyright (c) 2026. Released under the MIT License (see ../../LICENSE).

# The hypotheses of `LocalHopfInput` are jointly consistent

A theorem with contradictory hypotheses is vacuous. This file builds a (geometrically meaningless)
one-point model of `LocalHopfInput`, which shows that the fields can be satisfied simultaneously.
It says nothing about whether the *real* geometric objects satisfy them; that is what PROOF.md and
`verification/` establish.
-/
import LocalHopf.Main

namespace LocalHopf

open Set Filter Topology Profiles

/-- A one-point model of the inputs. -/
noncomputable def toyInput : LocalHopfInput where
  Met := Unit
  dist := { d := fun _ _ _ => 0, nonneg := fun _ _ _ => le_rfl,
            triangle := fun _ _ _ _ => by simp, mono := fun _ _ _ _ _ => le_rfl }
  PosSec := fun _ => True
  gprod := ()
  g := fun _ => ()
  radius := fun _ => ⟨1, (zero_lt_one : (0 : ℝ) < 1)⟩
  G := fun _ _ => ()
  g_tendsto := fun _ => tendsto_const_nhds
  G_tendsto := fun _ _ => tendsto_const_nhds
  𝒩 := Unit
  Z := Unit
  ρ := fun _ => 0
  ρ_cont := continuous_const
  ρ_nonneg := fun _ => le_rfl
  Ω := univ
  Ω_dense := dense_univ
  Sig_dense := fun x _ => subset_closure ⟨mem_univ x, rfl⟩
  nx := fun _ => 0
  ny := fun _ => 0
  nz := fun _ => 1
  xp := fun _ => 0
  zp := fun _ => 0
  sep := fun _ => 0
  frame := fun _ _ => by simp
  Fx := fun _ _ => 1
  Fy := fun _ _ => 1
  A := fun _ _ => 0
  B := fun _ _ => 0
  M1 := fun _ _ => 0
  M2 := fun _ _ => 0
  u := fun _ _ _ => 1
  U₂ := fun _ _ => 0
  U₃ := fun t _ => hh t * mu t
  U₂_cont := fun _ _ => continuous_const
  U₃_cont := fun _ _ => continuous_const
  sign := fun _ _ _ => trivial
  tube := fun _ => ⟨fun _ => True, fun _ => (), 1, 0, ⟨1 / 2, by norm_num, by norm_num⟩, one_pos,
    fun _ _ _ _ => by norm_num, fun _ _ _ h => absurd trivial h⟩
  U₂_normal_form := fun _ _ _ _ => by simp [V2form]
  certificate := fun _ _ _ _ => by
    simp [Gcal, frob]; norm_num
  U₃_on_Sig := fun _ _ _ _ _ => rfl

end LocalHopf
