/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaCore
import Zeta23.Assembly
import Zeta23.Tail

/-!
# The width-three boundary loss is negligible

The core-triple construction removes simple on-line zeros within distance
three of either endpoint of the main window.  This file proves, rather than
assumes, that the resulting `excludedSimpleCount` is `o(N(T,2T))`.

The finite-height proof first embeds the excluded subtype labels back into
the ambient complex plane and bounds them by two explicit zero windows.  The
two outer pieces use the frozen `NII` estimate; the two inner pieces comprise
six unit windows and are `O(log T)`.

This is a source draft pending the pinned Lean build.
-/

noncomputable section

open Filter Asymptotics Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace StrictImprovement

open ZeroSide

/-- The coercion from the finite enlarged-window label type to `ℂ`, as an
explicit embedding so that `Finset.map` preserves cardinality. -/
private def ziCoeEmbedding (Z : ZeroConfig) (T : ℝ) : ZI Z T ↪ ℂ where
  toFun z := z
  inj' _ _ h := Subtype.ext h

/-- The excluded simple labels, viewed as actual complex zeros. -/
private def excludedSimpleComplex (Z : ZeroConfig) (T C : ℝ) : Finset ℂ :=
  ((nearSimple Z T) \ coreSimple Z T C).map (ziCoeEmbedding Z T)

private lemma card_excludedSimpleComplex
    (Z : ZeroConfig) (T C : ℝ) :
    #(excludedSimpleComplex Z T C) = excludedSimpleCount Z T C := by
  simp [excludedSimpleComplex, excludedSimpleCount]

/-- Exact decomposition of the enlarged-window simple labels into the
selected core and its excluded boundary. -/
theorem coreCard_add_excluded_eq_s1
    (Z : ZeroConfig) (T C : ℝ) (P : Params)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fintype.card (CoreSimpleLabel Z T C) + excludedSimpleCount Z T C =
      Z.s1 T := by
  have hsub := coreSimple_subset_blockData_S₁ Z T C P hconj
  have hsplit := Finset.card_sdiff_add_card_eq_card hsub
  rw [card_blockData_S₁_sdiff_core Z T C P hconj] at hsplit
  have hs1mk := ZeroSide.s1_eq_mk Z T (ZeroSide.evalVec Z T P)
    (ZeroSide.evalVec_reflect hconj)
  have hs1card : #((ZeroSide.blockData Z T P hconj).S₁) = Z.s1 T := by
    change (ZeroSide.blockData Z T P hconj).s₁ = Z.s1 T
    exact hs1mk.symm
  rw [hs1card] at hsplit
  simpa only [Fintype.card_coe, add_comm] using hsplit

/-- The main-window simple count is no larger than the selected core plus
the exact boundary loss. -/
theorem N0s_le_coreCard_add_excluded
    (Z : ZeroConfig) {T C : ℝ} (hT : 0 ≤ T) (P : Params)
    (hconj : ZeroSide.PhiHatConj T P) :
    Z.N0s T (2 * T) ≤
      Fintype.card (CoreSimpleLabel Z T C) + excludedSimpleCount Z T C := by
  have hs1main : Z.N0s T (2 * T) ≤ Z.s1 T := by
    have hs1 : Z.s1 T = Z.N0s (T - D0 T) (2 * T + D0 T) := rfl
    rw [hs1,
      Assembly.N0s_add Z (a := T - D0 T) (b := T)
        (c := 2 * T + D0 T) (by positivity) (by linarith [Real.sqrt_nonneg T]),
      Assembly.N0s_add Z (a := T) (b := 2 * T)
        (c := 2 * T + D0 T) (by linarith) (by positivity)]
    omega
  rw [coreCard_add_excluded_eq_s1 Z T C P hconj]
  exact hs1main

/-- The selected core has density at most one, up to the already-frozen
outer boundary count `NII`. -/
theorem coreCard_le_N_add_NII
    (Z : ZeroConfig) {T C : ℝ} (hT : 0 ≤ T) (P : Params)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fintype.card (CoreSimpleLabel Z T C) ≤
      Z.N T (2 * T) + Assembly.NII Z T := by
  have hcore : Fintype.card (CoreSimpleLabel Z T C) ≤ Z.s1 T := by
    have h := coreCard_add_excluded_eq_s1 Z T C P hconj
    omega
  have hs1 := Assembly.s1_le Z hT
  have hchain := Z.trivial_chain T (2 * T)
  have hsimple : Z.N0s T (2 * T) ≤ Z.N T (2 * T) :=
    hchain.1.trans (hchain.2.1.trans hchain.2.2.1)
  omega

/-- Exact finite-window majorant for the boundary labels.  No asymptotics or
local-count hypothesis enters this statement. -/
theorem excludedSimpleCount_le_two_windows
    (Z : ZeroConfig) (T C : ℝ) :
    excludedSimpleCount Z T C ≤
      Z.N (T - D0 T) (T + C) + Z.N (2 * T - C) (2 * T + D0 T) := by
  let S := excludedSimpleComplex Z T C
  let Slo := S.filter fun ρ => ρ.im ≤ T + C
  let Shi := S.filter fun ρ => ¬ ρ.im ≤ T + C
  have hsplit : #Slo + #Shi = #S := by
    exact Finset.card_filter_add_card_filter_not S
  have hloSub : (↑Slo : Set ℂ) ⊆ Z.window (T - D0 T) (T + C) := by
    intro ρ hρ
    change ρ ∈ Slo at hρ
    rw [Slo, Finset.mem_filter] at hρ
    obtain ⟨hρS, hρup⟩ := hρ
    change ρ ∈ excludedSimpleComplex Z T C at hρS
    rw [excludedSimpleComplex, Finset.mem_map] at hρS
    obtain ⟨z, hz, rfl⟩ := hρS
    have hZI := (mem_ZIprime_iff Z T).mp ((mem_ZI Z T).mp z.2)
    exact ⟨hZI.1, hZI.2.1, hρup⟩
  have hhiSub : (↑Shi : Set ℂ) ⊆ Z.window (2 * T - C) (2 * T + D0 T) := by
    intro ρ hρ
    change ρ ∈ Shi at hρ
    rw [Shi, Finset.mem_filter] at hρ
    obtain ⟨hρS, hρcut⟩ := hρ
    change ρ ∈ excludedSimpleComplex Z T C at hρS
    rw [excludedSimpleComplex, Finset.mem_map] at hρS
    obtain ⟨z, hz, rfl⟩ := hρS
    rw [Finset.mem_sdiff] at hz
    have hZI := (mem_ZIprime_iff Z T).mp ((mem_ZI Z T).mp z.2)
    have hstart : T + C ≤ (z : ℂ).im := le_of_lt (lt_of_not_ge hρcut)
    have hend : 2 * T - C < (z : ℂ).im := by
      by_contra hn
      apply hz.2
      rw [coreSimple, Finset.mem_filter]
      exact ⟨hz.1, hstart, le_of_not_gt hn⟩
    exact ⟨hZI.1, hend, hZI.2.2⟩
  have hlo0 := Z.ncard_le_finsum_mult (T - D0 T) (T + C) hloSub
  have hlo1 := Z.finsum_mult_mono (T - D0 T) (T + C) hloSub subset_rfl
  have hlo : #Slo ≤ Z.N (T - D0 T) (T + C) := by
    rw [Set.ncard_coe_finset] at hlo0
    exact hlo0.trans (by simpa [ZeroConfig.N] using hlo1)
  have hhi0 := Z.ncard_le_finsum_mult (2 * T - C) (2 * T + D0 T) hhiSub
  have hhi1 := Z.finsum_mult_mono (2 * T - C) (2 * T + D0 T) hhiSub subset_rfl
  have hhi : #Shi ≤ Z.N (2 * T - C) (2 * T + D0 T) := by
    rw [Set.ncard_coe_finset] at hhi0
    exact hhi0.trans (by simpa [ZeroConfig.N] using hhi1)
  rw [← card_excludedSimpleComplex Z T C]
  omega

/-- The two interior strips of width three contain at most six unit-window
local counts. -/
theorem interior_three_count_le
    (Z : ZeroConfig) {A₀ T : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ,
      (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hT : Tail.T₀ ≤ T) :
    (Z.N T (T + 3) : ℝ) + (Z.N (2 * T - 3) (2 * T) : ℝ) ≤
      6 * A₀ * Real.log (4 * T) := by
  have hT0 : 0 < T := Tail.T₀_pos.trans_le hT
  have hT300 : (300 : ℝ) ≤ T := hT
  have hlog : ∀ u : ℝ, 0 ≤ u → u + 3 ≤ 4 * T →
      A₀ * Real.log (|u| + 3) ≤ A₀ * Real.log (4 * T) := by
    intro u hu huT
    rw [abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) huT) (by linarith)
  have h0 := (hloc T).trans (hlog T (by linarith) (by linarith))
  have h1 := (hloc (T + 1)).trans
    (hlog (T + 1) (by linarith) (by linarith))
  have h2 := (hloc (T + 2)).trans
    (hlog (T + 2) (by linarith) (by linarith))
  have h3 := (hloc (2 * T - 3)).trans
    (hlog (2 * T - 3) (by linarith) (by linarith))
  have h4 := (hloc (2 * T - 2)).trans
    (hlog (2 * T - 2) (by linarith) (by linarith))
  have h5 := (hloc (2 * T - 1)).trans
    (hlog (2 * T - 1) (by linarith) (by linarith))
  have hleft :
      (Z.N T (T + 3) : ℝ) =
        Z.N T (T + 1) + Z.N (T + 1) (T + 2) + Z.N (T + 2) (T + 3) := by
    rw [Assembly.N_add Z (a := T) (b := T + 1) (c := T + 3)
      (by linarith) (by linarith),
      Assembly.N_add Z (a := T + 1) (b := T + 2) (c := T + 3)
        (by linarith) (by linarith)]
    push_cast
  have hright :
      (Z.N (2 * T - 3) (2 * T) : ℝ) =
        Z.N (2 * T - 3) (2 * T - 2) +
          Z.N (2 * T - 2) (2 * T - 1) +
          Z.N (2 * T - 1) (2 * T) := by
    rw [Assembly.N_add Z (a := 2 * T - 3) (b := 2 * T - 2) (c := 2 * T)
      (by linarith) (by linarith),
      Assembly.N_add Z (a := 2 * T - 2) (b := 2 * T - 1) (c := 2 * T)
        (by linarith) (by linarith)]
    push_cast
  rw [hleft, hright]
  linarith

/-- Effective finite-height bound for the exact width-three loss. -/
theorem excludedSimpleCount_three_le
    (Z : ZeroConfig) {A₀ T : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ,
      (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hT : Tail.T₀ ≤ T) :
    (excludedSimpleCount Z T 3 : ℝ) ≤
      9 * A₀ * Real.sqrt T * Real.log (4 * T) := by
  have hexact := excludedSimpleCount_le_two_windows Z T 3
  rw [Assembly.N_add Z (a := T - D0 T) (b := T) (c := T + 3)
      (by positivity) (by norm_num),
    Assembly.N_add Z (a := 2 * T - 3) (b := 2 * T) (c := 2 * T + D0 T)
      (by norm_num) (by positivity)] at hexact
  have hexactNat :
      excludedSimpleCount Z T 3 ≤
        Assembly.NII Z T +
          (Z.N T (T + 3) + Z.N (2 * T - 3) (2 * T)) := by
    unfold Assembly.NII
    omega
  have hexactR :
      (excludedSimpleCount Z T 3 : ℝ) ≤
        (Assembly.NII Z T : ℝ) +
          ((Z.N T (T + 3) : ℝ) + (Z.N (2 * T - 3) (2 * T) : ℝ)) := by
    exact_mod_cast hexactNat
  have houter := Tail.NII_le Z hA₀ hloc hT
  have hinner := interior_three_count_le Z hA₀ hloc hT
  have hsqrt : 1 ≤ Real.sqrt T := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    exact (show (1 : ℝ) ≤ Tail.T₀ by norm_num [Tail.T₀]).trans hT
  have hlog0 : 0 ≤ Real.log (4 * T) :=
    zero_le_one.trans (Tail.one_le_log_four_mul hT)
  have hAl : 0 ≤ A₀ * Real.log (4 * T) :=
    mul_nonneg (by linarith) hlog0
  have hscale : A₀ * Real.log (4 * T) ≤
      Real.sqrt T * (A₀ * Real.log (4 * T)) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrt hAl
  nlinarith [hexactR, houter, hinner, hscale]

/-- The width-three boundary correction is negligible relative to the main
dyadic zero count. -/
theorem excludedSimpleCount_three_isLittleO
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    (fun T => (excludedSimpleCount Z T 3 : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hR.local_count
  have hbound : ∀ᶠ T in atTop,
      (excludedSimpleCount Z T 3 : ℝ) ≤
        18 * A₀ * Real.sqrt T * l T := by
    filter_upwards [eventually_ge_atTop Tail.T₀] with T hT
    have h := excludedSimpleCount_three_le Z hA₀ hloc hT
    have hlog := Tail.log_four_mul_le_two_mul_l hT
    have hcoef : 0 ≤ 9 * A₀ * Real.sqrt T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlog hcoef]
  have hO :
      (fun T => (excludedSimpleCount Z T 3 : ℝ)) =O[atTop]
        (fun T => Real.sqrt T * l T) := by
    refine IsBigO.of_bound (18 * A₀) ?_
    filter_upwards [hbound, eventually_ge_atTop 0, Assembly.eventually_l_pos]
      with T h hT hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    simpa [mul_assoc] using h
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl Z hR
      Assembly.isLittleO_sqrt_mul_l_Tl)

end StrictImprovement
end Zeta23

end
