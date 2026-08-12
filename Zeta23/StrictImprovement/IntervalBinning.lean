/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.BinnedEnumerationFiber

/-!
# Exact bins of width `8*pi`

This module is the geometric half of the local triple packing.  A finite
family of real coordinates contained in an interval of length at most
`2*pi*D` is assigned to

`floor(D/4) + 1`

half-open bins of width `8*pi`.  Equal bins imply pairwise distance strictly
less than `8*pi`, and the real cardinality of the bin type is at most
`D/4 + 1`.  All statements use Mathlib's exact real `pi` and natural floor;
there is no numerical approximation.
-/

noncomputable section

open Real Finset

namespace Zeta23
namespace StrictImprovement

/-- Number of width-`8*pi` bins sufficient for an interval of length
`2*pi*D`. -/
def intervalBinCount (D : ℝ) : ℕ := ⌊D / 4⌋₊ + 1

/-- Exact floor bin for a coordinate family whose translated coordinates lie
between zero and `2*pi*D`. -/
noncomputable def intervalBin
    {S : Type*} (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) (s : S) : Fin (intervalBinCount D) := by
  let q : ℝ := (coord s - base) / (8 * Real.pi)
  have hden : 0 < (8 : ℝ) * Real.pi := by positivity
  have hq0 : 0 ≤ q := div_nonneg (hrange s).1 hden.le
  have hqD : q ≤ D / 4 := by
    apply (div_le_iff₀ hden).2
    calc
      coord s - base ≤ 2 * Real.pi * D := (hrange s).2
      _ = D / 4 * (8 * Real.pi) := by ring
  refine ⟨⌊q⌋₊, ?_⟩
  unfold intervalBinCount
  exact Nat.lt_succ_of_le (Nat.floor_mono hqD)

/-- The real cardinality of the chosen bin type is at most `D/4+1`. -/
theorem intervalBin_card_le {D : ℝ} (hD : 0 ≤ D) :
    (Fintype.card (Fin (intervalBinCount D)) : ℝ) ≤ D / 4 + 1 := by
  have hf : ((⌊D / 4⌋₊ : ℕ) : ℝ) ≤ D / 4 :=
    Nat.floor_le (div_nonneg hD (by norm_num))
  have hcardNat :
      Fintype.card (Fin (intervalBinCount D)) = intervalBinCount D :=
    Fintype.card_fin _
  have hcardReal :
      (Fintype.card (Fin (intervalBinCount D)) : ℝ) =
        (intervalBinCount D : ℝ) := by
    exact_mod_cast hcardNat
  rw [hcardReal, intervalBinCount, Nat.cast_add, Nat.cast_one]
  linarith

/-- Two labels in the same floor bin have coordinate distance strictly less
than `8*pi`. -/
theorem abs_coord_sub_lt_eight_pi_of_intervalBin_eq
    {S : Type*} {D base : ℝ} {coord : S → ℝ}
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D)
    {s t : S}
    (hbin : intervalBin D base coord hrange s =
      intervalBin D base coord hrange t) :
    |coord s - coord t| < 8 * Real.pi := by
  let qs : ℝ := (coord s - base) / (8 * Real.pi)
  let qt : ℝ := (coord t - base) / (8 * Real.pi)
  have hden : 0 < (8 : ℝ) * Real.pi := by positivity
  have hqs0 : 0 ≤ qs := div_nonneg (hrange s).1 hden.le
  have hqt0 : 0 ≤ qt := div_nonneg (hrange t).1 hden.le
  have hfloor : ⌊qs⌋₊ = ⌊qt⌋₊ := by
    simpa [intervalBin, qs, qt] using congrArg Fin.val hbin
  have hslo : ((⌊qs⌋₊ : ℕ) : ℝ) ≤ qs := Nat.floor_le hqs0
  have hshi : qs < (⌊qs⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one qs
  have htlo : ((⌊qs⌋₊ : ℕ) : ℝ) ≤ qt := by
    rw [hfloor]
    exact Nat.floor_le hqt0
  have hthi : qt < (⌊qs⌋₊ : ℕ) + 1 := by
    rw [hfloor]
    exact Nat.lt_floor_add_one qt
  have hslo' : ((⌊qs⌋₊ : ℕ) : ℝ) * (8 * Real.pi) ≤ coord s - base := by
    exact (le_div_iff₀ hden).mp hslo
  have hshi' : coord s - base <
      (((⌊qs⌋₊ : ℕ) : ℝ) + 1) * (8 * Real.pi) := by
    exact (div_lt_iff₀ hden).mp hshi
  have htlo' : ((⌊qs⌋₊ : ℕ) : ℝ) * (8 * Real.pi) ≤ coord t - base := by
    exact (le_div_iff₀ hden).mp htlo
  have hthi' : coord t - base <
      (((⌊qs⌋₊ : ℕ) : ℝ) + 1) * (8 * Real.pi) := by
    exact (div_lt_iff₀ hden).mp hthi
  rw [abs_lt]
  constructor <;> nlinarith

/-- Any three labels from one bin have diameter strictly below `8*pi`. -/
theorem triple_diameter_lt_eight_pi_of_intervalBin_eq
    {S : Type*} {D base : ℝ} {coord : S → ℝ}
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D)
    {s₀ s₁ s₂ : S}
    (h01 : intervalBin D base coord hrange s₀ =
      intervalBin D base coord hrange s₁)
    (h02 : intervalBin D base coord hrange s₀ =
      intervalBin D base coord hrange s₂) :
    |coord s₀ - coord s₁| < 8 * Real.pi ∧
      |coord s₀ - coord s₂| < 8 * Real.pi ∧
      |coord s₁ - coord s₂| < 8 * Real.pi := by
  refine ⟨abs_coord_sub_lt_eight_pi_of_intervalBin_eq hrange h01,
    abs_coord_sub_lt_eight_pi_of_intervalBin_eq hrange h02, ?_⟩
  apply abs_coord_sub_lt_eight_pi_of_intervalBin_eq hrange
  exact h01.symm.trans h02

/-- The lossless fiber enumeration of interval bins has exact coverage and
the bin-count bound required by the hyperbolic target theorem. -/
theorem interval_fiber_binning_interfaces
    {S : Type*} [Fintype S] [DecidableEq S]
    {D base : ℝ} (hD : 0 ≤ D) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) :
    let bin := intervalBin D base coord hrange
    (∑ b, (fiberBinnedEnumeration bin).occupancy b = Fintype.card S) ∧
      (Fintype.card (Fin (intervalBinCount D)) : ℝ) ≤ D / 4 + 1 := by
  dsimp
  exact ⟨fiberBinnedEnumeration_cover _, intervalBin_card_le hD⟩

end StrictImprovement
end Zeta23
