/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WidthSixBinning

/-!
# Exact bins of physical width `16*pi`

The core interval has scaled length at most `2*pi*D`; hence these translated
half-open bins have cardinality at most `D/8+1`.
-/

noncomputable section

open Real Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

def wideRepairBinCount (D : ℝ) : ℕ := ⌊D / 8⌋₊ + 1

noncomputable def wideRepairBin
    {S : Type*} (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) (s : S) :
    Fin (wideRepairBinCount D) := by
  let q : ℝ := (coord s - base) / (16 * Real.pi)
  have hden : 0 < (16 : ℝ) * Real.pi := by positivity
  have hqD : q ≤ D / 8 := by
    apply (div_le_iff₀ hden).2
    calc
      coord s - base ≤ 2 * Real.pi * D := (hrange s).2
      _ = D / 8 * (16 * Real.pi) := by ring
  refine ⟨⌊q⌋₊, ?_⟩
  unfold wideRepairBinCount
  exact Nat.lt_succ_of_le (Nat.floor_mono hqD)

theorem wideRepairBin_card_le {D : ℝ} (hD : 0 ≤ D) :
    (Fintype.card (Fin (wideRepairBinCount D)) : ℝ) ≤ D / 8 + 1 := by
  have hf : ((⌊D / 8⌋₊ : ℕ) : ℝ) ≤ D / 8 :=
    Nat.floor_le (div_nonneg hD (by norm_num))
  have hcardNat : Fintype.card (Fin (wideRepairBinCount D)) =
      wideRepairBinCount D := Fintype.card_fin _
  have hcardReal : (Fintype.card (Fin (wideRepairBinCount D)) : ℝ) =
      (wideRepairBinCount D : ℝ) := by exact_mod_cast hcardNat
  rw [hcardReal, wideRepairBinCount, Nat.cast_add, Nat.cast_one]
  linarith

theorem abs_coord_sub_lt_sixteen_pi_of_wideRepairBin_eq
    {S : Type*} {D base : ℝ} {coord : S → ℝ}
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D)
    {s t : S}
    (hbin : wideRepairBin D base coord hrange s =
      wideRepairBin D base coord hrange t) :
    |coord s - coord t| < 16 * Real.pi := by
  let qs : ℝ := (coord s - base) / (16 * Real.pi)
  let qt : ℝ := (coord t - base) / (16 * Real.pi)
  have hden : 0 < (16 : ℝ) * Real.pi := by positivity
  have hqs0 : 0 ≤ qs := div_nonneg (hrange s).1 hden.le
  have hqt0 : 0 ≤ qt := div_nonneg (hrange t).1 hden.le
  have hfloor : ⌊qs⌋₊ = ⌊qt⌋₊ := by
    simpa [wideRepairBin, qs, qt] using congrArg Fin.val hbin
  have hslo : ((⌊qs⌋₊ : ℕ) : ℝ) ≤ qs := Nat.floor_le hqs0
  have hshi : qs < (⌊qs⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one qs
  have htlo : ((⌊qs⌋₊ : ℕ) : ℝ) ≤ qt := by
    rw [hfloor]
    exact Nat.floor_le hqt0
  have hthi : qt < (⌊qs⌋₊ : ℕ) + 1 := by
    rw [hfloor]
    exact Nat.lt_floor_add_one qt
  have hslo' : ((⌊qs⌋₊ : ℕ) : ℝ) * (16 * Real.pi) ≤ coord s - base :=
    (le_div_iff₀ hden).mp hslo
  have hshi' : coord s - base <
      (((⌊qs⌋₊ : ℕ) : ℝ) + 1) * (16 * Real.pi) :=
    (div_lt_iff₀ hden).mp hshi
  have htlo' : ((⌊qs⌋₊ : ℕ) : ℝ) * (16 * Real.pi) ≤ coord t - base :=
    (le_div_iff₀ hden).mp htlo
  have hthi' : coord t - base <
      (((⌊qs⌋₊ : ℕ) : ℝ) + 1) * (16 * Real.pi) :=
    (div_lt_iff₀ hden).mp hthi
  rw [abs_lt]
  constructor <;> nlinarith

variable (Z : ZeroConfig) (T C : ℝ) (P : Params)

noncomputable def coreWideRepairBin
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (z : CoreSimpleLabel Z T C) : Fin (wideRepairBinCount (coreBinD T P)) :=
  wideRepairBin (coreBinD T P) (coreBinBase T C P)
    (coreScaledOrdinate Z T C P) (coreScaledOrdinate_range Z T C P hL hC) z

noncomputable def coreWideRepairEnumeration
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    BinnedEnumeration (CoreSimpleLabel Z T C)
      (Fin (wideRepairBinCount (coreBinD T P))) :=
  fiberBinnedEnumeration (coreWideRepairBin Z T C P hL hC)

theorem coreWideRepairEnumeration_cover
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    ∑ b, (coreWideRepairEnumeration Z T C P hL hC).occupancy b =
      Fintype.card (CoreSimpleLabel Z T C) := by
  exact fiberBinnedEnumeration_cover (coreWideRepairBin Z T C P hL hC)

theorem coreWideRepairBin_card_le
    (hL : 0 < P.L T) (hT : 0 ≤ T) :
    (Fintype.card (Fin (wideRepairBinCount (coreBinD T P))) : ℝ) ≤
      coreBinD T P / 8 + 1 := by
  apply wideRepairBin_card_le
  unfold coreBinD
  positivity

@[simp] theorem coreWideRepairEntry_bin
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (b : Fin (wideRepairBinCount (coreBinD T P)))
    (k : Fin ((coreWideRepairEnumeration Z T C P hL hC).occupancy b)) :
    coreWideRepairBin Z T C P hL hC
      ((coreWideRepairEnumeration Z T C P hL hC).entry b k) = b := by
  exact fiberBinnedEnumeration_at_bin
    (coreWideRepairBin Z T C P hL hC) b k

theorem coreWideRepairEntry_pair_distance_lt
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (b : Fin (wideRepairBinCount (coreBinD T P)))
    (k t : Fin ((coreWideRepairEnumeration Z T C P hL hC).occupancy b)) :
    |coreScaledOrdinate Z T C P
        ((coreWideRepairEnumeration Z T C P hL hC).entry b k) -
      coreScaledOrdinate Z T C P
        ((coreWideRepairEnumeration Z T C P hL hC).entry b t)| <
      16 * Real.pi := by
  apply abs_coord_sub_lt_sixteen_pi_of_wideRepairBin_eq
    (coreScaledOrdinate_range Z T C P hL hC)
  rw [coreWideRepairEntry_bin, coreWideRepairEntry_bin]

end StrictImprovement
end Zeta23

end
