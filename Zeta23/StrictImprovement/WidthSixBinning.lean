/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.FourBlockDefect
import Zeta23.StrictImprovement.ZetaCoreBinning

/-!
# Exact width-six bins for packed four-point blocks

Coordinates in an interval of length `2*pi*D` are assigned to
`floor(D/6)+1` half-open bins of width `12*pi`.  This is the geometric and
lossless-enumeration interface needed by the `(q,d)=(4,6)` route.

No sampled coordinate or approximate value of `pi` occurs here.  This remains
a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Real Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

def widthSixBinCount (D : ℝ) : ℕ := ⌊D / 6⌋₊ + 1

noncomputable def widthSixBin
    {S : Type*} (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) (s : S) : Fin (widthSixBinCount D) := by
  let q : ℝ := (coord s - base) / (12 * Real.pi)
  have hden : 0 < (12 : ℝ) * Real.pi := by positivity
  have hq0 : 0 ≤ q := div_nonneg (hrange s).1 hden.le
  have hqD : q ≤ D / 6 := by
    apply (div_le_iff₀ hden).2
    calc
      coord s - base ≤ 2 * Real.pi * D := (hrange s).2
      _ = D / 6 * (12 * Real.pi) := by ring
  refine ⟨⌊q⌋₊, ?_⟩
  unfold widthSixBinCount
  exact Nat.lt_succ_of_le (Nat.floor_mono hqD)

theorem widthSixBin_card_le {D : ℝ} (hD : 0 ≤ D) :
    (Fintype.card (Fin (widthSixBinCount D)) : ℝ) ≤ D / 6 + 1 := by
  have hf : ((⌊D / 6⌋₊ : ℕ) : ℝ) ≤ D / 6 :=
    Nat.floor_le (div_nonneg hD (by norm_num))
  have hcardNat :
      Fintype.card (Fin (widthSixBinCount D)) = widthSixBinCount D :=
    Fintype.card_fin _
  have hcardReal :
      (Fintype.card (Fin (widthSixBinCount D)) : ℝ) =
        (widthSixBinCount D : ℝ) := by
    exact_mod_cast hcardNat
  rw [hcardReal, widthSixBinCount, Nat.cast_add, Nat.cast_one]
  exact add_le_add_right hf 1

theorem abs_coord_sub_lt_twelve_pi_of_widthSixBin_eq
    {S : Type*} {D base : ℝ} {coord : S → ℝ}
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D)
    {s t : S}
    (hbin : widthSixBin D base coord hrange s =
      widthSixBin D base coord hrange t) :
    |coord s - coord t| < 12 * Real.pi := by
  let qs : ℝ := (coord s - base) / (12 * Real.pi)
  let qt : ℝ := (coord t - base) / (12 * Real.pi)
  have hden : 0 < (12 : ℝ) * Real.pi := by positivity
  have hqs0 : 0 ≤ qs := div_nonneg (hrange s).1 hden.le
  have hqt0 : 0 ≤ qt := div_nonneg (hrange t).1 hden.le
  have hfloor : ⌊qs⌋₊ = ⌊qt⌋₊ := by
    simpa [widthSixBin, qs, qt] using congrArg Fin.val hbin
  have hslo : ((⌊qs⌋₊ : ℕ) : ℝ) ≤ qs := Nat.floor_le hqs0
  have hshi : qs < (⌊qs⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one qs
  have htlo : ((⌊qs⌋₊ : ℕ) : ℝ) ≤ qt := by
    rw [hfloor]
    exact Nat.floor_le hqt0
  have hthi : qt < (⌊qs⌋₊ : ℕ) + 1 := by
    rw [hfloor]
    exact Nat.lt_floor_add_one qt
  have hslo' : ((⌊qs⌋₊ : ℕ) : ℝ) * (12 * Real.pi) ≤ coord s - base :=
    (le_div_iff₀ hden).mp hslo
  have hshi' : coord s - base <
      (((⌊qs⌋₊ : ℕ) : ℝ) + 1) * (12 * Real.pi) :=
    (div_lt_iff₀ hden).mp hshi
  have htlo' : ((⌊qs⌋₊ : ℕ) : ℝ) * (12 * Real.pi) ≤ coord t - base :=
    (le_div_iff₀ hden).mp htlo
  have hthi' : coord t - base <
      (((⌊qs⌋₊ : ℕ) : ℝ) + 1) * (12 * Real.pi) :=
    (div_lt_iff₀ hden).mp hthi
  rw [abs_lt]
  constructor <;> nlinarith

variable (Z : ZeroConfig) (T C : ℝ) (P : Params)

noncomputable def coreWidthSixBin
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (z : CoreSimpleLabel Z T C) : Fin (widthSixBinCount (coreBinD T P)) :=
  widthSixBin (coreBinD T P) (coreBinBase T C P)
    (coreScaledOrdinate Z T C P) (coreScaledOrdinate_range Z T C P hL hC) z

noncomputable def coreWidthSixEnumeration
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    BinnedEnumeration (CoreSimpleLabel Z T C)
      (Fin (widthSixBinCount (coreBinD T P))) :=
  fiberBinnedEnumeration (coreWidthSixBin Z T C P hL hC)

theorem coreWidthSixEnumeration_cover
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    ∑ b, (coreWidthSixEnumeration Z T C P hL hC).occupancy b =
      Fintype.card (CoreSimpleLabel Z T C) := by
  exact fiberBinnedEnumeration_cover (coreWidthSixBin Z T C P hL hC)

theorem coreWidthSixBin_card_le
    (hL : 0 < P.L T) (hT : 0 ≤ T) :
    (Fintype.card (Fin (widthSixBinCount (coreBinD T P))) : ℝ) ≤
      coreBinD T P / 6 + 1 := by
  apply widthSixBin_card_le
  unfold coreBinD
  positivity

@[simp] theorem corePackedFourIndex_bin
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (q : PackedFour (coreWidthSixEnumeration Z T C P hL hC)) (k : Fin 4) :
    coreWidthSixBin Z T C P hL hC
      (packedFourIndex (coreWidthSixEnumeration Z T C P hL hC) q k) = q.1 := by
  exact fiberBinnedEnumeration_at_bin
    (coreWidthSixBin Z T C P hL hC) q.1 _

theorem corePackedFour_pair_distance_lt_twelve_pi
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (q : PackedFour (coreWidthSixEnumeration Z T C P hL hC))
    (r t : Fin 4) :
    |coreScaledOrdinate Z T C P
        (packedFourIndex (coreWidthSixEnumeration Z T C P hL hC) q r) -
      coreScaledOrdinate Z T C P
        (packedFourIndex (coreWidthSixEnumeration Z T C P hL hC) q t)| <
      12 * Real.pi := by
  apply abs_coord_sub_lt_twelve_pi_of_widthSixBin_eq
    (coreScaledOrdinate_range Z T C P hL hC)
  rw [corePackedFourIndex_bin, corePackedFourIndex_bin]

end StrictImprovement
end Zeta23

end
