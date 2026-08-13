/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WidthSixBinning

/-!
# Rational bins consuming the full spectral certificate domain

The retained external certificate covers every ordered four-point block of
diameter at most `264/7`.  This file partitions a scaled interval of length
`2*pi*D` into half-open bins of that rational width.  The resulting number of
bins is at most `7*pi*D/132 + 1`.
-/

noncomputable section

open Real Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

/-- Number of half-open bins of width `264/7` needed for scaled length
`2*pi*D`. -/
def certificateSlackBinCount (D : ℝ) : ℕ :=
  ⌊(7 * Real.pi / 132) * D⌋₊ + 1

noncomputable def certificateSlackBin
    {S : Type*} (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) (s : S) :
    Fin (certificateSlackBinCount D) := by
  let q : ℝ := (coord s - base) / ((264 : ℝ) / 7)
  have hden : 0 < (264 : ℝ) / 7 := by norm_num
  have hqD : q ≤ (7 * Real.pi / 132) * D := by
    apply (div_le_iff₀ hden).2
    calc
      coord s - base ≤ 2 * Real.pi * D := (hrange s).2
      _ = (7 * Real.pi / 132) * D * ((264 : ℝ) / 7) := by ring
  refine ⟨⌊q⌋₊, ?_⟩
  unfold certificateSlackBinCount
  exact Nat.lt_succ_of_le (Nat.floor_mono hqD)

theorem certificateSlackBin_card_le {D : ℝ} (hD : 0 ≤ D) :
    (Fintype.card (Fin (certificateSlackBinCount D)) : ℝ) ≤
      (7 * Real.pi / 132) * D + 1 := by
  have hcoef : 0 ≤ (7 * Real.pi / 132 : ℝ) := by positivity
  have hf :
      ((⌊(7 * Real.pi / 132) * D⌋₊ : ℕ) : ℝ) ≤
        (7 * Real.pi / 132) * D :=
    Nat.floor_le (mul_nonneg hcoef hD)
  have hcardNat :
      Fintype.card (Fin (certificateSlackBinCount D)) =
        certificateSlackBinCount D := Fintype.card_fin _
  have hcardReal :
      (Fintype.card (Fin (certificateSlackBinCount D)) : ℝ) =
        (certificateSlackBinCount D : ℝ) := by
    exact_mod_cast hcardNat
  rw [hcardReal, certificateSlackBinCount, Nat.cast_add, Nat.cast_one]
  linarith

theorem abs_coord_sub_lt_certificateDiameter_of_bin_eq
    {S : Type*} {D base : ℝ} {coord : S → ℝ}
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D)
    {s t : S}
    (hbin : certificateSlackBin D base coord hrange s =
      certificateSlackBin D base coord hrange t) :
    |coord s - coord t| < (264 : ℝ) / 7 := by
  let qs : ℝ := (coord s - base) / ((264 : ℝ) / 7)
  let qt : ℝ := (coord t - base) / ((264 : ℝ) / 7)
  have hden : 0 < (264 : ℝ) / 7 := by norm_num
  have hqs0 : 0 ≤ qs := div_nonneg (hrange s).1 hden.le
  have hqt0 : 0 ≤ qt := div_nonneg (hrange t).1 hden.le
  have hfloor : ⌊qs⌋₊ = ⌊qt⌋₊ := by
    simpa [certificateSlackBin, qs, qt] using congrArg Fin.val hbin
  have hslo : ((⌊qs⌋₊ : ℕ) : ℝ) ≤ qs := Nat.floor_le hqs0
  have hshi : qs < (⌊qs⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one qs
  have htlo : ((⌊qs⌋₊ : ℕ) : ℝ) ≤ qt := by
    rw [hfloor]
    exact Nat.floor_le hqt0
  have hthi : qt < (⌊qs⌋₊ : ℕ) + 1 := by
    rw [hfloor]
    exact Nat.lt_floor_add_one qt
  have hslo' : ((⌊qs⌋₊ : ℕ) : ℝ) * ((264 : ℝ) / 7) ≤
      coord s - base := (le_div_iff₀ hden).mp hslo
  have hshi' : coord s - base <
      (((⌊qs⌋₊ : ℕ) : ℝ) + 1) * ((264 : ℝ) / 7) :=
    (div_lt_iff₀ hden).mp hshi
  have htlo' : ((⌊qs⌋₊ : ℕ) : ℝ) * ((264 : ℝ) / 7) ≤
      coord t - base := (le_div_iff₀ hden).mp htlo
  have hthi' : coord t - base <
      (((⌊qs⌋₊ : ℕ) : ℝ) + 1) * ((264 : ℝ) / 7) :=
    (div_lt_iff₀ hden).mp hthi
  rw [abs_lt]
  constructor <;> nlinarith

variable (Z : ZeroConfig) (T C : ℝ) (P : Params)

noncomputable def coreCertificateSlackBin
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (z : CoreSimpleLabel Z T C) :
    Fin (certificateSlackBinCount (coreBinD T P)) :=
  certificateSlackBin (coreBinD T P) (coreBinBase T C P)
    (coreScaledOrdinate Z T C P) (coreScaledOrdinate_range Z T C P hL hC) z

noncomputable def coreCertificateSlackEnumeration
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    BinnedEnumeration (CoreSimpleLabel Z T C)
      (Fin (certificateSlackBinCount (coreBinD T P))) :=
  fiberBinnedEnumeration (coreCertificateSlackBin Z T C P hL hC)

theorem coreCertificateSlackEnumeration_cover
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    ∑ b, (coreCertificateSlackEnumeration Z T C P hL hC).occupancy b =
      Fintype.card (CoreSimpleLabel Z T C) := by
  exact fiberBinnedEnumeration_cover
    (coreCertificateSlackBin Z T C P hL hC)

theorem coreCertificateSlackBin_card_le
    (hL : 0 < P.L T) (hT : 0 ≤ T) :
    (Fintype.card
      (Fin (certificateSlackBinCount (coreBinD T P))) : ℝ) ≤
      (7 * Real.pi / 132) * coreBinD T P + 1 := by
  apply certificateSlackBin_card_le
  unfold coreBinD
  positivity

@[simp] theorem coreCertificateSlackPackedFourIndex_bin
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (q : PackedFour
      (coreCertificateSlackEnumeration Z T C P hL hC)) (k : Fin 4) :
    coreCertificateSlackBin Z T C P hL hC
      (packedFourIndex
        (coreCertificateSlackEnumeration Z T C P hL hC) q k) = q.1 := by
  exact fiberBinnedEnumeration_at_bin
    (coreCertificateSlackBin Z T C P hL hC) q.1 _

theorem coreCertificateSlackPackedFour_pair_distance_lt
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (q : PackedFour
      (coreCertificateSlackEnumeration Z T C P hL hC))
    (r t : Fin 4) :
    |coreScaledOrdinate Z T C P
        (packedFourIndex
          (coreCertificateSlackEnumeration Z T C P hL hC) q r) -
      coreScaledOrdinate Z T C P
        (packedFourIndex
          (coreCertificateSlackEnumeration Z T C P hL hC) q t)| <
      (264 : ℝ) / 7 := by
  apply abs_coord_sub_lt_certificateDiameter_of_bin_eq
    (coreScaledOrdinate_range Z T C P hL hC)
  change coreCertificateSlackBin Z T C P hL hC
        (packedFourIndex
          (coreCertificateSlackEnumeration Z T C P hL hC) q r) =
      coreCertificateSlackBin Z T C P hL hC
        (packedFourIndex
          (coreCertificateSlackEnumeration Z T C P hL hC) q t)
  rw [coreCertificateSlackPackedFourIndex_bin,
    coreCertificateSlackPackedFourIndex_bin]

end StrictImprovement
end Zeta23

end
