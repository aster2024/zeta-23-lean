/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WideRepairCoreBlocks
import Zeta23.StrictImprovement.ZetaBoundaryLoss
import Zeta23.ZeroSide.Mult
import Zeta23.ThmD.ParamsD

/-!
# Fixed-height zero-side defect with mixed three--four--five blocks
-/

noncomputable section

open Matrix Finset Real RHLinalg
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide ZeroSide.RankTraceMult

def wideRepairAtDCoreGain
    (Z : ZeroConfig) (T : ℝ) (P : Params) (scale : ℝ) : ℝ :=
  scale ^ 2 * wideRepairAlpha ^ 2 /
      (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) *
    max 0 ((Fintype.card (CoreSimpleLabel Z T 3) : ℝ) -
      wideRepairPackingLoss * coreBinD T (P.atD T) -
      wideRepairPackingIntercept) ^ 2

/-- Fixed-height `c=2` zero-side inequality with the mixed repaired gain. -/
theorem hatAz_mult2_with_wide_repair_gain
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P) (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) (hL : 0 < P.L T) (hT : 0 ≤ T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 P hconj z)
    [Nonempty (CoreSimpleLabel Z T 3)]
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hlocal : ∀ q : WideRepairBlock
      (coreWideRepairEnumeration Z T 3 P hL (by norm_num)),
      2 * (scale * wideRepairBlockReward q) ≤ Tail.traceNorm
        ((gramDeviation_isHermitian
          (normalizedCoreVec Z T 3 P hconj)).submatrix
            (wideRepairBlockIndex
              (coreWideRepairEnumeration Z T 3 P hL (by norm_num)) q))) :
    4 * rtrace (P.hat T (Z.Az P T)) -
        frobSq (P.hat T (Z.Az P T)) - 2 * (Z.NIprime T : ℝ) +
        scale ^ 2 * wideRepairAlpha ^ 2 /
          (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) *
          max 0 ((Fintype.card (CoreSimpleLabel Z T 3) : ℝ) -
            wideRepairPackingLoss * coreBinD T P -
            wideRepairPackingIntercept) ^ 2
      ≤ (Z.s1 T : ℝ) + excludedSimpleCount Z T 3 := by
  let D := blockData Z T P hconj
  let E := coreWideRepairEnumeration Z T 3 P hL (by norm_num)
  let x := normalizedCoreVec Z T 3 P hconj
  let wgt := finiteCoreWeight Z T 3 P hconj
  let A : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
    ((((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • D.blockA)
  have hA : A.IsHermitian := by
    dsimp [A]
    exact ZeroSide.ZeroBlockData.isHermitian_real_smul D.blockA_isHermitian _
  have hcover : ∑ b, E.occupancy b =
      Fintype.card (CoreSimpleLabel Z T 3) := by
    dsimp [E]
    exact coreWideRepairEnumeration_cover Z T 3 P hL (by norm_num)
  have hbins := coreWideRepairBin_card_le T P hL hT
  have hunit : ∀ z, ∑ k, ‖x z k‖ ^ 2 = 1 := by
    intro z
    dsimp [x]
    exact normalizedCoreVec_isUnit Z T 3 P hconj hpos z
  have hw0 : ∀ z, 0 ≤ wgt z := by
    intro z
    exact finiteCoreWeight_nonneg Z T 3 P hconj z
  have hw1 : ∀ z, wgt z ≤ 1 := by
    intro z
    dsimp [wgt]
    exact finiteCoreWeight_le_one Z T 3 P hconj hreal hPois hc z
  have hb := posIndex_scaledBlockA_sub_weightedCore_le
    Z T 3 P hconj hc hpos
  have hmain := rank_trace_two_with_normalized_mixed_blocks
    E hcover (coreBinD T P) hbins x hunit hscale hlocal
    wgt hw0 hw1 hA hb
  have htr : rtrace (projectorSum x) =
      Fintype.card (CoreSimpleLabel Z T 3) :=
    rtrace_projectorSum_of_unit x hunit
  have hAeq : A = P.hat T (Z.Az P T) := by
    dsimp [A, D]
    rw [← ZeroSide.Az_eq_blockA Z T P hconj]
    exact (ZeroSide.hat_eq T P (Z.Az P T)).symm
  have hsplit := coreCard_add_excluded_eq_s1 Z T 3 P hconj
  have hcountZ : Z.s1 T + 2 * Z.s2 T + 2 * Z.p T ≤ Z.NIprime T :=
    ZeroSide.s1_add_two_s2_add_two_p_le_NIprime Z T
  have hcountNat :
      3 * Fintype.card (CoreSimpleLabel Z T 3) +
          4 * (excludedSimpleCount Z T 3 + Z.s2 T + Z.p T) ≤
        2 * Z.NIprime T + Z.s1 T + excludedSimpleCount Z T 3 := by
    omega
  have hcountReal :
      3 * (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) +
          4 * ((excludedSimpleCount Z T 3 + Z.s2 T + Z.p T : ℕ) : ℝ) ≤
        2 * (Z.NIprime T : ℝ) + (Z.s1 T : ℝ) +
          excludedSimpleCount Z T 3 := by
    exact_mod_cast hcountNat
  rw [rtrace_sub, htr, hAeq] at hmain
  linarith

end StrictImprovement
end Zeta23

end
