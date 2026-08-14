/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7FullSpectralBlocks
import Zeta23.StrictImprovement.Q7FullSpectralMixedPacking

/-!
# Concrete full-spectral q7 superbin packing interface

This module instantiates the abstract dependent-block pinching theorem with
the concrete nine-kind block inventory.  The only remaining analytic input
is the local trace-norm lower bound for each selected block.
-/

noncomputable section

open Matrix Finset Real
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

theorem q7FullSpectralBlocks_traceNorm_target_lower
    {S B d : Type*} [Fintype S] [DecidableEq S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S (B × Fin 2))
    (hcover : ∑ b, (q7FullSpectralLeftOccupancy E b +
      q7FullSpectralRightOccupancy E b) = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 16 + 1)
    (x : S → d → ℂ) {scale : ℝ} (hscale : 0 ≤ scale)
    (hlocal : ∀ q : Q7FullSpectralBlock E,
      2 * (scale * q7FullSpectralBlockReward q) ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix
          (q7FullSpectralBlockIndex E q))) :
    2 * (scale * wideRepairAlpha * max 0
        ((Fintype.card S : ℝ) - q7FullSpectralPackingLoss * D -
          q7FullSpectralPackingIntercept)) ≤
      Tail.traceNorm (gramDeviation_isHermitian x) := by
  apply q7FullSpectral_selected_blocks_traceNorm_target_lower
    (q7FullSpectralLeftOccupancy E) (q7FullSpectralRightOccupancy E)
    hcover D hbins q7FullSpectralBlockSize (q7FullSpectralBlockIndex E)
    (q7FullSpectralBlockIndex_injective E) q7FullSpectralBlockReward
    (sum_q7FullSpectralBlockReward_eq E) x hscale hlocal

theorem rank_trace_two_with_q7FullSpectralBlocks
    {S B d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S (B × Fin 2))
    (hcover : ∑ b, (q7FullSpectralLeftOccupancy E b +
      q7FullSpectralRightOccupancy E b) = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 16 + 1)
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hlocal : ∀ q : Q7FullSpectralBlock E,
      2 * (scale * q7FullSpectralBlockReward q) ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix
          (q7FullSpectralBlockIndex E q)))
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (columnMatrix x * (columnMatrix x)ᴴ) -
        (Fintype.card S : ℝ) + 4 * rtrace Q - 4 * (b : ℝ) +
        scale ^ 2 * wideRepairAlpha ^ 2 / (Fintype.card S : ℝ) *
          max 0 ((Fintype.card S : ℝ) -
            q7FullSpectralPackingLoss * D -
            q7FullSpectralPackingIntercept) ^ 2 ≤
      frobSq (columnMatrix x * (columnMatrix x)ᴴ + Q) := by
  exact rank_trace_two_with_q7FullSpectral_selected_blocks
    (q7FullSpectralLeftOccupancy E) (q7FullSpectralRightOccupancy E)
    hcover D hbins q7FullSpectralBlockSize (q7FullSpectralBlockIndex E)
    (q7FullSpectralBlockIndex_injective E) q7FullSpectralBlockReward
    (sum_q7FullSpectralBlockReward_eq E) x hunit hscale hlocal hQ hb

end StrictImprovement
end Zeta23

end
