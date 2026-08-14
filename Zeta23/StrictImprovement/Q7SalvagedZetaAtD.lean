/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7SalvagedCoreBlocks
import Zeta23.StrictImprovement.ZetaAtDCorrelation

/-! # Salvaged q7 superbin local blocks at a fixed taper -/

noncomputable section

open Filter Topology Real
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

theorem packedCoreQ7SalvagedBlock_atD_traceNorm_lower
    (hcertificates : Q7SalvagedEndpointCertificates)
    (Z : ZeroConfig) {T : ℝ} {P : Params} (hP : P.Valid)
    (hconj : PhiHatConj T (P.atD T))
    (hreal : PhiHatReal T (P.atD T))
    (hF : PrimeSide.LocalHypsCoreW (ThmD.cDT P.ϱ P.lam)
      ((P.atD T).toSetting T) ((P.atD T).localFun T))
    (hT : 0 < T)
    (hc : 0 < (P.atD T).a T * (P.atD T).L T ^ 2)
    (hbudget :
      coreTailBudget (ThmD.cDT P.ϱ P.lam) ((P.atD T).toSetting T) 3 <
        (P.atD T).a T * (P.atD T).L T ^ 2)
    (hwL : 16 * P.w ≤ P.L T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 (P.atD T) hconj z)
    {scale : ℝ}
    (hmargin3 : scale * wideRepairRewardThree +
        (3 * Real.sqrt 3 / 2) *
          localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
            (12 * P.w / P.L T + 3 * (1 - P.lam)) ≤
      wideRepairRewardThree)
    (hmargin4 : scale * wideRepairRewardFour +
        2 * Real.sqrt 3 *
          localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
            (12 * P.w / P.L T + 3 * (1 - P.lam)) ≤
      wideRepairRewardFour)
    (hmargin5 : scale * wideRepairRewardFive +
        (5 * Real.sqrt 5 / 2) *
          localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
            (12 * P.w / P.L T + 3 * (1 - P.lam)) ≤
      wideRepairRewardFive)
    (hmargin6 : scale * q7SalvagedSixReward +
        3 * Real.sqrt 6 *
          localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
            (12 * P.w / P.L T + 3 * (1 - P.lam)) ≤
      q7SalvagedSixReward)
    (hmargin7 : scale * q7SalvagedSevenReward +
        (7 * Real.sqrt 7 / 2) *
          localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
            (12 * P.w / P.L T + 3 * (1 - P.lam)) ≤
      q7SalvagedSevenReward)
    (q : Q7SalvagedBlock
      (coreQ6HalfBinEnumeration Z T 3 (P.atD T)
        (by simpa using (show 0 < P.L T by linarith [hP.one_le_w]))
        (by norm_num))) :
    2 * (scale * q7SalvagedBlockReward q) ≤ Tail.traceNorm
      ((gramDeviation_isHermitian
        (normalizedCoreVec Z T 3 (P.atD T) hconj)).submatrix
          (q7SalvagedBlockIndex
            (coreQ6HalfBinEnumeration Z T 3 (P.atD T)
              (by simpa using
                (show 0 < P.L T by linarith [hP.one_le_w]))
              (by norm_num)) q)) := by
  have hL : 0 < (P.atD T).L T := by
    simpa using (show 0 < P.L T by linarith [hP.one_le_w])
  have heps : 0 ≤ 12 * P.w / P.L T + 3 * (1 - P.lam) := by
    have hL' : 0 < P.L T := by linarith [hP.one_le_w]
    have hw0 : 0 ≤ P.w := by linarith [hP.one_le_w]
    have hlam0 : 0 ≤ 1 - P.lam := sub_nonneg.mpr hP.lam_le_one
    have hfinite0 : 0 ≤ 12 * P.w / P.L T :=
      div_nonneg (mul_nonneg (by norm_num) hw0) hL'.le
    nlinarith
  apply packedCoreQ7SalvagedBlock_traceNorm_lower
    Z T (P.atD T) hcertificates (ThmD.cDT P.ϱ P.lam) hconj
    hreal hF hT hc hbudget hL hpos heps
  · intro z z'
    simpa only [Params.atD_L, coreScaledOrdinate] using
      (fullCoreCorrelation_atD_close_endpointR Z hP hwL z z')
  · exact hmargin3
  · exact hmargin4
  · exact hmargin5
  · exact hmargin6
  · exact hmargin7

end StrictImprovement
end Zeta23

end
