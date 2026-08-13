/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WideRepairZetaAtD
import Zeta23.StrictImprovement.WideRepairZetaSeamDefect

/-! # Concrete fixed-height seam for mixed repaired packing -/

noncomputable section

open Matrix Finset Real RHLinalg
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide

theorem seamA_mult2_atD_with_wide_repair_gain
    (hcertificates : WideRepairEndpointCertificates)
    (Z : ZeroConfig) {T : ℝ} {P : Params} (hP : P.Valid)
    (hconj : PhiHatConj T (P.atD T))
    (hreal : PhiHatReal T (P.atD T))
    (hPois : PoissonSq T (P.atD T))
    (hF : PrimeSide.LocalHypsCoreW (ThmD.cDT P.ϱ P.lam)
      ((P.atD T).toSetting T) ((P.atD T).localFun T))
    {theta0 : ℝ} (hTl : Assembly.TailInputs Z (P.atD T) T theta0)
    (hT : 0 < T)
    (hc : 0 < (P.atD T).a T * (P.atD T).L T ^ 2)
    (hbudget :
      coreTailBudget (ThmD.cDT P.ϱ P.lam) ((P.atD T).toSetting T) 3 <
        (P.atD T).a T * (P.atD T).L T ^ 2)
    (hwL : 16 * P.w ≤ P.L T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 (P.atD T) hconj z)
    [Nonempty (CoreSimpleLabel Z T 3)]
    {scale : ℝ} (hscale : 0 ≤ scale)
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
      wideRepairRewardFive) :
    4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
        frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
        2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ) -
        theta0 / ((P.atD T).a T * (P.atD T).L T) *
          (4 + 2 * Real.sqrt
              (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
            theta0 / ((P.atD T).a T * (P.atD T).L T)) +
        wideRepairAtDCoreGain Z T P scale
      ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3 := by
  have hLD : 0 < (P.atD T).L T := by
    simpa using (show 0 < P.L T by linarith [hP.one_le_w])
  have haD : 0 < (P.atD T).a T := by
    have hs : 0 ≤ (P.atD T).L T ^ 2 := sq_nonneg _
    nlinarith
  apply seamA_mult2_with_wide_repair_gain Z T (P.atD T)
    hconj hreal hPois hTl haD hLD hT.le hpos hscale
  intro q
  exact packedCoreWideRepairBlock_atD_traceNorm_lower
    hcertificates Z hP hconj hreal hF hT hc hbudget hwL hpos
      hmargin3 hmargin4 hmargin5 q

end StrictImprovement
end Zeta23

end
