/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WiderRootArithmetic
import Zeta23.StrictImprovement.ZetaEndpointConstant

/-!
# Optimized exact constants for the wider-window four-point route

The companion energy module certifies the exact minimum of the 216 frozen
weighted-Cauchy budgets, but the stricter localization gate is the active
bottleneck.  At block size four and width six, the general larger-block
coefficient is one eighth and the activation margin is exactly HD 1 - 1/2.
This file selects a local constant strictly below the localization supremum
and verifies the resulting best unit-fraction increment for the frozen
rational endpoint gap.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

namespace Zeta23
namespace StrictImprovement

def widerWeightedBudgetCeiling : ℝ :=
  9755468468368320337833317374859207102505001 /
    1623000197669009639771565694101668583197612441600

/-- The endpoint-optimized local energy constant.  It is chosen so that the
frozen rational endpoint product is exactly `1/79828975`, while remaining
strictly below the squared localization threshold. -/
def widerDeltaLower : ℝ :=
  2810232522752 / 834437357315980975

def widerEtaLower : ℝ := 1 / 79828975

theorem widerDeltaLower_le_weightedBudgetCeiling :
    widerDeltaLower ≤ widerWeightedBudgetCeiling := by
  norm_num [widerDeltaLower, widerWeightedBudgetCeiling]

theorem wider_delta_activates_localization :
    widerDeltaLower < widerCorrelationThreshold ^ 2 := by
  norm_num [widerDeltaLower, widerCorrelationThreshold]

/-- Exact endpoint arithmetic for the (q,d)=(4,6) candidate. -/
theorem widerEtaLower_le_endpoint_gain :
    widerEtaLower ≤
      widerDeltaLower / 8 * (ThmD.HD 1 - 1 / 2) ^ 2 := by
  have hgap0 : 0 ≤ (102239 : ℝ) / 592688 := by norm_num
  have hsq := pow_le_pow_left₀ hgap0 refined_endpoint_gap 2
  have hcoef : 0 ≤ widerDeltaLower / 8 := by
    norm_num [widerDeltaLower]
  calc
    widerEtaLower
        ≤ widerDeltaLower / 8 * ((102239 : ℝ) / 592688) ^ 2 := by
            norm_num [widerEtaLower, widerDeltaLower]
    _ ≤ widerDeltaLower / 8 * (ThmD.HD 1 - 1 / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef

theorem widerEtaLower_gt_current :
    (1 : ℝ) / 233423794 < widerEtaLower := by
  norm_num [widerEtaLower]

end StrictImprovement
end Zeta23

end
