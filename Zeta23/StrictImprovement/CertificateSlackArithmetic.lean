/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Zeta23.StrictImprovement.SpectralFourPointInterface

/-!
# Exact arithmetic for the certificate-domain slack

The external interval tree covers diameter `264/7`, slightly larger than
`12*pi`.  This file records the exact endpoint margin and public unit-fraction
weakening obtained from Mathlib's strict twenty-decimal upper bound on `pi`.
-/

noncomputable section

namespace Zeta23
namespace StrictImprovement

/-- Rational lower bound for the endpoint packing margin after using the full
`264/7` certificate domain. -/
def certificateSlackMarginLower : ℝ :=
  (102239 : ℝ) / 592688 +
    (22 - 7 * (314159265358979323847 : ℝ) / 100000000000000000000) / 44

theorem pi_lt_certificateSlackUpper :
    Real.pi <
      (314159265358979323847 : ℝ) / 100000000000000000000 := by
  exact Real.pi_lt_d20.trans_eq (by norm_num)

theorem certificateSlackMarginLower_lt_endpointMargin :
    certificateSlackMarginLower <
      ThmD.HD 1 - 7 * Real.pi / 44 := by
  have hgap :
      (102239 : ℝ) / 592688 ≤ ThmD.HD 1 - 1 / 2 :=
    refined_endpoint_gap
  have hpi := pi_lt_certificateSlackUpper
  unfold certificateSlackMarginLower
  nlinarith

theorem certificateSlack_public_lt_exact_gain :
    (1 : ℝ) / 911960 <
      spectralFourMassLower / 16 * certificateSlackMarginLower ^ 2 := by
  norm_num [spectralFourMassLower, certificateSlackMarginLower]

theorem certificateSlack_next_unit_not_below_exact_gain :
    spectralFourMassLower / 16 * certificateSlackMarginLower ^ 2 <
      (1 : ℝ) / 911959 := by
  norm_num [spectralFourMassLower, certificateSlackMarginLower]

end StrictImprovement
end Zeta23

end
