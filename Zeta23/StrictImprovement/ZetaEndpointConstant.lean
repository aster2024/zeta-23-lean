/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.EndpointTaylorRefinement

/-!
# Exact endpoint gap in the Theorem-D constant

The root-localization package proves `6/5 < endpointKappa`.  The final gain
also needs the exact bridge

`HD 1 = 3/2 - endpointKappa^(-1)`.

Together they imply the strict rational margin

`1/6 < HD 1 - 1/2`.

This file contains no approximation or floating-point literal.
-/

noncomputable section

open Real

namespace Zeta23
namespace StrictImprovement

/-- The endpoint Theorem-D constant written in terms of the same root
parameter used by the explicit three-point certificate. -/
theorem HD_one_eq_three_halves_sub_inv_endpointKappa :
    ThmD.HD 1 = 3 / 2 - endpointKappa⁻¹ := by
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  have hsin : 0 < Real.sin (ThmD.theta 1) :=
    ThmD.sin_theta_pos (lam := (1 : ℝ)) (by norm_num) (by norm_num)
  have hcos : 0 < Real.cos (ThmD.theta 1) :=
    ThmD.cos_theta_pos (lam := (1 : ℝ)) (by norm_num) (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have htheta : Real.sqrt 2 * ThmD.theta 1 = 1 :=
    sqrtTwo_mul_endpointTheta
  unfold ThmD.HD ThmD.cStar endpointKappa
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hsqrt.ne', hsin.ne', hcos.ne']
  nlinarith

/-- Exact strict rational gap consumed by the endpoint eta ledger. -/
theorem one_sixth_lt_HD_one_sub_half :
    (1 : ℝ) / 6 < ThmD.HD 1 - 1 / 2 := by
  have hinv : endpointKappa⁻¹ < (5 : ℝ) / 6 := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ endpointKappa_pos).2
    nlinarith [six_fifths_lt_endpointKappa]
  rw [HD_one_eq_three_halves_sub_inv_endpointKappa]
  linarith

/-- Non-strict form used when multiplying nonnegative endpoint factors. -/
theorem one_sixth_le_HD_one_sub_half :
    (1 : ℝ) / 6 ≤ ThmD.HD 1 - 1 / 2 :=
  one_sixth_lt_HD_one_sub_half.le

/-- The exact rational endpoint gain follows from the certified local defect
and the strict endpoint density gap. -/
theorem explicitEtaLower_le_endpoint_gain :
    explicitEtaLower ≤
      explicitDeltaLower / 9 * (ThmD.HD 1 - 1 / 2) ^ 2 := by
  have hgap0 : 0 ≤ (1 : ℝ) / 6 := by norm_num
  have hsq := pow_le_pow_left₀ hgap0 one_sixth_le_HD_one_sub_half 2
  have hcoef : 0 ≤ explicitDeltaLower / 9 := by
    norm_num [explicitDeltaLower]
  rw [← delta_gap_eq_eta]
  exact mul_le_mul_of_nonneg_left hsq hcoef

/-- Improved public rational gain obtained by retaining the unrounded
`88/73` endpoint-root lower bound. -/
def explicitEtaImproved : ℝ := 1 / 239333277

/-- The unrounded endpoint-root estimate improves the density gap from
`1/6` to `15/88`. -/
theorem fifteen_over_eighty_eight_lt_HD_one_sub_half :
    (15 : ℝ) / 88 < ThmD.HD 1 - 1 / 2 := by
  have hinv : endpointKappa⁻¹ < (73 : ℝ) / 88 := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ endpointKappa_pos).2
    nlinarith [eighty_eight_over_seventy_three_lt_endpointKappa]
  rw [HD_one_eq_three_halves_sub_inv_endpointKappa]
  linarith

/-- Exact comparison between the improved public rational and the endpoint
quadratic gain.  The comparison has positive rational slack. -/
theorem explicitEtaImproved_le_endpoint_gain :
    explicitEtaImproved ≤
      explicitDeltaLower / 9 * (ThmD.HD 1 - 1 / 2) ^ 2 := by
  have hgap0 : 0 ≤ (15 : ℝ) / 88 := by norm_num
  have hsq := pow_le_pow_left₀ hgap0
    fifteen_over_eighty_eight_lt_HD_one_sub_half.le 2
  have hcoef : 0 ≤ explicitDeltaLower / 9 := by
    norm_num [explicitDeltaLower]
  calc
    explicitEtaImproved
        ≤ explicitDeltaLower / 9 * ((15 : ℝ) / 88) ^ 2 := by
            norm_num [explicitEtaImproved, explicitDeltaLower]
    _ ≤ explicitDeltaLower / 9 * (ThmD.HD 1 - 1 / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef

/-- Final Taylor- and threshold-refined public rational gain. -/
def explicitEtaTaylor : ℝ := 1 / 233423794

/-- The seventh/eighth-order endpoint estimate gives the sharper exact gap. -/
theorem refined_endpoint_gap :
    (102239 : ℝ) / 592688 ≤ ThmD.HD 1 - 1 / 2 := by
  have hinv : endpointKappa⁻¹ ≤ (490449 : ℝ) / 592688 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ endpointKappa_pos).2
    nlinarith [endpointKappa_refined_lower]
  rw [HD_one_eq_three_halves_sub_inv_endpointKappa]
  linarith

/-- The exact integer ceiling comparison for the Taylor-refined gain. -/
theorem explicitEtaTaylor_le_endpoint_gain :
    explicitEtaTaylor ≤
      explicitDeltaLower / 9 * (ThmD.HD 1 - 1 / 2) ^ 2 := by
  have hgap0 : 0 ≤ (102239 : ℝ) / 592688 := by norm_num
  have hsq := pow_le_pow_left₀ hgap0 refined_endpoint_gap 2
  have hcoef : 0 ≤ explicitDeltaLower / 9 := by
    norm_num [explicitDeltaLower]
  calc
    explicitEtaTaylor
        ≤ explicitDeltaLower / 9 * ((102239 : ℝ) / 592688) ^ 2 := by
            norm_num [explicitEtaTaylor, explicitDeltaLower]
    _ ≤ explicitDeltaLower / 9 * (ThmD.HD 1 - 1 / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef

end StrictImprovement
end Zeta23

end
