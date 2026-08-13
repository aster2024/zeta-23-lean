/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaEndpointPassage
import Zeta23.StrictImprovement.WideRepairZetaStrictConcrete

/-!
# Endpoint passage for the mixed repaired packing

The auxiliary taper is fixed before height tends to infinity.  A common
endpoint scale leaves strict room for the three-, four-, and five-point
stability losses.  The external interval certificates remain explicit
hypotheses of the public theorem.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

/-- One common reserve coefficient for all three local block sizes. -/
def wideRepairEndpointReserve : ℝ :=
  1800 * Real.sqrt 3 + 240 * Real.sqrt 5 + 1

/-- The finite fixed-window scale; it tends to one at the endpoint. -/
def wideRepairEndpointScale (n : ℕ) : ℝ :=
  1 - wideRepairEndpointReserve * endpointStep n

/-- The mixed packing's positive part before truncation. -/
def wideRepairEndpointQ (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) - endpointEps n -
    (13 : ℝ) / 40 * (endpointLam n + endpointEps n) - endpointEps n

/-- Fixed-window coefficient delivered at the `n`-th taper. -/
def wideRepairEndpointRate (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) +
    wideRepairEndpointScale n ^ 2 * wideRepairEndpointQ n ^ 2 /
      (25600 * (1 + endpointEps n))

/-- Endpoint coefficient before its public unit-fraction weakening. -/
def wideRepairEndpointRateLimit : ℝ :=
  ThmD.HD 1 + (ThmD.HD 1 - (13 : ℝ) / 40) ^ 2 / 25600

theorem tendsto_wideRepairEndpointScale :
    Tendsto wideRepairEndpointScale atTop (nhds 1) := by
  have h := tendsto_const_nhds.sub
    (tendsto_endpointStep_zero.const_mul wideRepairEndpointReserve)
  change Tendsto
    (fun n : ℕ => 1 - wideRepairEndpointReserve * endpointStep n)
      atTop (nhds 1)
  simpa only [mul_zero, sub_zero] using h

theorem tendsto_wideRepairEndpointQ :
    Tendsto wideRepairEndpointQ atTop
      (nhds (ThmD.HD 1 - (13 : ℝ) / 40)) := by
  have hsum := tendsto_endpointLam_one.add tendsto_endpointStep_zero
  have hscaled := hsum.const_mul ((13 : ℝ) / 40)
  have h := ((tendsto_endpointHD.sub tendsto_endpointStep_zero).sub
    hscaled).sub tendsto_endpointStep_zero
  change Tendsto
    (fun n : ℕ => ThmD.HD (endpointLam n) - endpointEps n -
      (13 : ℝ) / 40 * (endpointLam n + endpointEps n) -
      endpointEps n) atTop _
  simpa only [endpointEps, add_zero, mul_one, sub_zero] using h

theorem tendsto_wideRepairEndpointRate :
    Tendsto wideRepairEndpointRate atTop
      (nhds wideRepairEndpointRateLimit) := by
  have hnum := (tendsto_wideRepairEndpointScale.pow 2).mul
    (tendsto_wideRepairEndpointQ.pow 2)
  have hden : Tendsto
      (fun n : ℕ => (25600 : ℝ) * (1 + endpointStep n)) atTop
      (nhds ((25600 : ℝ) * (1 + 0))) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.add tendsto_endpointStep_zero)
  have hgain := hnum.div hden
    (by norm_num : (25600 : ℝ) * (1 + 0) ≠ 0)
  have h := tendsto_endpointHD.add hgain
  have hend :
      ThmD.HD 1 + 1 ^ 2 * (ThmD.HD 1 - (13 : ℝ) / 40) ^ 2 /
          (25600 * (1 + 0)) = wideRepairEndpointRateLimit := by
    unfold wideRepairEndpointRateLimit
    ring
  rw [← hend]
  change Tendsto
    (fun n : ℕ => ThmD.HD (endpointLam n) +
      wideRepairEndpointScale n ^ 2 * wideRepairEndpointQ n ^ 2 /
        (25600 * (1 + endpointStep n))) atTop _
  exact h

/-- All fixed-window hypotheses needed by the mixed endpoint passage. -/
def WideRepairEndpointFeasible (n : ℕ) : Prop :=
  0 < endpointLam n ∧ endpointLam n < 1 ∧
  0 < endpointEps n ∧
  0 < ThmD.HD (endpointLam n) - endpointEps n ∧
  0 ≤ wideRepairEndpointScale n ∧
  wideRepairEndpointScale n * wideRepairRewardThree +
      (9 * Real.sqrt 3 / 2) * (1 - endpointLam n) <
    wideRepairRewardThree ∧
  wideRepairEndpointScale n * wideRepairRewardFour +
      6 * Real.sqrt 3 * (1 - endpointLam n) <
    wideRepairRewardFour ∧
  wideRepairEndpointScale n * wideRepairRewardFive +
      (15 * Real.sqrt 5 / 2) * (1 - endpointLam n) <
    wideRepairRewardFive ∧
  0 ≤ wideRepairEndpointQ n

theorem eventually_wideRepairEndpointFeasible :
    ∀ᶠ n in atTop, WideRepairEndpointFeasible n := by
  have hlamPos : ∀ᶠ n in atTop, 0 < endpointLam n :=
    tendsto_endpointLam_one.eventually (Ioi_mem_nhds one_pos)
  have hscalePos : ∀ᶠ n in atTop, 0 < wideRepairEndpointScale n :=
    tendsto_wideRepairEndpointScale.eventually (Ioi_mem_nhds one_pos)
  have hHlim :
      Tendsto (fun n => ThmD.HD (endpointLam n) - endpointEps n)
        atTop (nhds (ThmD.HD 1)) := by
    simpa [endpointEps] using
      tendsto_endpointHD.sub tendsto_endpointStep_zero
  have hHone : 0 < ThmD.HD 1 := by
    linarith [one_sixth_lt_HD_one_sub_half]
  have hHpos :
      ∀ᶠ n in atTop, 0 < ThmD.HD (endpointLam n) - endpointEps n :=
    hHlim.eventually (Ioi_mem_nhds hHone)
  have hqLimit : 0 < ThmD.HD 1 - (13 : ℝ) / 40 := by
    linarith [refined_endpoint_gap]
  have hqPos : ∀ᶠ n in atTop, 0 < wideRepairEndpointQ n :=
    tendsto_wideRepairEndpointQ.eventually (Ioi_mem_nhds hqLimit)
  filter_upwards [hlamPos, hscalePos, hHpos, hqPos]
    with n hlam hscale hH hq
  have hstep := endpointStep_pos n
  have hlamStep : 1 - endpointLam n = endpointStep n := by
    unfold endpointLam
    ring
  have hsqrt3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt5 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hc3 : 0 < wideRepairEndpointReserve * wideRepairRewardThree -
      9 * Real.sqrt 3 / 2 := by
    unfold wideRepairEndpointReserve wideRepairRewardThree
    nlinarith
  have hc4 : 0 < wideRepairEndpointReserve * wideRepairRewardFour -
      6 * Real.sqrt 3 := by
    unfold wideRepairEndpointReserve wideRepairRewardFour
    nlinarith
  have hc5 : 0 < wideRepairEndpointReserve * wideRepairRewardFive -
      15 * Real.sqrt 5 / 2 := by
    unfold wideRepairEndpointReserve wideRepairRewardFive
    nlinarith
  have hm3 : wideRepairEndpointScale n * wideRepairRewardThree +
      (9 * Real.sqrt 3 / 2) * (1 - endpointLam n) <
      wideRepairRewardThree := by
    rw [hlamStep]
    unfold wideRepairEndpointScale
    nlinarith [mul_pos hstep hc3]
  have hm4 : wideRepairEndpointScale n * wideRepairRewardFour +
      6 * Real.sqrt 3 * (1 - endpointLam n) <
      wideRepairRewardFour := by
    rw [hlamStep]
    unfold wideRepairEndpointScale
    nlinarith [mul_pos hstep hc4]
  have hm5 : wideRepairEndpointScale n * wideRepairRewardFive +
      (15 * Real.sqrt 5 / 2) * (1 - endpointLam n) <
      wideRepairRewardFive := by
    rw [hlamStep]
    unfold wideRepairEndpointScale
    nlinarith [mul_pos hstep hc5]
  refine ⟨hlam, endpointLam_lt_one n, ?_, hH, hscale.le,
    hm3, hm4, hm5, hq.le⟩
  simpa [endpointEps] using hstep

/-- Conditional endpoint passage for any certified lower bound on the mixed
quadratic gain. -/
theorem zeta_wide_repair_strict_simple_endpoint_of_le_gain
    (hcertificates : WideRepairEndpointCertificates)
    {eta : ℝ}
    (heta : eta ≤ (ThmD.HD 1 - (13 : ℝ) / 40) ^ 2 / 25600) :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + eta - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  intro outer houter
  have hclose : ∀ᶠ n in atTop,
      wideRepairEndpointRateLimit - outer / 2 < wideRepairEndpointRate n :=
    tendsto_wideRepairEndpointRate.eventually
      (Ioi_mem_nhds (by linarith :
        wideRepairEndpointRateLimit - outer / 2 <
          wideRepairEndpointRateLimit))
  obtain ⟨n, hn, hrate⟩ :=
    (eventually_wideRepairEndpointFeasible.and hclose).exists
  rcases hn with
    ⟨hlam0, hlam1, heps, hH, hscale, hm3, hm4, hm5, hq⟩
  obtain ⟨T₀, hT₀⟩ := zeta_wide_repair_strict_simple_fixed_lam
    hcertificates hlam0 hlam1 heps hH hscale hm3 hm4 hm5
      (by simpa [wideRepairEndpointQ] using hq)
      (outer / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have hfixed :
      (wideRepairEndpointRate n - outer / 2) *
          (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
    simpa [wideRepairEndpointRate, wideRepairEndpointQ] using hT₀ T hT
  have hcoef :
      ThmD.HD 1 + eta - outer ≤
        wideRepairEndpointRate n - outer / 2 := by
    unfold wideRepairEndpointRateLimit at hrate
    linarith
  exact le_trans
    (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) hfixed

theorem wideRepair_endpoint_gap_lower :
    (1029797 : ℝ) / 2963440 ≤ ThmD.HD 1 - (13 : ℝ) / 40 := by
  linarith [refined_endpoint_gap]

theorem wideRepair_public_le_endpoint_gain :
    (1 : ℝ) / 211997 ≤
      (ThmD.HD 1 - (13 : ℝ) / 40) ^ 2 / 25600 := by
  have hgap0 : 0 ≤ (1029797 : ℝ) / 2963440 := by norm_num
  have hsq := pow_le_pow_left₀ hgap0 wideRepair_endpoint_gap_lower 2
  calc
    (1 : ℝ) / 211997 ≤
        ((1029797 : ℝ) / 2963440) ^ 2 / 25600 := by norm_num
    _ ≤ (ThmD.HD 1 - (13 : ℝ) / 40) ^ 2 / 25600 := by
      exact div_le_div_of_nonneg_right hsq (by norm_num)

/-- Public rational form, explicitly conditional on all three external
endpoint interval certificates. -/
theorem zeta_wide_repair_strict_simple_endpoint_rational
    (hcertificates : WideRepairEndpointCertificates) :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + (1 : ℝ) / 211997 - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  zeta_wide_repair_strict_simple_endpoint_of_le_gain
    hcertificates wideRepair_public_le_endpoint_gain

end StrictImprovement
end Zeta23

end
