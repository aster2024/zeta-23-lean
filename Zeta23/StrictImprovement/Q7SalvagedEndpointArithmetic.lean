/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7SalvagedResiduePacking
import Zeta23.StrictImprovement.ZetaEndpointPassage

/-!
# Endpoint arithmetic for the q6 superbin repair

This module is independent of the still-pending concrete finite selector.  It
checks the common stability scale, endpoint limits, exact amplitude, and the
public unit-fraction weakening `1/175919`.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

def q7SalvagedEndpointReserve : ℝ := 4096

def q7SalvagedEndpointScale (n : ℕ) : ℝ :=
  1 - q7SalvagedEndpointReserve * endpointStep n

def q7SalvagedEndpointQ (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) - endpointEps n -
    q7SalvagedPackingLoss * (endpointLam n + endpointEps n) - endpointEps n

def q7SalvagedEndpointRate (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) +
    q7SalvagedEndpointScale n ^ 2 * wideRepairAlpha ^ 2 *
      q7SalvagedEndpointQ n ^ 2 / (1 + endpointEps n)

def q7SalvagedEndpointRateLimit : ℝ :=
  ThmD.HD 1 + wideRepairAlpha ^ 2 *
    (ThmD.HD 1 - q7SalvagedPackingLoss) ^ 2

theorem tendsto_q7SalvagedEndpointScale :
    Tendsto q7SalvagedEndpointScale atTop (nhds 1) := by
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h := hconst.sub
    (tendsto_endpointStep_zero.const_mul q7SalvagedEndpointReserve)
  change Tendsto
    (fun n : ℕ => 1 - q7SalvagedEndpointReserve * endpointStep n)
      atTop (nhds 1)
  simpa only [mul_zero, sub_zero] using h

theorem tendsto_q7SalvagedEndpointQ :
    Tendsto q7SalvagedEndpointQ atTop
      (nhds (ThmD.HD 1 - q7SalvagedPackingLoss)) := by
  have hsum := tendsto_endpointLam_one.add tendsto_endpointStep_zero
  have hscaled := hsum.const_mul q7SalvagedPackingLoss
  have h := ((tendsto_endpointHD.sub tendsto_endpointStep_zero).sub
    hscaled).sub tendsto_endpointStep_zero
  change Tendsto
    (fun n : ℕ => ThmD.HD (endpointLam n) - endpointEps n -
      q7SalvagedPackingLoss * (endpointLam n + endpointEps n) -
      endpointEps n) atTop _
  simpa only [endpointEps, add_zero, mul_one, sub_zero] using h

theorem tendsto_q7SalvagedEndpointRate :
    Tendsto q7SalvagedEndpointRate atTop
      (nhds q7SalvagedEndpointRateLimit) := by
  have hnum := ((tendsto_q7SalvagedEndpointScale.pow 2).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => wideRepairAlpha ^ 2)
      atTop (nhds (wideRepairAlpha ^ 2)))).mul
    (tendsto_q7SalvagedEndpointQ.pow 2)
  have hden : Tendsto
      (fun n : ℕ => (1 : ℝ) + endpointStep n) atTop
      (nhds ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add tendsto_endpointStep_zero
  have hgain := hnum.div hden (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have h := tendsto_endpointHD.add hgain
  have hend :
      ThmD.HD 1 + 1 ^ 2 * wideRepairAlpha ^ 2 *
          (ThmD.HD 1 - q7SalvagedPackingLoss) ^ 2 / (1 + 0) =
        q7SalvagedEndpointRateLimit := by
    unfold q7SalvagedEndpointRateLimit
    ring
  rw [← hend]
  change Tendsto
    (fun n : ℕ => ThmD.HD (endpointLam n) +
      q7SalvagedEndpointScale n ^ 2 * wideRepairAlpha ^ 2 *
        q7SalvagedEndpointQ n ^ 2 / (1 + endpointStep n)) atTop _
  exact h

/-- Fixed-window hypotheses required by the q3/q4/q5/raised-q6/q7 route. -/
def Q7SalvagedEndpointFeasible (n : ℕ) : Prop :=
  0 < endpointLam n ∧ endpointLam n < 1 ∧
  0 < endpointEps n ∧
  0 < ThmD.HD (endpointLam n) - endpointEps n ∧
  0 ≤ q7SalvagedEndpointScale n ∧
  q7SalvagedEndpointScale n * wideRepairRewardThree +
      (9 * Real.sqrt 3 / 2) * (1 - endpointLam n) <
    wideRepairRewardThree ∧
  q7SalvagedEndpointScale n * wideRepairRewardFour +
      6 * Real.sqrt 3 * (1 - endpointLam n) <
    wideRepairRewardFour ∧
  q7SalvagedEndpointScale n * wideRepairRewardFive +
      (15 * Real.sqrt 5 / 2) * (1 - endpointLam n) <
    wideRepairRewardFive ∧
  q7SalvagedEndpointScale n * q7SalvagedSixReward +
      9 * Real.sqrt 6 * (1 - endpointLam n) <
    q7SalvagedSixReward ∧
  q7SalvagedEndpointScale n * q7SalvagedSevenReward +
      (21 * Real.sqrt 7 / 2) * (1 - endpointLam n) <
    q7SalvagedSevenReward ∧
  0 ≤ q7SalvagedEndpointQ n

theorem eventually_q7SalvagedEndpointFeasible :
    ∀ᶠ n in atTop, Q7SalvagedEndpointFeasible n := by
  have hlamPos : ∀ᶠ n in atTop, 0 < endpointLam n :=
    tendsto_endpointLam_one.eventually (Ioi_mem_nhds one_pos)
  have hscalePos : ∀ᶠ n in atTop, 0 < q7SalvagedEndpointScale n :=
    tendsto_q7SalvagedEndpointScale.eventually (Ioi_mem_nhds one_pos)
  have hHlim : Tendsto
      (fun n => ThmD.HD (endpointLam n) - endpointEps n)
        atTop (nhds (ThmD.HD 1)) := by
    simpa [endpointEps] using
      tendsto_endpointHD.sub tendsto_endpointStep_zero
  have hHone : 0 < ThmD.HD 1 := by
    linarith [one_sixth_lt_HD_one_sub_half]
  have hHpos :
      ∀ᶠ n in atTop, 0 < ThmD.HD (endpointLam n) - endpointEps n :=
    hHlim.eventually (Ioi_mem_nhds hHone)
  have hqLimit : 0 < ThmD.HD 1 - q7SalvagedPackingLoss := by
    have hloss : q7SalvagedPackingLoss < (1 : ℝ) / 2 := by
      rw [q7SalvagedPackingLoss_value]
      norm_num
    linarith [refined_endpoint_gap]
  have hqPos : ∀ᶠ n in atTop, 0 < q7SalvagedEndpointQ n :=
    tendsto_q7SalvagedEndpointQ.eventually (Ioi_mem_nhds hqLimit)
  filter_upwards [hlamPos, hscalePos, hHpos, hqPos]
    with n hlam hscale hH hq
  have hstep := endpointStep_pos n
  have hlamStep : 1 - endpointLam n = endpointStep n := by
    unfold endpointLam
    ring
  have hsqrt3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt5 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrt6 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hsqrt7 : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  have hsqrt3sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt5sq : (Real.sqrt 5) ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt6sq : (Real.sqrt 6) ^ 2 = 6 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt7sq : (Real.sqrt 7) ^ 2 = 7 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt3lt : Real.sqrt 3 < 2 := by nlinarith
  have hsqrt5lt : Real.sqrt 5 < 3 := by nlinarith
  have hsqrt6lt : Real.sqrt 6 < (5 : ℝ) / 2 := by nlinarith
  have hsqrt7lt : Real.sqrt 7 < 3 := by nlinarith
  have hc3 : 0 < q7SalvagedEndpointReserve * wideRepairRewardThree -
      9 * Real.sqrt 3 / 2 := by
    have hrat : 9 < q7SalvagedEndpointReserve * wideRepairRewardThree := by
      norm_num [q7SalvagedEndpointReserve, wideRepairRewardThree]
    nlinarith
  have hc4 : 0 < q7SalvagedEndpointReserve * wideRepairRewardFour -
      6 * Real.sqrt 3 := by
    have hrat : 12 < q7SalvagedEndpointReserve * wideRepairRewardFour := by
      norm_num [q7SalvagedEndpointReserve, wideRepairRewardFour]
    nlinarith
  have hc5 : 0 < q7SalvagedEndpointReserve * wideRepairRewardFive -
      15 * Real.sqrt 5 / 2 := by
    have hrat : (45 : ℝ) / 2 <
        q7SalvagedEndpointReserve * wideRepairRewardFive := by
      norm_num [q7SalvagedEndpointReserve, wideRepairRewardFive]
    nlinarith
  have hc6 : 0 < q7SalvagedEndpointReserve * q7SalvagedSixReward -
      9 * Real.sqrt 6 := by
    have hrat : (45 : ℝ) / 2 <
        q7SalvagedEndpointReserve * q7SalvagedSixReward := by
      norm_num [q7SalvagedEndpointReserve, q7SalvagedSixReward]
    nlinarith
  have hc7 : 0 < q7SalvagedEndpointReserve * q7SalvagedSevenReward -
      21 * Real.sqrt 7 / 2 := by
    have hrat : (63 : ℝ) / 2 <
        q7SalvagedEndpointReserve * q7SalvagedSevenReward := by
      norm_num [q7SalvagedEndpointReserve, q7SalvagedSevenReward]
    nlinarith
  have hm3 : q7SalvagedEndpointScale n * wideRepairRewardThree +
      (9 * Real.sqrt 3 / 2) * (1 - endpointLam n) <
      wideRepairRewardThree := by
    rw [hlamStep]
    unfold q7SalvagedEndpointScale
    nlinarith [mul_pos hstep hc3]
  have hm4 : q7SalvagedEndpointScale n * wideRepairRewardFour +
      6 * Real.sqrt 3 * (1 - endpointLam n) <
      wideRepairRewardFour := by
    rw [hlamStep]
    unfold q7SalvagedEndpointScale
    nlinarith [mul_pos hstep hc4]
  have hm5 : q7SalvagedEndpointScale n * wideRepairRewardFive +
      (15 * Real.sqrt 5 / 2) * (1 - endpointLam n) <
      wideRepairRewardFive := by
    rw [hlamStep]
    unfold q7SalvagedEndpointScale
    nlinarith [mul_pos hstep hc5]
  have hm6 : q7SalvagedEndpointScale n * q7SalvagedSixReward +
      9 * Real.sqrt 6 * (1 - endpointLam n) <
      q7SalvagedSixReward := by
    rw [hlamStep]
    unfold q7SalvagedEndpointScale
    nlinarith [mul_pos hstep hc6]
  have hm7 : q7SalvagedEndpointScale n * q7SalvagedSevenReward +
      (21 * Real.sqrt 7 / 2) * (1 - endpointLam n) <
      q7SalvagedSevenReward := by
    rw [hlamStep]
    unfold q7SalvagedEndpointScale
    nlinarith [mul_pos hstep hc7]
  refine ⟨hlam, endpointLam_lt_one n, ?_, hH, hscale.le,
    hm3, hm4, hm5, hm6, hm7, hq.le⟩
  simpa [endpointEps] using hstep

theorem q7Salvaged_saturated_amplitude_lower :
    (551988813 : ℝ) / 231518750000 ≤
      wideRepairAlpha * (ThmD.HD 1 - q7SalvagedPackingLoss) := by
  norm_num [q7SalvagedPackingLoss, q7SalvagedDeficit,
    q7SalvagedSixReward, wideRepairAlpha, wideRepairRewardFive]
  nlinarith [refined_endpoint_gap]

theorem q7Salvaged_public_le_endpoint_gain :
    (1 : ℝ) / 175919 ≤ wideRepairAlpha ^ 2 *
      (ThmD.HD 1 - q7SalvagedPackingLoss) ^ 2 := by
  have hamp0 : 0 ≤ (551988813 : ℝ) / 231518750000 := by norm_num
  have hsq := pow_le_pow_left₀ hamp0
    q7Salvaged_saturated_amplitude_lower 2
  calc
    (1 : ℝ) / 175919 ≤
        ((551988813 : ℝ) / 231518750000) ^ 2 := by norm_num
    _ ≤ (wideRepairAlpha *
        (ThmD.HD 1 - q7SalvagedPackingLoss)) ^ 2 := hsq
    _ = wideRepairAlpha ^ 2 *
        (ThmD.HD 1 - q7SalvagedPackingLoss) ^ 2 := by ring

/-- The neighboring unit fraction is too strong for this exact amplitude
lower bound, documenting the sharp public weakening of the frozen ledger. -/
lemma q7Salvaged_endpoint_amplitude_sq_lt_next_unit :
    ((551988813 : ℝ) / 231518750000) ^ 2 < (1 : ℝ) / 175918 := by
  norm_num

end StrictImprovement
end Zeta23

end
