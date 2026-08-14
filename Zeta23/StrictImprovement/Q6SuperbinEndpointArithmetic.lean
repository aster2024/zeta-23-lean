/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q6SuperbinResiduePacking
import Zeta23.StrictImprovement.ZetaEndpointPassage

/-!
# Endpoint arithmetic for the q6 superbin repair

This module is independent of the still-pending concrete finite selector.  It
checks the common stability scale, endpoint limits, exact amplitude, and the
public unit-fraction weakening `1/176171`.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

def q6SuperbinEndpointReserve : ℝ := 4096

def q6SuperbinEndpointScale (n : ℕ) : ℝ :=
  1 - q6SuperbinEndpointReserve * endpointStep n

def q6SuperbinEndpointQ (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) - endpointEps n -
    q6SuperbinPackingLoss * (endpointLam n + endpointEps n) - endpointEps n

def q6SuperbinEndpointRate (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) +
    q6SuperbinEndpointScale n ^ 2 * wideRepairAlpha ^ 2 *
      q6SuperbinEndpointQ n ^ 2 / (1 + endpointEps n)

def q6SuperbinEndpointRateLimit : ℝ :=
  ThmD.HD 1 + wideRepairAlpha ^ 2 *
    (ThmD.HD 1 - q6SuperbinPackingLoss) ^ 2

theorem tendsto_q6SuperbinEndpointScale :
    Tendsto q6SuperbinEndpointScale atTop (nhds 1) := by
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h := hconst.sub
    (tendsto_endpointStep_zero.const_mul q6SuperbinEndpointReserve)
  change Tendsto
    (fun n : ℕ => 1 - q6SuperbinEndpointReserve * endpointStep n)
      atTop (nhds 1)
  simpa only [mul_zero, sub_zero] using h

theorem tendsto_q6SuperbinEndpointQ :
    Tendsto q6SuperbinEndpointQ atTop
      (nhds (ThmD.HD 1 - q6SuperbinPackingLoss)) := by
  have hsum := tendsto_endpointLam_one.add tendsto_endpointStep_zero
  have hscaled := hsum.const_mul q6SuperbinPackingLoss
  have h := ((tendsto_endpointHD.sub tendsto_endpointStep_zero).sub
    hscaled).sub tendsto_endpointStep_zero
  change Tendsto
    (fun n : ℕ => ThmD.HD (endpointLam n) - endpointEps n -
      q6SuperbinPackingLoss * (endpointLam n + endpointEps n) -
      endpointEps n) atTop _
  simpa only [endpointEps, add_zero, mul_one, sub_zero] using h

theorem tendsto_q6SuperbinEndpointRate :
    Tendsto q6SuperbinEndpointRate atTop
      (nhds q6SuperbinEndpointRateLimit) := by
  have hnum := ((tendsto_q6SuperbinEndpointScale.pow 2).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => wideRepairAlpha ^ 2)
      atTop (nhds (wideRepairAlpha ^ 2)))).mul
    (tendsto_q6SuperbinEndpointQ.pow 2)
  have hden : Tendsto
      (fun n : ℕ => (1 : ℝ) + endpointStep n) atTop
      (nhds ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add tendsto_endpointStep_zero
  have hgain := hnum.div hden (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have h := tendsto_endpointHD.add hgain
  have hend :
      ThmD.HD 1 + 1 ^ 2 * wideRepairAlpha ^ 2 *
          (ThmD.HD 1 - q6SuperbinPackingLoss) ^ 2 / (1 + 0) =
        q6SuperbinEndpointRateLimit := by
    unfold q6SuperbinEndpointRateLimit
    ring
  rw [← hend]
  change Tendsto
    (fun n : ℕ => ThmD.HD (endpointLam n) +
      q6SuperbinEndpointScale n ^ 2 * wideRepairAlpha ^ 2 *
        q6SuperbinEndpointQ n ^ 2 / (1 + endpointStep n)) atTop _
  exact h

/-- Fixed-window hypotheses required by the q3/q4/q5/q6 superbin route. -/
def Q6SuperbinEndpointFeasible (n : ℕ) : Prop :=
  0 < endpointLam n ∧ endpointLam n < 1 ∧
  0 < endpointEps n ∧
  0 < ThmD.HD (endpointLam n) - endpointEps n ∧
  0 ≤ q6SuperbinEndpointScale n ∧
  q6SuperbinEndpointScale n * wideRepairRewardThree +
      (9 * Real.sqrt 3 / 2) * (1 - endpointLam n) <
    wideRepairRewardThree ∧
  q6SuperbinEndpointScale n * wideRepairRewardFour +
      6 * Real.sqrt 3 * (1 - endpointLam n) <
    wideRepairRewardFour ∧
  q6SuperbinEndpointScale n * wideRepairRewardFive +
      (15 * Real.sqrt 5 / 2) * (1 - endpointLam n) <
    wideRepairRewardFive ∧
  q6SuperbinEndpointScale n * q6SuperbinReward +
      9 * Real.sqrt 6 * (1 - endpointLam n) <
    q6SuperbinReward ∧
  0 ≤ q6SuperbinEndpointQ n

theorem eventually_q6SuperbinEndpointFeasible :
    ∀ᶠ n in atTop, Q6SuperbinEndpointFeasible n := by
  have hlamPos : ∀ᶠ n in atTop, 0 < endpointLam n :=
    tendsto_endpointLam_one.eventually (Ioi_mem_nhds one_pos)
  have hscalePos : ∀ᶠ n in atTop, 0 < q6SuperbinEndpointScale n :=
    tendsto_q6SuperbinEndpointScale.eventually (Ioi_mem_nhds one_pos)
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
  have hqLimit : 0 < ThmD.HD 1 - q6SuperbinPackingLoss := by
    have hloss : q6SuperbinPackingLoss < (1 : ℝ) / 2 := by
      rw [q6SuperbinPackingLoss_value]
      norm_num
    linarith [refined_endpoint_gap]
  have hqPos : ∀ᶠ n in atTop, 0 < q6SuperbinEndpointQ n :=
    tendsto_q6SuperbinEndpointQ.eventually (Ioi_mem_nhds hqLimit)
  filter_upwards [hlamPos, hscalePos, hHpos, hqPos]
    with n hlam hscale hH hq
  have hstep := endpointStep_pos n
  have hlamStep : 1 - endpointLam n = endpointStep n := by
    unfold endpointLam
    ring
  have hsqrt3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt5 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrt6 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hsqrt3sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt5sq : (Real.sqrt 5) ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt6sq : (Real.sqrt 6) ^ 2 = 6 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt3lt : Real.sqrt 3 < 2 := by nlinarith
  have hsqrt5lt : Real.sqrt 5 < 3 := by nlinarith
  have hsqrt6lt : Real.sqrt 6 < (5 : ℝ) / 2 := by nlinarith
  have hc3 : 0 < q6SuperbinEndpointReserve * wideRepairRewardThree -
      9 * Real.sqrt 3 / 2 := by
    have hrat : 9 < q6SuperbinEndpointReserve * wideRepairRewardThree := by
      norm_num [q6SuperbinEndpointReserve, wideRepairRewardThree]
    nlinarith
  have hc4 : 0 < q6SuperbinEndpointReserve * wideRepairRewardFour -
      6 * Real.sqrt 3 := by
    have hrat : 12 < q6SuperbinEndpointReserve * wideRepairRewardFour := by
      norm_num [q6SuperbinEndpointReserve, wideRepairRewardFour]
    nlinarith
  have hc5 : 0 < q6SuperbinEndpointReserve * wideRepairRewardFive -
      15 * Real.sqrt 5 / 2 := by
    have hrat : (45 : ℝ) / 2 <
        q6SuperbinEndpointReserve * wideRepairRewardFive := by
      norm_num [q6SuperbinEndpointReserve, wideRepairRewardFive]
    nlinarith
  have hc6 : 0 < q6SuperbinEndpointReserve * q6SuperbinReward -
      9 * Real.sqrt 6 := by
    have hrat : (45 : ℝ) / 2 <
        q6SuperbinEndpointReserve * q6SuperbinReward := by
      norm_num [q6SuperbinEndpointReserve, q6SuperbinReward]
    nlinarith
  have hm3 : q6SuperbinEndpointScale n * wideRepairRewardThree +
      (9 * Real.sqrt 3 / 2) * (1 - endpointLam n) <
      wideRepairRewardThree := by
    rw [hlamStep]
    unfold q6SuperbinEndpointScale
    nlinarith [mul_pos hstep hc3]
  have hm4 : q6SuperbinEndpointScale n * wideRepairRewardFour +
      6 * Real.sqrt 3 * (1 - endpointLam n) <
      wideRepairRewardFour := by
    rw [hlamStep]
    unfold q6SuperbinEndpointScale
    nlinarith [mul_pos hstep hc4]
  have hm5 : q6SuperbinEndpointScale n * wideRepairRewardFive +
      (15 * Real.sqrt 5 / 2) * (1 - endpointLam n) <
      wideRepairRewardFive := by
    rw [hlamStep]
    unfold q6SuperbinEndpointScale
    nlinarith [mul_pos hstep hc5]
  have hm6 : q6SuperbinEndpointScale n * q6SuperbinReward +
      9 * Real.sqrt 6 * (1 - endpointLam n) <
      q6SuperbinReward := by
    rw [hlamStep]
    unfold q6SuperbinEndpointScale
    nlinarith [mul_pos hstep hc6]
  refine ⟨hlam, endpointLam_lt_one n, ?_, hH, hscale.le,
    hm3, hm4, hm5, hm6, hq.le⟩
  simpa [endpointEps] using hstep

theorem q6Superbin_saturated_amplitude_lower :
    (2206375477 : ℝ) / 926075000000 ≤
      wideRepairAlpha * (ThmD.HD 1 - q6SuperbinPackingLoss) := by
  norm_num [q6SuperbinPackingLoss, q6SuperbinDeficit,
    wideRepairAlpha, wideRepairRewardFive, wideRepairRewardThree,
    wideRepairRewardFour]
  nlinarith [refined_endpoint_gap]

theorem q6Superbin_public_le_endpoint_gain :
    (1 : ℝ) / 176171 ≤ wideRepairAlpha ^ 2 *
      (ThmD.HD 1 - q6SuperbinPackingLoss) ^ 2 := by
  have hamp0 : 0 ≤ (2206375477 : ℝ) / 926075000000 := by norm_num
  have hsq := pow_le_pow_left₀ hamp0
    q6Superbin_saturated_amplitude_lower 2
  calc
    (1 : ℝ) / 176171 ≤
        ((2206375477 : ℝ) / 926075000000) ^ 2 := by norm_num
    _ ≤ (wideRepairAlpha *
        (ThmD.HD 1 - q6SuperbinPackingLoss)) ^ 2 := hsq
    _ = wideRepairAlpha ^ 2 *
        (ThmD.HD 1 - q6SuperbinPackingLoss) ^ 2 := by ring

/-- The neighboring unit fraction is too strong for this exact amplitude
lower bound, documenting the sharp public weakening of the frozen ledger. -/
lemma q6Superbin_endpoint_amplitude_sq_lt_next_unit :
    ((2206375477 : ℝ) / 926075000000) ^ 2 < (1 : ℝ) / 176170 := by
  norm_num

end StrictImprovement
end Zeta23

end
