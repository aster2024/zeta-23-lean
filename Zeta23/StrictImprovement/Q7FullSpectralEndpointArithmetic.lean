/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7FullSpectralResiduePacking
import Zeta23.StrictImprovement.Q6SuperbinEndpointArithmetic
import Zeta23.StrictImprovement.ZetaEndpointPassage

/-!
# Endpoint arithmetic for the q6 superbin repair

This module is independent of the still-pending concrete finite selector.  It
checks the common stability scale, endpoint limits, exact amplitude, and the
public unit-fraction weakening `1/170887`.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

def q7FullSpectralEndpointReserve : ℝ := 4096

def q7FullSpectralEndpointScale (n : ℕ) : ℝ :=
  1 - q7FullSpectralEndpointReserve * endpointStep n

def q7FullSpectralEndpointQ (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) - endpointEps n -
    q7FullSpectralPackingLoss * (endpointLam n + endpointEps n) - endpointEps n

def q7FullSpectralEndpointRate (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) +
    q7FullSpectralEndpointScale n ^ 2 * wideRepairAlpha ^ 2 *
      q7FullSpectralEndpointQ n ^ 2 / (1 + endpointEps n)

def q7FullSpectralEndpointRateLimit : ℝ :=
  ThmD.HD 1 + wideRepairAlpha ^ 2 *
    (ThmD.HD 1 - q7FullSpectralPackingLoss) ^ 2

theorem tendsto_q7FullSpectralEndpointScale :
    Tendsto q7FullSpectralEndpointScale atTop (nhds 1) := by
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h := hconst.sub
    (tendsto_endpointStep_zero.const_mul q7FullSpectralEndpointReserve)
  change Tendsto
    (fun n : ℕ => 1 - q7FullSpectralEndpointReserve * endpointStep n)
      atTop (nhds 1)
  simpa only [mul_zero, sub_zero] using h

theorem tendsto_q7FullSpectralEndpointQ :
    Tendsto q7FullSpectralEndpointQ atTop
      (nhds (ThmD.HD 1 - q7FullSpectralPackingLoss)) := by
  have hsum := tendsto_endpointLam_one.add tendsto_endpointStep_zero
  have hscaled := hsum.const_mul q7FullSpectralPackingLoss
  have h := ((tendsto_endpointHD.sub tendsto_endpointStep_zero).sub
    hscaled).sub tendsto_endpointStep_zero
  change Tendsto
    (fun n : ℕ => ThmD.HD (endpointLam n) - endpointEps n -
      q7FullSpectralPackingLoss * (endpointLam n + endpointEps n) -
      endpointEps n) atTop _
  simpa only [endpointEps, add_zero, mul_one, sub_zero] using h

theorem tendsto_q7FullSpectralEndpointRate :
    Tendsto q7FullSpectralEndpointRate atTop
      (nhds q7FullSpectralEndpointRateLimit) := by
  have hnum := ((tendsto_q7FullSpectralEndpointScale.pow 2).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => wideRepairAlpha ^ 2)
      atTop (nhds (wideRepairAlpha ^ 2)))).mul
    (tendsto_q7FullSpectralEndpointQ.pow 2)
  have hden : Tendsto
      (fun n : ℕ => (1 : ℝ) + endpointStep n) atTop
      (nhds ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add tendsto_endpointStep_zero
  have hgain := hnum.div hden (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have h := tendsto_endpointHD.add hgain
  have hend :
      ThmD.HD 1 + 1 ^ 2 * wideRepairAlpha ^ 2 *
          (ThmD.HD 1 - q7FullSpectralPackingLoss) ^ 2 / (1 + 0) =
        q7FullSpectralEndpointRateLimit := by
    unfold q7FullSpectralEndpointRateLimit
    ring
  rw [← hend]
  change Tendsto
    (fun n : ℕ => ThmD.HD (endpointLam n) +
      q7FullSpectralEndpointScale n ^ 2 * wideRepairAlpha ^ 2 *
        q7FullSpectralEndpointQ n ^ 2 / (1 + endpointStep n)) atTop _
  exact h

/-- Fixed-window hypotheses required by the q3/q4/q5/raised-q6/q7 route. -/
def Q7FullSpectralEndpointFeasible (n : ℕ) : Prop :=
  0 < endpointLam n ∧ endpointLam n < 1 ∧
  0 < endpointEps n ∧
  0 < ThmD.HD (endpointLam n) - endpointEps n ∧
  0 ≤ q7FullSpectralEndpointScale n ∧
  q7FullSpectralEndpointScale n * wideRepairRewardThree +
      (9 * Real.sqrt 3 / 2) * (1 - endpointLam n) <
    wideRepairRewardThree ∧
  q7FullSpectralEndpointScale n * wideRepairRewardFour +
      6 * Real.sqrt 3 * (1 - endpointLam n) <
    wideRepairRewardFour ∧
  q7FullSpectralEndpointScale n * wideRepairRewardFive +
      (15 * Real.sqrt 5 / 2) * (1 - endpointLam n) <
    wideRepairRewardFive ∧
  q7FullSpectralEndpointScale n * q7FullSpectralSixReward +
      9 * Real.sqrt 6 * (1 - endpointLam n) <
    q7FullSpectralSixReward ∧
  q7FullSpectralEndpointScale n * q7FullSpectralSevenReward +
      (21 * Real.sqrt 7 / 2) * (1 - endpointLam n) <
    q7FullSpectralSevenReward ∧
  0 ≤ q7FullSpectralEndpointQ n

private theorem scaled_reward_lt_reward
    {reserve reward loss step : ℝ}
    (hstep : 0 < step) (hmargin : 0 < reserve * reward - loss) :
    (1 - reserve * step) * reward + loss * step < reward := by
  nlinarith [mul_pos hstep hmargin]

theorem eventually_q7FullSpectralEndpointFeasible :
    ∀ᶠ n in atTop, Q7FullSpectralEndpointFeasible n := by
  have hqLimit : 0 < ThmD.HD 1 - q7FullSpectralPackingLoss := by
    have hloss : q7FullSpectralPackingLoss < (1 : ℝ) / 2 := by
      rw [q7FullSpectralPackingLoss_value]
      norm_num
    linarith [refined_endpoint_gap]
  have hqPos : ∀ᶠ n in atTop, 0 < q7FullSpectralEndpointQ n :=
    tendsto_q7FullSpectralEndpointQ.eventually (Ioi_mem_nhds hqLimit)
  filter_upwards [eventually_q6SuperbinEndpointFeasible, hqPos]
    with n hbase hq
  rcases hbase with
    ⟨hlam, hlamLt, heps, hH, hscale, hm3, hm4, hm5, _, _⟩
  have hstep := endpointStep_pos n
  have hlamStep : 1 - endpointLam n = endpointStep n := by
    unfold endpointLam
    ring
  have hsqrt6 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hsqrt7 : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  have hsqrt6sq : (Real.sqrt 6) ^ 2 = 6 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt7sq : (Real.sqrt 7) ^ 2 = 7 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt6lt : Real.sqrt 6 < (5 : ℝ) / 2 := by nlinarith
  have hsqrt7lt : Real.sqrt 7 < 3 := by nlinarith
  have hc6 : 0 < q7FullSpectralEndpointReserve * q7FullSpectralSixReward -
      9 * Real.sqrt 6 := by
    have hrat : (45 : ℝ) / 2 <
        q7FullSpectralEndpointReserve * q7FullSpectralSixReward := by
      norm_num [q7FullSpectralEndpointReserve, q7FullSpectralSixReward]
    nlinarith
  have hc7 : 0 < q7FullSpectralEndpointReserve * q7FullSpectralSevenReward -
      21 * Real.sqrt 7 / 2 := by
    have hrat : (63 : ℝ) / 2 <
        q7FullSpectralEndpointReserve * q7FullSpectralSevenReward := by
      norm_num [q7FullSpectralEndpointReserve, q7FullSpectralSevenReward]
    nlinarith
  have hscale' : 0 ≤ q7FullSpectralEndpointScale n := by
    simpa [q7FullSpectralEndpointScale, q7FullSpectralEndpointReserve,
      q6SuperbinEndpointScale, q6SuperbinEndpointReserve] using hscale
  have hm3' : q7FullSpectralEndpointScale n * wideRepairRewardThree +
      (9 * Real.sqrt 3 / 2) * (1 - endpointLam n) <
      wideRepairRewardThree := by
    simpa [q7FullSpectralEndpointScale, q7FullSpectralEndpointReserve,
      q6SuperbinEndpointScale, q6SuperbinEndpointReserve] using hm3
  have hm4' : q7FullSpectralEndpointScale n * wideRepairRewardFour +
      6 * Real.sqrt 3 * (1 - endpointLam n) <
      wideRepairRewardFour := by
    simpa [q7FullSpectralEndpointScale, q7FullSpectralEndpointReserve,
      q6SuperbinEndpointScale, q6SuperbinEndpointReserve] using hm4
  have hm5' : q7FullSpectralEndpointScale n * wideRepairRewardFive +
      (15 * Real.sqrt 5 / 2) * (1 - endpointLam n) <
      wideRepairRewardFive := by
    simpa [q7FullSpectralEndpointScale, q7FullSpectralEndpointReserve,
      q6SuperbinEndpointScale, q6SuperbinEndpointReserve] using hm5
  have hm6 : q7FullSpectralEndpointScale n * q7FullSpectralSixReward +
      9 * Real.sqrt 6 * (1 - endpointLam n) <
      q7FullSpectralSixReward := by
    rw [hlamStep]
    unfold q7FullSpectralEndpointScale
    exact scaled_reward_lt_reward hstep hc6
  have hm7 : q7FullSpectralEndpointScale n * q7FullSpectralSevenReward +
      (21 * Real.sqrt 7 / 2) * (1 - endpointLam n) <
      q7FullSpectralSevenReward := by
    rw [hlamStep]
    unfold q7FullSpectralEndpointScale
    exact scaled_reward_lt_reward hstep hc7
  exact ⟨hlam, hlamLt, heps, hH, hscale',
    hm3', hm4', hm5', hm6, hm7, hq.le⟩

theorem q7FullSpectral_saturated_amplitude_lower :
    (2867488631 : ℝ) / 1185376000000 ≤
      wideRepairAlpha * (ThmD.HD 1 - q7FullSpectralPackingLoss) := by
  norm_num [q7FullSpectralPackingLoss, q7FullSpectralDeficit,
    q7FullSpectralSixReward, wideRepairAlpha, wideRepairRewardFive]
  nlinarith [refined_endpoint_gap]

theorem q7FullSpectral_public_le_endpoint_gain :
    (1 : ℝ) / 170887 ≤ wideRepairAlpha ^ 2 *
      (ThmD.HD 1 - q7FullSpectralPackingLoss) ^ 2 := by
  have hamp0 : 0 ≤ (2867488631 : ℝ) / 1185376000000 := by norm_num
  have hsq := pow_le_pow_left₀ hamp0
    q7FullSpectral_saturated_amplitude_lower 2
  calc
    (1 : ℝ) / 170887 ≤
        ((2867488631 : ℝ) / 1185376000000) ^ 2 := by norm_num
    _ ≤ (wideRepairAlpha *
        (ThmD.HD 1 - q7FullSpectralPackingLoss)) ^ 2 := hsq
    _ = wideRepairAlpha ^ 2 *
        (ThmD.HD 1 - q7FullSpectralPackingLoss) ^ 2 := by ring

/-- The neighboring unit fraction is too strong for this exact amplitude
lower bound, documenting the sharp public weakening of the frozen ledger. -/
lemma q7FullSpectral_endpoint_amplitude_sq_lt_next_unit :
    ((2867488631 : ℝ) / 1185376000000) ^ 2 <
      (1 : ℝ) / 170886 := by
  norm_num

end StrictImprovement
end Zeta23

end
