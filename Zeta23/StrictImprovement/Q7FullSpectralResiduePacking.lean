/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7FullSpectralEndpointInterface

/-!
# Exact residue arithmetic for the full-spectral q7 superbin repair

Five-point blocks are packed separately in the two halves.  The `(3,3)` pair
uses the raised six-point reward, while `(3,4)` and `(4,3)` use the oriented
seven-point reward.  All 25 residue cases are discharged exactly.
-/

noncomputable section

open Real

namespace Zeta23
namespace StrictImprovement

def q7FullSpectralFineRemainderReward (r : ℕ) : ℝ :=
  if r = 3 then wideRepairRewardThree
  else if r = 4 then wideRepairRewardFour
  else 0

def q7FullSpectralPairReward (n m : ℕ) : ℝ :=
  ((n / 5 + m / 5 : ℕ) : ℝ) * wideRepairRewardFive +
    if n % 5 = 3 ∧ m % 5 = 3 then q7FullSpectralSixReward
    else if (n % 5 = 3 ∧ m % 5 = 4) ∨
        (n % 5 = 4 ∧ m % 5 = 3) then q7FullSpectralSevenReward
    else q7FullSpectralFineRemainderReward (n % 5) +
      q7FullSpectralFineRemainderReward (m % 5)

/-- Common worst deficit at `(3,3)`, `(3,4)`, and `(4,3)`. -/
def q7FullSpectralDeficit : ℝ :=
  6 * wideRepairAlpha - q7FullSpectralSixReward

def q7FullSpectralPackingLoss : ℝ :=
  q7FullSpectralDeficit / (16 * wideRepairAlpha)

def q7FullSpectralPackingIntercept : ℝ :=
  q7FullSpectralDeficit / wideRepairAlpha

lemma q7FullSpectral_transition_eq :
    q7FullSpectralSevenReward = wideRepairAlpha + q7FullSpectralSixReward := by
  norm_num [q7FullSpectralSevenReward, q7FullSpectralSixReward,
    wideRepairAlpha, wideRepairRewardFive]

lemma q7FullSpectralDeficit_value : q7FullSpectralDeficit =
    (733681 : ℝ) / 25000000 := by
  norm_num [q7FullSpectralDeficit, q7FullSpectralSixReward,
    wideRepairAlpha, wideRepairRewardFive]

lemma q7FullSpectralPackingLoss_value : q7FullSpectralPackingLoss =
    (733681 : ℝ) / 2529816 := by
  norm_num [q7FullSpectralPackingLoss, q7FullSpectralDeficit,
    q7FullSpectralSixReward, wideRepairAlpha, wideRepairRewardFive]

lemma q7FullSpectralPackingIntercept_value : q7FullSpectralPackingIntercept =
    (1467362 : ℝ) / 316227 := by
  norm_num [q7FullSpectralPackingIntercept, q7FullSpectralDeficit,
    q7FullSpectralSixReward, wideRepairAlpha, wideRepairRewardFive]

lemma q7FullSpectralDeficit_nonneg : 0 ≤ q7FullSpectralDeficit := by
  rw [q7FullSpectralDeficit_value]
  norm_num

lemma q7FullSpectralPackingLoss_nonneg : 0 ≤ q7FullSpectralPackingLoss := by
  rw [q7FullSpectralPackingLoss_value]
  norm_num

lemma q7FullSpectralPackingIntercept_nonneg :
    0 ≤ q7FullSpectralPackingIntercept := by
  rw [q7FullSpectralPackingIntercept_value]
  norm_num

/-- The complete 25-case paired-residue inequality. -/
theorem q7FullSpectralPairReward_lower (n m : ℕ) :
    wideRepairAlpha * ((n + m : ℕ) : ℝ) - q7FullSpectralDeficit ≤
      q7FullSpectralPairReward n m := by
  have hnDecomp : n % 5 + 5 * (n / 5) = n := Nat.mod_add_div n 5
  have hmDecomp : m % 5 + 5 * (m / 5) = m := Nat.mod_add_div m 5
  have hnReal : (n : ℝ) = ((n % 5 : ℕ) : ℝ) +
      5 * ((n / 5 : ℕ) : ℝ) := by
    exact_mod_cast hnDecomp.symm
  have hmReal : (m : ℝ) = ((m % 5 : ℕ) : ℝ) +
      5 * ((m / 5 : ℕ) : ℝ) := by
    exact_mod_cast hmDecomp.symm
  have hnMod : n % 5 < 5 := Nat.mod_lt n (by norm_num)
  have hmMod : m % 5 < 5 := Nat.mod_lt m (by norm_num)
  push_cast
  rw [hnReal, hmReal]
  interval_cases hn : n % 5 <;>
    interval_cases hm : m % 5 <;>
    simp [q7FullSpectralPairReward, q7FullSpectralFineRemainderReward, hn, hm,
      q7FullSpectralSixReward, q7FullSpectralSevenReward, q7FullSpectralDeficit,
      wideRepairAlpha, wideRepairRewardFive, wideRepairRewardThree,
      wideRepairRewardFour] <;>
    norm_num <;>
    linarith

lemma q7FullSpectralFineRemainderReward_nonneg (r : ℕ) :
    0 ≤ q7FullSpectralFineRemainderReward r := by
  unfold q7FullSpectralFineRemainderReward
  split_ifs <;>
    norm_num [wideRepairRewardThree, wideRepairRewardFour]

lemma q7FullSpectralPairReward_nonneg (n m : ℕ) :
    0 ≤ q7FullSpectralPairReward n m := by
  unfold q7FullSpectralPairReward
  split_ifs
  · exact add_nonneg
      (mul_nonneg (by positivity) wideRepairRewardFive_nonneg)
      q7FullSpectralSixReward_nonneg
  · exact add_nonneg
      (mul_nonneg (by positivity) wideRepairRewardFive_nonneg)
      q7FullSpectralSevenReward_nonneg
  · exact add_nonneg
      (mul_nonneg (by positivity) wideRepairRewardFive_nonneg)
      (add_nonneg (q7FullSpectralFineRemainderReward_nonneg _)
        (q7FullSpectralFineRemainderReward_nonneg _))

theorem sum_q7FullSpectralPairReward_lower
    {B : Type*} [Fintype B] [DecidableEq B]
    (left right : B → ℕ) :
    wideRepairAlpha *
        ((∑ b, (left b + right b : ℕ) : ℕ) : ℝ) -
        q7FullSpectralDeficit * (Fintype.card B : ℝ) ≤
      ∑ b, q7FullSpectralPairReward (left b) (right b) := by
  calc
    wideRepairAlpha *
          ((∑ b, (left b + right b : ℕ) : ℕ) : ℝ) -
          q7FullSpectralDeficit * (Fintype.card B : ℝ) =
        ∑ b : B, (wideRepairAlpha *
          (((left b + right b : ℕ) : ℝ)) - q7FullSpectralDeficit) := by
      push_cast
      simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ ∑ b, q7FullSpectralPairReward (left b) (right b) :=
      Finset.sum_le_sum fun b _ =>
        q7FullSpectralPairReward_lower (left b) (right b)

/-- The `D/16+1` superbin count turns the residue table into the global
affine reward bound. -/
theorem sum_q7FullSpectralPairReward_target_lower
    {S B : Type*} [Fintype S]
    [Fintype B] [DecidableEq B]
    (left right : B → ℕ)
    (hcover : ∑ b, (left b + right b) = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 16 + 1) :
    wideRepairAlpha * max 0
        ((Fintype.card S : ℝ) - q7FullSpectralPackingLoss * D -
          q7FullSpectralPackingIntercept) ≤
      ∑ b, q7FullSpectralPairReward (left b) (right b) := by
  have hrewards := sum_q7FullSpectralPairReward_lower left right
  rw [hcover] at hrewards
  have hdefcard : q7FullSpectralDeficit * (Fintype.card B : ℝ) ≤
      q7FullSpectralDeficit * (D / 16 + 1) :=
    mul_le_mul_of_nonneg_left hbins q7FullSpectralDeficit_nonneg
  have hbase : wideRepairAlpha *
      ((Fintype.card S : ℝ) - q7FullSpectralPackingLoss * D -
        q7FullSpectralPackingIntercept) ≤
      ∑ b, q7FullSpectralPairReward (left b) (right b) := by
    have halphaNe : wideRepairAlpha ≠ 0 := ne_of_gt wideRepairAlpha_pos
    calc
      wideRepairAlpha *
          ((Fintype.card S : ℝ) - q7FullSpectralPackingLoss * D -
            q7FullSpectralPackingIntercept) =
          wideRepairAlpha * (Fintype.card S : ℝ) -
            q7FullSpectralDeficit * (D / 16 + 1) := by
        unfold q7FullSpectralPackingLoss q7FullSpectralPackingIntercept
        field_simp [halphaNe]
        ring
      _ ≤ wideRepairAlpha * (Fintype.card S : ℝ) -
          q7FullSpectralDeficit * (Fintype.card B : ℝ) := by linarith
      _ ≤ ∑ b, q7FullSpectralPairReward (left b) (right b) := hrewards
  have hrewards0 : 0 ≤
      ∑ b, q7FullSpectralPairReward (left b) (right b) :=
    Finset.sum_nonneg fun b _ => q7FullSpectralPairReward_nonneg _ _
  by_cases harg : 0 ≤
      (Fintype.card S : ℝ) - q7FullSpectralPackingLoss * D -
        q7FullSpectralPackingIntercept
  · rw [max_eq_right harg]
    exact hbase
  · have harg' :
        (Fintype.card S : ℝ) - q7FullSpectralPackingLoss * D -
          q7FullSpectralPackingIntercept ≤ 0 := le_of_not_ge harg
    rw [max_eq_left harg']
    simpa using hrewards0

lemma q7FullSpectralPairReward_three_three :
    q7FullSpectralPairReward 3 3 = q7FullSpectralSixReward := by
  norm_num [q7FullSpectralPairReward]

lemma q7FullSpectralPairReward_three_four :
    q7FullSpectralPairReward 3 4 = q7FullSpectralSevenReward := by
  norm_num [q7FullSpectralPairReward]

lemma q7FullSpectralPairReward_four_three :
    q7FullSpectralPairReward 4 3 = q7FullSpectralSevenReward := by
  norm_num [q7FullSpectralPairReward]

end StrictImprovement
end Zeta23

end
