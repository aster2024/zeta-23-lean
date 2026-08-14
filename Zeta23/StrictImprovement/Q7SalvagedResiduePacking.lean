/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7SalvagedEndpointInterface

/-!
# Exact residue arithmetic for the salvaged q7 superbin repair

Five-point blocks are packed separately in the two halves.  The `(3,3)` pair
uses the raised six-point reward, while `(3,4)` and `(4,3)` use the oriented
seven-point reward.  All 25 residue cases are discharged exactly.
-/

noncomputable section

open Real

namespace Zeta23
namespace StrictImprovement

def q7SalvagedFineRemainderReward (r : ℕ) : ℝ :=
  if r = 3 then wideRepairRewardThree
  else if r = 4 then wideRepairRewardFour
  else 0

def q7SalvagedPairReward (n m : ℕ) : ℝ :=
  ((n / 5 + m / 5 : ℕ) : ℝ) * wideRepairRewardFive +
    if n % 5 = 3 ∧ m % 5 = 3 then q7SalvagedSixReward
    else if (n % 5 = 3 ∧ m % 5 = 4) ∨
        (n % 5 = 4 ∧ m % 5 = 3) then q7SalvagedSevenReward
    else q7SalvagedFineRemainderReward (n % 5) +
      q7SalvagedFineRemainderReward (m % 5)

/-- Common worst deficit at `(3,3)`, `(3,4)`, and `(4,3)`. -/
def q7SalvagedDeficit : ℝ :=
  6 * wideRepairAlpha - q7SalvagedSixReward

def q7SalvagedPackingLoss : ℝ :=
  q7SalvagedDeficit / (16 * wideRepairAlpha)

def q7SalvagedPackingIntercept : ℝ :=
  q7SalvagedDeficit / wideRepairAlpha

lemma q7Salvaged_transition_eq :
    q7SalvagedSevenReward = wideRepairAlpha + q7SalvagedSixReward := by
  norm_num [q7SalvagedSevenReward, q7SalvagedSixReward,
    wideRepairAlpha, wideRepairRewardFive]

lemma q7SalvagedDeficit_value : q7SalvagedDeficit =
    (1495239 : ℝ) / 50000000 := by
  norm_num [q7SalvagedDeficit, q7SalvagedSixReward,
    wideRepairAlpha, wideRepairRewardFive]

lemma q7SalvagedPackingLoss_value : q7SalvagedPackingLoss =
    (498413 : ℝ) / 1686544 := by
  norm_num [q7SalvagedPackingLoss, q7SalvagedDeficit,
    q7SalvagedSixReward, wideRepairAlpha, wideRepairRewardFive]

lemma q7SalvagedPackingIntercept_value : q7SalvagedPackingIntercept =
    (498413 : ℝ) / 105409 := by
  norm_num [q7SalvagedPackingIntercept, q7SalvagedDeficit,
    q7SalvagedSixReward, wideRepairAlpha, wideRepairRewardFive]

lemma q7SalvagedDeficit_nonneg : 0 ≤ q7SalvagedDeficit := by
  rw [q7SalvagedDeficit_value]
  norm_num

lemma q7SalvagedPackingLoss_nonneg : 0 ≤ q7SalvagedPackingLoss := by
  rw [q7SalvagedPackingLoss_value]
  norm_num

lemma q7SalvagedPackingIntercept_nonneg :
    0 ≤ q7SalvagedPackingIntercept := by
  rw [q7SalvagedPackingIntercept_value]
  norm_num

/-- The complete 25-case paired-residue inequality. -/
theorem q7SalvagedPairReward_lower (n m : ℕ) :
    wideRepairAlpha * ((n + m : ℕ) : ℝ) - q7SalvagedDeficit ≤
      q7SalvagedPairReward n m := by
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
    simp [q7SalvagedPairReward, q7SalvagedFineRemainderReward, hn, hm,
      q7SalvagedSixReward, q7SalvagedSevenReward, q7SalvagedDeficit,
      wideRepairAlpha, wideRepairRewardFive, wideRepairRewardThree,
      wideRepairRewardFour] <;>
    norm_num <;>
    linarith

lemma q7SalvagedFineRemainderReward_nonneg (r : ℕ) :
    0 ≤ q7SalvagedFineRemainderReward r := by
  unfold q7SalvagedFineRemainderReward
  split_ifs <;>
    norm_num [wideRepairRewardThree, wideRepairRewardFour]

lemma q7SalvagedPairReward_nonneg (n m : ℕ) :
    0 ≤ q7SalvagedPairReward n m := by
  unfold q7SalvagedPairReward
  split_ifs
  · exact add_nonneg
      (mul_nonneg (by positivity) wideRepairRewardFive_nonneg)
      q7SalvagedSixReward_nonneg
  · exact add_nonneg
      (mul_nonneg (by positivity) wideRepairRewardFive_nonneg)
      q7SalvagedSevenReward_nonneg
  · exact add_nonneg
      (mul_nonneg (by positivity) wideRepairRewardFive_nonneg)
      (add_nonneg (q7SalvagedFineRemainderReward_nonneg _)
        (q7SalvagedFineRemainderReward_nonneg _))

theorem sum_q7SalvagedPairReward_lower
    {B : Type*} [Fintype B] [DecidableEq B]
    (left right : B → ℕ) :
    wideRepairAlpha *
        ((∑ b, (left b + right b : ℕ) : ℕ) : ℝ) -
        q7SalvagedDeficit * (Fintype.card B : ℝ) ≤
      ∑ b, q7SalvagedPairReward (left b) (right b) := by
  calc
    wideRepairAlpha *
          ((∑ b, (left b + right b : ℕ) : ℕ) : ℝ) -
          q7SalvagedDeficit * (Fintype.card B : ℝ) =
        ∑ b : B, (wideRepairAlpha *
          (((left b + right b : ℕ) : ℝ)) - q7SalvagedDeficit) := by
      push_cast
      simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ ∑ b, q7SalvagedPairReward (left b) (right b) :=
      Finset.sum_le_sum fun b _ =>
        q7SalvagedPairReward_lower (left b) (right b)

/-- The `D/16+1` superbin count turns the residue table into the global
affine reward bound. -/
theorem sum_q7SalvagedPairReward_target_lower
    {S B : Type*} [Fintype S]
    [Fintype B] [DecidableEq B]
    (left right : B → ℕ)
    (hcover : ∑ b, (left b + right b) = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 16 + 1) :
    wideRepairAlpha * max 0
        ((Fintype.card S : ℝ) - q7SalvagedPackingLoss * D -
          q7SalvagedPackingIntercept) ≤
      ∑ b, q7SalvagedPairReward (left b) (right b) := by
  have hrewards := sum_q7SalvagedPairReward_lower left right
  rw [hcover] at hrewards
  have hdefcard : q7SalvagedDeficit * (Fintype.card B : ℝ) ≤
      q7SalvagedDeficit * (D / 16 + 1) :=
    mul_le_mul_of_nonneg_left hbins q7SalvagedDeficit_nonneg
  have hbase : wideRepairAlpha *
      ((Fintype.card S : ℝ) - q7SalvagedPackingLoss * D -
        q7SalvagedPackingIntercept) ≤
      ∑ b, q7SalvagedPairReward (left b) (right b) := by
    have halphaNe : wideRepairAlpha ≠ 0 := ne_of_gt wideRepairAlpha_pos
    calc
      wideRepairAlpha *
          ((Fintype.card S : ℝ) - q7SalvagedPackingLoss * D -
            q7SalvagedPackingIntercept) =
          wideRepairAlpha * (Fintype.card S : ℝ) -
            q7SalvagedDeficit * (D / 16 + 1) := by
        unfold q7SalvagedPackingLoss q7SalvagedPackingIntercept
        field_simp [halphaNe]
        ring
      _ ≤ wideRepairAlpha * (Fintype.card S : ℝ) -
          q7SalvagedDeficit * (Fintype.card B : ℝ) := by linarith
      _ ≤ ∑ b, q7SalvagedPairReward (left b) (right b) := hrewards
  have hrewards0 : 0 ≤
      ∑ b, q7SalvagedPairReward (left b) (right b) :=
    Finset.sum_nonneg fun b _ => q7SalvagedPairReward_nonneg _ _
  by_cases harg : 0 ≤
      (Fintype.card S : ℝ) - q7SalvagedPackingLoss * D -
        q7SalvagedPackingIntercept
  · rw [max_eq_right harg]
    exact hbase
  · have harg' :
        (Fintype.card S : ℝ) - q7SalvagedPackingLoss * D -
          q7SalvagedPackingIntercept ≤ 0 := le_of_not_ge harg
    rw [max_eq_left harg']
    simpa using hrewards0

lemma q7SalvagedPairReward_three_three :
    q7SalvagedPairReward 3 3 = q7SalvagedSixReward := by
  norm_num [q7SalvagedPairReward]

lemma q7SalvagedPairReward_three_four :
    q7SalvagedPairReward 3 4 = q7SalvagedSevenReward := by
  norm_num [q7SalvagedPairReward]

lemma q7SalvagedPairReward_four_three :
    q7SalvagedPairReward 4 3 = q7SalvagedSevenReward := by
  norm_num [q7SalvagedPairReward]

end StrictImprovement
end Zeta23

end
