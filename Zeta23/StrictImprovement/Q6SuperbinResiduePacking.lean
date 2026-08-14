/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q6SuperbinEndpointInterface

/-!
# Exact residue arithmetic for paired width-sixteen bins

Five-point blocks are packed separately in the two halves.  The `(3,3)`
remainder pair is repaired by the explicit q6 reward; all other remainders use
the existing q3/q4 rewards.  The 25 residue cases are discharged exactly.
-/

noncomputable section

open Real

namespace Zeta23
namespace StrictImprovement

def q6FineRemainderReward (r : ℕ) : ℝ :=
  if r = 3 then wideRepairRewardThree
  else if r = 4 then wideRepairRewardFour
  else 0

def q6SuperbinPairReward (n m : ℕ) : ℝ :=
  ((n / 5 + m / 5 : ℕ) : ℝ) * wideRepairRewardFive +
    if n % 5 = 3 ∧ m % 5 = 3 then q6SuperbinReward
    else q6FineRemainderReward (n % 5) +
      q6FineRemainderReward (m % 5)

/-- Worst two-half residue deficit, attained at `(3,4)` and `(4,3)`. -/
def q6SuperbinDeficit : ℝ :=
  7 * wideRepairAlpha - wideRepairRewardThree - wideRepairRewardFour

def q6SuperbinPackingLoss : ℝ :=
  q6SuperbinDeficit / (16 * wideRepairAlpha)

def q6SuperbinPackingIntercept : ℝ :=
  q6SuperbinDeficit / wideRepairAlpha

lemma q6SuperbinDeficit_value : q6SuperbinDeficit =
    (25442263 : ℝ) / 850000000 := by
  norm_num [q6SuperbinDeficit, wideRepairAlpha, wideRepairRewardFive,
    wideRepairRewardThree, wideRepairRewardFour]

lemma q6SuperbinPackingLoss_value : q6SuperbinPackingLoss =
    (25442263 : ℝ) / 86013744 := by
  norm_num [q6SuperbinPackingLoss, q6SuperbinDeficit, wideRepairAlpha,
    wideRepairRewardFive, wideRepairRewardThree, wideRepairRewardFour]

lemma q6SuperbinPackingIntercept_value : q6SuperbinPackingIntercept =
    (25442263 : ℝ) / 5375859 := by
  norm_num [q6SuperbinPackingIntercept, q6SuperbinDeficit, wideRepairAlpha,
    wideRepairRewardFive, wideRepairRewardThree, wideRepairRewardFour]

lemma q6SuperbinDeficit_nonneg : 0 ≤ q6SuperbinDeficit := by
  rw [q6SuperbinDeficit_value]
  norm_num

lemma q6SuperbinPackingLoss_nonneg : 0 ≤ q6SuperbinPackingLoss := by
  rw [q6SuperbinPackingLoss_value]
  norm_num

lemma q6SuperbinPackingIntercept_nonneg :
    0 ≤ q6SuperbinPackingIntercept := by
  rw [q6SuperbinPackingIntercept_value]
  norm_num

/-- Exact transition slack making the q6 reward preferable at `(3,3)`. -/
lemma q6Superbin_transition_strict :
    wideRepairRewardThree + wideRepairRewardFour - wideRepairAlpha <
      q6SuperbinReward := by
  norm_num [q6SuperbinReward, wideRepairRewardThree,
    wideRepairRewardFour, wideRepairAlpha, wideRepairRewardFive]

/-- The complete 25-case residue inequality. -/
theorem q6SuperbinPairReward_lower (n m : ℕ) :
    wideRepairAlpha * ((n + m : ℕ) : ℝ) - q6SuperbinDeficit ≤
      q6SuperbinPairReward n m := by
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
    simp [q6SuperbinPairReward, q6FineRemainderReward, hn, hm,
      q6SuperbinReward, q6SuperbinDeficit, wideRepairAlpha,
      wideRepairRewardFive, wideRepairRewardThree,
      wideRepairRewardFour] <;>
    norm_num <;>
    linarith

lemma q6FineRemainderReward_nonneg (r : ℕ) :
    0 ≤ q6FineRemainderReward r := by
  unfold q6FineRemainderReward
  split_ifs <;>
    norm_num [wideRepairRewardThree, wideRepairRewardFour]

lemma q6SuperbinPairReward_nonneg (n m : ℕ) :
    0 ≤ q6SuperbinPairReward n m := by
  unfold q6SuperbinPairReward
  split_ifs
  · exact add_nonneg
      (mul_nonneg (by positivity) wideRepairRewardFive_nonneg)
      q6SuperbinReward_nonneg
  · exact add_nonneg
      (mul_nonneg (by positivity) wideRepairRewardFive_nonneg)
      (add_nonneg (q6FineRemainderReward_nonneg _)
        (q6FineRemainderReward_nonneg _))

/-- Sum of the exact pairwise residue table over an arbitrary superbin type. -/
theorem sum_q6SuperbinPairReward_lower
    {B : Type*} [Fintype B] [DecidableEq B]
    (left right : B → ℕ) :
    wideRepairAlpha *
        ((∑ b, (left b + right b : ℕ) : ℕ) : ℝ) -
        q6SuperbinDeficit * (Fintype.card B : ℝ) ≤
      ∑ b, q6SuperbinPairReward (left b) (right b) := by
  calc
    wideRepairAlpha *
          ((∑ b, (left b + right b : ℕ) : ℕ) : ℝ) -
          q6SuperbinDeficit * (Fintype.card B : ℝ) =
        ∑ b : B, (wideRepairAlpha *
          (((left b + right b : ℕ) : ℝ)) - q6SuperbinDeficit) := by
      push_cast
      simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ ∑ b, q6SuperbinPairReward (left b) (right b) :=
      Finset.sum_le_sum fun b _ => q6SuperbinPairReward_lower (left b) (right b)

/-- The `D/16+1` superbin count turns the residue table into the global
affine reward bound. -/
theorem sum_q6SuperbinPairReward_target_lower
    {S B : Type*} [Fintype S]
    [Fintype B] [DecidableEq B]
    (left right : B → ℕ)
    (hcover : ∑ b, (left b + right b) = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 16 + 1) :
    wideRepairAlpha * max 0
        ((Fintype.card S : ℝ) - q6SuperbinPackingLoss * D -
          q6SuperbinPackingIntercept) ≤
      ∑ b, q6SuperbinPairReward (left b) (right b) := by
  have hrewards := sum_q6SuperbinPairReward_lower left right
  rw [hcover] at hrewards
  have hdefcard : q6SuperbinDeficit * (Fintype.card B : ℝ) ≤
      q6SuperbinDeficit * (D / 16 + 1) :=
    mul_le_mul_of_nonneg_left hbins q6SuperbinDeficit_nonneg
  have hbase : wideRepairAlpha *
      ((Fintype.card S : ℝ) - q6SuperbinPackingLoss * D -
        q6SuperbinPackingIntercept) ≤
      ∑ b, q6SuperbinPairReward (left b) (right b) := by
    have halphaNe : wideRepairAlpha ≠ 0 := ne_of_gt wideRepairAlpha_pos
    calc
      wideRepairAlpha *
          ((Fintype.card S : ℝ) - q6SuperbinPackingLoss * D -
            q6SuperbinPackingIntercept) =
          wideRepairAlpha * (Fintype.card S : ℝ) -
            q6SuperbinDeficit * (D / 16 + 1) := by
        unfold q6SuperbinPackingLoss q6SuperbinPackingIntercept
        field_simp [halphaNe]
        ring
      _ ≤ wideRepairAlpha * (Fintype.card S : ℝ) -
          q6SuperbinDeficit * (Fintype.card B : ℝ) := by linarith
      _ ≤ ∑ b, q6SuperbinPairReward (left b) (right b) := hrewards
  have hrewards0 : 0 ≤
      ∑ b, q6SuperbinPairReward (left b) (right b) :=
    Finset.sum_nonneg fun b _ => q6SuperbinPairReward_nonneg _ _
  by_cases harg : 0 ≤
      (Fintype.card S : ℝ) - q6SuperbinPackingLoss * D -
        q6SuperbinPackingIntercept
  · rw [max_eq_right harg]
    exact hbase
  · have harg' :
        (Fintype.card S : ℝ) - q6SuperbinPackingLoss * D -
          q6SuperbinPackingIntercept ≤ 0 := le_of_not_ge harg
    rw [max_eq_left harg']
    simpa using hrewards0

/-- The exact bottleneck pair realizes the deficit. -/
lemma q6SuperbinPairReward_three_four :
    q6SuperbinPairReward 3 4 =
      wideRepairRewardThree + wideRepairRewardFour := by
  norm_num [q6SuperbinPairReward, q6FineRemainderReward]

end StrictImprovement
end Zeta23

end
