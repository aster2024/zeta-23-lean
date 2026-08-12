/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.RootLocalization

/-!
# Exact arithmetic for the wider-window four-point route

This module contains the analytic inequalities and finite rational ledger used
to extend endpoint-kernel localization from three roots below 8 * pi to six
roots below 12 * pi.  It contains no floating-point literal or root
approximation.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Real Set

namespace Zeta23
namespace StrictImprovement

def widerRadius : ℝ := 1 / 8

def widerCorrelationThreshold : ℝ := 1815107 / 989072150

lemma widerRadius_pos : 0 < widerRadius := by
  norm_num [widerRadius]

lemma widerCorrelationThreshold_pos : 0 < widerCorrelationThreshold := by
  norm_num [widerCorrelationThreshold]

def widerCosLower : ℝ := 12359 / 12800

def widerDerivativeLower (n : ℕ) : ℝ :=
  (3 * (n : ℝ) - 1 / 16) * widerCosLower - 129 / 1280

/-- The second root offset lies beyond the exact rational test point 11/60. -/
theorem eleven_sixtieths_lt_epsilonTwo :
    (11 : ℝ) / 60 < epsilonTwo := by
  have htan := tan_le_quadratic_fraction
    (x := (11 : ℝ) / 120) (by norm_num) (by norm_num)
  have hpi : Real.pi < (22 : ℝ) / 7 := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    linarith
  have htanPos : 0 < Real.tan ((11 : ℝ) / 120) := by
    have hlt : (11 : ℝ) / 120 < Real.tan ((11 : ℝ) / 120) := by
      apply Real.lt_tan
      · norm_num
      · nlinarith [Real.pi_gt_three]
    nlinarith
  have hcoef :
      2 * Real.pi * (2 : ℝ) + (11 : ℝ) / 60 <
        (88 : ℝ) / 7 + 11 / 60 := by
    nlinarith
  have hcoefNonneg : 0 ≤ (88 : ℝ) / 7 + 11 / 60 := by norm_num
  have htest : offsetEquation 2 ((11 : ℝ) / 60) < endpointKappa := by
    unfold offsetEquation
    calc
      (2 * Real.pi * (2 : ℝ) + 11 / 60) * Real.tan ((11 / 60) / 2)
          < ((88 : ℝ) / 7 + 11 / 60) *
              Real.tan ((11 : ℝ) / 120) := by
            rw [show ((11 : ℝ) / 60) / 2 = 11 / 120 by norm_num]
            exact mul_lt_mul_of_pos_right hcoef htanPos
      _ ≤ ((88 : ℝ) / 7 + 11 / 60) *
              ((11 : ℝ) / 120 / (1 - ((11 : ℝ) / 120) ^ 2 / 2)) :=
            mul_le_mul_of_nonneg_left htan hcoefNonneg
      _ = (235708 : ℝ) / 200753 := by norm_num
      _ < (6 : ℝ) / 5 := by norm_num
      _ < endpointKappa := six_fifths_lt_endpointKappa
  have hroot : offsetEquation 2 epsilonTwo = endpointKappa := by
    simpa [epsilonTwo] using rootOffset_equation 2 (by norm_num)
  have htestMem : (11 : ℝ) / 60 ∈ Set.Icc (0 : ℝ) (2 / 5) := by norm_num
  have hepsMem : epsilonTwo ∈ Set.Icc (0 : ℝ) (2 / 5) :=
    ⟨epsilonTwo_mem.1.le, epsilonTwo_mem.2.le⟩
  by_contra hnot
  have hle : epsilonTwo ≤ (11 : ℝ) / 60 := not_lt.mp hnot
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq] at hroot
    linarith
  · have hmono := offsetEquation_strictMonoOn 2 (by norm_num)
      hepsMem htestMem hlt
    linarith

/-- The sixth positive root offset lies below the exact rational test point
`1/15`.  Together with `1/8 < epsilonThree`, this removes the exceptional
smaller separation floor in the `(3,3,6)` row. -/
theorem epsilonSix_lt_one_fifteenth :
    rootOffset 6 (by norm_num) < (1 : ℝ) / 15 := by
  have htan : (1 : ℝ) / 30 < Real.tan ((1 : ℝ) / 30) := by
    apply Real.lt_tan
    · norm_num
    · nlinarith [Real.pi_gt_three]
  have hcoef :
      12 * ((157 : ℝ) / 50) + 1 / 15 <
        12 * Real.pi + 1 / 15 := by
    nlinarith [Real.pi_gt_d2]
  have hcoefPos : 0 < 12 * Real.pi + (1 : ℝ) / 15 := by
    nlinarith [Real.pi_gt_three]
  have hprod :
      (12 * ((157 : ℝ) / 50) + 1 / 15) * (1 / 30) <
        (12 * Real.pi + 1 / 15) * Real.tan (1 / 30) := by
    calc
      (12 * ((157 : ℝ) / 50) + 1 / 15) * (1 / 30)
          < (12 * Real.pi + 1 / 15) * (1 / 30) :=
            mul_lt_mul_of_pos_right hcoef (by norm_num)
      _ < (12 * Real.pi + 1 / 15) * Real.tan (1 / 30) :=
        mul_lt_mul_of_pos_left htan hcoefPos
  have htest : endpointKappa < offsetEquation 6 ((1 : ℝ) / 15) := by
    unfold offsetEquation
    calc
      endpointKappa ≤ (49 : ℝ) / 40 := endpointKappa_le
      _ < (2831 : ℝ) / 2250 := by norm_num
      _ = (12 * ((157 : ℝ) / 50) + 1 / 15) * (1 / 30) := by
        norm_num
      _ < (12 * Real.pi + 1 / 15) * Real.tan (1 / 30) := hprod
      _ = (2 * Real.pi * (6 : ℝ) + 1 / 15) *
          Real.tan (((1 : ℝ) / 15) / 2) := by ring
  let e6 := rootOffset 6 (by norm_num)
  have he6Mem : e6 ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    have h := rootOffset_mem 6 (by norm_num)
    exact ⟨h.1.le, h.2.le⟩
  have htestMem : (1 : ℝ) / 15 ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    norm_num
  have hroot : offsetEquation 6 e6 = endpointKappa := by
    simpa [e6] using rootOffset_equation 6 (by norm_num)
  by_contra hnot
  have hle : (1 : ℝ) / 15 ≤ e6 := not_lt.mp hnot
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [← heq] at hroot
    linarith
  · have hmono := offsetEquation_strictMonoOn 6 (by norm_num)
      htestMem he6Mem hlt
    rw [hroot] at hmono
    linarith

/-- The exact cosine bound used on the enlarged rational strip. -/
lemma wider_cos_lower {e : ℝ}
    (he : e ∈ Set.Icc (-(1 : ℝ) / 8) (21 / 40)) :
    widerCosLower ≤ Real.cos (e / 2) := by
  have hsum : 0 ≤ (21 : ℝ) / 40 + e := by linarith [he.1]
  have hprod :
      0 ≤ ((21 : ℝ) / 40 - e) * ((21 : ℝ) / 40 + e) :=
    mul_nonneg (sub_nonneg.mpr he.2) hsum
  have hesq : (e / 2) ^ 2 ≤ ((21 : ℝ) / 80) ^ 2 := by
    nlinarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x := e / 2)
  norm_num [widerCosLower] at hcos ⊢
  nlinarith

/-- The potentially negative sine term in the derivative has a uniform exact
lower bound on the enlarged strip. -/
lemma wider_sine_term_lower {e : ℝ}
    (he : e ∈ Set.Icc (-(1 : ℝ) / 8) (21 / 40)) :
    -(129 : ℝ) / 1280 ≤
      (1 + endpointKappa / 2) * Real.sin (e / 2) := by
  have hcoefPos : 0 < 1 + endpointKappa / 2 := by
    nlinarith [endpointKappa_pos]
  by_cases he0 : 0 ≤ e
  · have hsin : 0 ≤ Real.sin (e / 2) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · linarith
      · nlinarith [he.2, Real.pi_gt_three]
    have hmul := mul_nonneg hcoefPos.le hsin
    linarith
  · have hsinLe := Real.sin_le (show 0 ≤ -(e / 2) by linarith)
    rw [Real.sin_neg] at hsinLe
    have hsinLower : -(1 : ℝ) / 16 ≤ Real.sin (e / 2) := by
      nlinarith [he.1]
    by_cases hs : 0 ≤ Real.sin (e / 2)
    · have hmul := mul_nonneg hcoefPos.le hs
      linarith
    · have hsNonpos : Real.sin (e / 2) ≤ 0 := le_of_not_ge hs
      have hcoefUpper : 1 + endpointKappa / 2 ≤ (129 : ℝ) / 80 := by
        nlinarith [endpointKappa_le]
      have hmul :
          (129 : ℝ) / 80 * Real.sin (e / 2) ≤
            (1 + endpointKappa / 2) * Real.sin (e / 2) :=
        mul_le_mul_of_nonpos_right hcoefUpper hsNonpos
      have hrat :
          -(129 : ℝ) / 1280 ≤
            (129 : ℝ) / 80 * Real.sin (e / 2) := by
        nlinarith
      exact hrat.trans hmul

/-- Uniform derivative bound on the enlarged strip.  The result is stated for
every n >= 1; the wider route consumes only n <= 6. -/
theorem wider_offset_derivative_lower
    {n : ℕ} (hn : 1 ≤ n) {e : ℝ}
    (he : e ∈ Set.Icc (-(1 : ℝ) / 8) (21 / 40)) :
    widerDerivativeLower n ≤ offsetNumeratorDerivative n e := by
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnReal
  have hpiMul : 3 * (n : ℝ) < Real.pi * (n : ℝ) :=
    mul_lt_mul_of_pos_right Real.pi_gt_three hnPos
  have hcoef :
      3 * (n : ℝ) - 1 / 16 ≤
        (2 * Real.pi * (n : ℝ) + e) / 2 := by
    nlinarith [he.1]
  have hcos := wider_cos_lower he
  have hcoefPos :
      0 < (2 * Real.pi * (n : ℝ) + e) / 2 := by
    nlinarith [hpiMul, he.1]
  have hsecond :
      (3 * (n : ℝ) - 1 / 16) * widerCosLower ≤
        (2 * Real.pi * (n : ℝ) + e) / 2 * Real.cos (e / 2) := by
    calc
      (3 * (n : ℝ) - 1 / 16) * widerCosLower
          ≤ (2 * Real.pi * (n : ℝ) + e) / 2 * widerCosLower :=
            mul_le_mul_of_nonneg_right hcoef (by norm_num [widerCosLower])
      _ ≤ (2 * Real.pi * (n : ℝ) + e) / 2 * Real.cos (e / 2) :=
            mul_le_mul_of_nonneg_left hcos hcoefPos.le
  have hfirst := wider_sine_term_lower he
  unfold widerDerivativeLower offsetNumeratorDerivative
  linarith

/-- Exact rational reciprocal-slope denominators for the six local linear
kernel bounds.  These retain all of the certified rational slope supplied by
the common derivative and denominator estimates; no terminal rounding remains. -/
def widerSlopeDenominator : Fin 6 → ℝ :=
  ![930982144 / 82354251,
    3442403584 / 169559355,
    2513265408 / 85588153,
    13223160064 / 343969563,
    20492495104 / 431174667,
    9782600448 / 172793257]

lemma widerSlopeDenominator_pos (i : Fin 6) :
    0 < widerSlopeDenominator i := by
  fin_cases i <;> norm_num [widerSlopeDenominator]

/-- Terminal rational identity for all six local slopes. -/
theorem wider_local_slope_rational (i : Fin 6) :
    1 / widerSlopeDenominator i ≤
      (3 / 2 : ℝ) * widerDerivativeLower ((i : ℕ) + 1) /
        ((44 * ((i : ℕ) + 1) : ℝ) / 7 + 21 / 40) ^ 2 := by
  fin_cases i <;>
    norm_num [widerSlopeDenominator, widerDerivativeLower, widerCosLower]

/-- Terminal rational verification outside each of the first five positive
root intervals. -/
theorem wider_positive_outside_rational (i : Fin 5) :
    widerCorrelationThreshold <
      (3 / 2 : ℝ) * widerDerivativeLower ((i : ℕ) + 1) * widerRadius /
        ((22 * (2 * ((i : ℕ) + 1) + 1) : ℝ) / 7) ^ 2 := by
  fin_cases i <;>
    norm_num [widerCorrelationThreshold, widerDerivativeLower,
      widerCosLower, widerRadius]

/-- Terminal rational verification on the first five zero-free intervals. -/
theorem wider_zero_free_rational (i : Fin 5) :
    widerCorrelationThreshold ≤
      (3 / 2 : ℝ) * ((592688 : ℝ) / 490449) /
        ((44 * ((i : ℕ) + 1) : ℝ) / 7) ^ 2 := by
  fin_cases i <;> norm_num [widerCorrelationThreshold]

theorem wider_last_zero_free_far_rational :
    widerCorrelationThreshold <
      (3 / 2 : ℝ) * (33 / 17) / ((264 / 7 : ℝ) ^ 2) := by
  norm_num [widerCorrelationThreshold]

theorem wider_last_zero_free_short_rational :
    widerCorrelationThreshold <
      (3 / 2 : ℝ) * widerDerivativeLower 6 * widerRadius /
        ((264 / 7 : ℝ) ^ 2) := by
  norm_num [widerCorrelationThreshold, widerDerivativeLower,
    widerCosLower, widerRadius]

end StrictImprovement
end Zeta23

end
