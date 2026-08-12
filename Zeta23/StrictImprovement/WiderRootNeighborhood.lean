/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WiderRootArithmetic

/-!
# Linear control in the first six endpoint-root neighborhoods

This module integrates the exact derivative bound from
WiderRootArithmetic.lean and converts it through the closed kernel formula.
The final interface is a six-case linear lower bound for the normalized
endpoint correlation.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open MeasureTheory Real Set intervalIntegral

namespace Zeta23
namespace StrictImprovement

def firstSixIndex (i : Fin 6) : ℕ := (i : ℕ) + 1

lemma firstSixIndex_pos (i : Fin 6) : 1 ≤ firstSixIndex i := by
  unfold firstSixIndex
  omega

noncomputable def firstSixOffset (i : Fin 6) : ℝ :=
  rootOffset (firstSixIndex i) (firstSixIndex_pos i)

noncomputable def firstSixRoot (i : Fin 6) : ℝ :=
  certifiedRoot (firstSixIndex i) (firstSixIndex_pos i)

lemma firstSixOffset_mem (i : Fin 6) :
    firstSixOffset i ∈ Set.Ioo (0 : ℝ) (2 / 5) := by
  exact rootOffset_mem (firstSixIndex i) (firstSixIndex_pos i)

lemma firstSixRoot_eq (i : Fin 6) :
    firstSixRoot i =
      2 * Real.pi * (firstSixIndex i : ℝ) + firstSixOffset i := by
  rfl

lemma firstSixOffset_numerator_zero (i : Fin 6) :
    offsetNumerator (firstSixIndex i) (firstSixOffset i) = 0 := by
  exact rootOffset_numerator_zero (firstSixIndex i) (firstSixIndex_pos i)

lemma widerDerivativeLower_pos (i : Fin 6) :
    0 < widerDerivativeLower (firstSixIndex i) := by
  have hn : (1 : ℝ) ≤ firstSixIndex i := by
    exact_mod_cast firstSixIndex_pos i
  unfold widerDerivativeLower widerCosLower
  nlinarith

/-- Integrating the enlarged-strip derivative estimate gives linear growth
away from any one of the first six roots. -/
theorem wider_neighborhood_numerator_linear
    (i : Fin 6) {e : ℝ}
    (hdist : |e - firstSixOffset i| ≤ widerRadius) :
    widerDerivativeLower (firstSixIndex i) *
        |e - firstSixOffset i| ≤
      |offsetNumerator (firstSixIndex i) e| := by
  let n := firstSixIndex i
  let eps := firstSixOffset i
  let L := widerDerivativeLower n
  have hn : 1 ≤ n := firstSixIndex_pos i
  have heps := firstSixOffset_mem i
  have hLpos : 0 < L := by
    simpa [n, L] using widerDerivativeLower_pos i
  have hrho : widerRadius = (1 : ℝ) / 8 := rfl
  have hderivInt : ∀ a b : ℝ,
      IntervalIntegrable (offsetNumeratorDerivative n) volume a b :=
    fun a b => Continuous.intervalIntegrable
      (by unfold offsetNumeratorDerivative; fun_prop) a b
  rcases le_total e eps with hleft | hright
  · have hdist' := abs_le.mp hdist
    have helow : -(1 : ℝ) / 8 ≤ e := by
      rw [hrho] at hdist'
      nlinarith [heps.1]
    have hupper : eps ≤ (21 : ℝ) / 40 := by
      dsimp [eps]
      nlinarith [heps.2]
    have hconstInt : IntervalIntegrable (fun _ : ℝ => L) volume e eps :=
      intervalIntegrable_const
    have hmono :
        (∫ _u in e..eps, L) ≤
          ∫ u in e..eps, offsetNumeratorDerivative n u := by
      refine intervalIntegral.integral_mono_on hleft hconstInt
        (hderivInt e eps) ?_
      intro u hu
      apply wider_offset_derivative_lower hn
      exact ⟨helow.trans hu.1, hu.2.trans hupper⟩
    have hint := integral_offsetNumeratorDerivative n e eps
    rw [intervalIntegral.integral_const, smul_eq_mul, hint] at hmono
    have hroot : offsetNumerator n eps = 0 := by
      simpa [n, eps] using firstSixOffset_numerator_zero i
    rw [hroot, zero_sub] at hmono
    have hneg : offsetNumerator n e ≤ 0 := by
      have hlen : 0 ≤ eps - e := sub_nonneg.mpr hleft
      nlinarith [mul_nonneg hLpos.le hlen]
    rw [abs_of_nonpos (sub_nonpos.mpr hleft), abs_of_nonpos hneg]
    dsimp [L, eps, n] at hmono ⊢
    nlinarith
  · have hdist' := abs_le.mp hdist
    have helow : -(1 : ℝ) / 8 ≤ eps := by
      dsimp [eps]
      nlinarith [heps.1]
    have hupper : e ≤ (21 : ℝ) / 40 := by
      rw [hrho] at hdist'
      nlinarith [heps.2]
    have hconstInt : IntervalIntegrable (fun _ : ℝ => L) volume eps e :=
      intervalIntegrable_const
    have hmono :
        (∫ _u in eps..e, L) ≤
          ∫ u in eps..e, offsetNumeratorDerivative n u := by
      refine intervalIntegral.integral_mono_on hright hconstInt
        (hderivInt eps e) ?_
      intro u hu
      apply wider_offset_derivative_lower hn
      exact ⟨helow.trans hu.1, hu.2.trans hupper⟩
    have hint := integral_offsetNumeratorDerivative n eps e
    rw [intervalIntegral.integral_const, smul_eq_mul, hint] at hmono
    have hroot : offsetNumerator n eps = 0 := by
      simpa [n, eps] using firstSixOffset_numerator_zero i
    rw [hroot, sub_zero] at hmono
    have hpos : 0 ≤ offsetNumerator n e := by
      have hlen : 0 ≤ e - eps := sub_nonneg.mpr hright
      nlinarith [mul_nonneg hLpos.le hlen]
    rw [abs_of_nonneg (sub_nonneg.mpr hright), abs_of_nonneg hpos]
    dsimp [L, eps, n] at hmono ⊢
    nlinarith

theorem wider_neighborhood_G_linear
    (i : Fin 6) {e : ℝ}
    (hdist : |e - firstSixOffset i| ≤ widerRadius) :
    widerDerivativeLower (firstSixIndex i) *
        |e - firstSixOffset i| ≤
      |endpointG
        (2 * Real.pi * (firstSixIndex i : ℝ) + e)| := by
  rw [endpointG_abs_eq_offsetNumerator_abs]
  exact wider_neighborhood_numerator_linear i hdist

/-- Final local interface: in the radius-1/8 neighborhood of each of the first
six roots, the normalized kernel grows at least linearly with the exact
rational denominator recorded in WiderRootArithmetic. -/
theorem wider_neighborhood_R_linear
    (i : Fin 6) {x : ℝ}
    (hdist : |x - firstSixRoot i| ≤ widerRadius) :
    |x - firstSixRoot i| / widerSlopeDenominator i ≤ |endpointR x| := by
  let n := firstSixIndex i
  let eps := firstSixOffset i
  let e := x - 2 * Real.pi * (n : ℝ)
  let A : ℝ := 44 * (n : ℝ) / 7 + 21 / 40
  let D : ℝ := A ^ 2
  have hn : 1 ≤ n := firstSixIndex_pos i
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have heps := firstSixOffset_mem i
  have hroot : firstSixRoot i = 2 * Real.pi * (n : ℝ) + eps := by
    simpa [n, eps] using firstSixRoot_eq i
  have heq : e - eps = x - firstSixRoot i := by
    dsimp [e]
    rw [hroot]
    ring
  have hdistE : |e - eps| ≤ widerRadius := by
    rw [heq]
    exact hdist
  have hdistE' := abs_le.mp hdistE
  have hrho : widerRadius = (1 : ℝ) / 8 := rfl
  have helow : -(1 : ℝ) / 8 ≤ e := by
    rw [hrho] at hdistE'
    nlinarith [heps.1]
  have heupper : e ≤ (21 : ℝ) / 40 := by
    rw [hrho] at hdistE'
    nlinarith [heps.2]
  have hxrepr : 2 * Real.pi * (n : ℝ) + e = x := by
    dsimp [e]
    ring
  have hpiUpper : Real.pi < (22 : ℝ) / 7 := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    linarith
  have hxpos : 0 < x := by
    rw [← hxrepr]
    have hpiMul : 3 * (n : ℝ) < Real.pi * (n : ℝ) :=
      mul_lt_mul_of_pos_right Real.pi_gt_three
        (lt_of_lt_of_le zero_lt_one hnReal)
    nlinarith
  have hxlarge : 2 < x := by
    rw [← hxrepr]
    have hpiMul : 3 * (n : ℝ) < Real.pi * (n : ℝ) :=
      mul_lt_mul_of_pos_right Real.pi_gt_three
        (lt_of_lt_of_le zero_lt_one hnReal)
    nlinarith
  have hxupper : x < A := by
    rw [← hxrepr]
    dsimp [A]
    have hpiMul :
        Real.pi * (n : ℝ) < (22 : ℝ) / 7 * (n : ℝ) :=
      mul_lt_mul_of_pos_right hpiUpper
        (lt_of_lt_of_le zero_lt_one hnReal)
    nlinarith
  have hApos : 0 < A := lt_trans hxpos hxupper
  have hsq : x ^ 2 < A ^ 2 := by
    have hprod : 0 < (A - x) * (A + x) :=
      mul_pos (sub_pos.mpr hxupper) (add_pos hApos hxpos)
    nlinarith
  have hdenpos : 0 < x ^ 2 - 2 := by nlinarith
  have hdenD : x ^ 2 - 2 < D := by
    dsimp [D]
    nlinarith
  have hxne : x ^ 2 ≠ 2 := by nlinarith
  have hG0 := wider_neighborhood_G_linear i hdistE
  rw [hxrepr] at hG0
  have hK := endpointK_abs_lower_of_G
    (x := x) (D := D) hxne hdenpos hdenD
  have hfactor : 0 ≤ ((3 : ℝ) / 2) / D := by
    dsimp [D]
    positivity
  have hslope : (widerSlopeDenominator i)⁻¹ ≤
      (3 / 2 : ℝ) * widerDerivativeLower n / A ^ 2 := by
    simpa [n, A, firstSixIndex, one_div] using wider_local_slope_rational i
  rw [div_eq_mul_inv]
  calc
    |x - firstSixRoot i| * (widerSlopeDenominator i)⁻¹
        = (widerSlopeDenominator i)⁻¹ * |x - firstSixRoot i| := by ring
    _ ≤ ((3 / 2 : ℝ) * widerDerivativeLower n / A ^ 2) *
            |x - firstSixRoot i| :=
          mul_le_mul_of_nonneg_right hslope (abs_nonneg _)
    _ = ((3 : ℝ) / 2) / D *
          (widerDerivativeLower n * |e - eps|) := by
          rw [heq]
          dsimp [D]
          ring
    _ ≤ ((3 : ℝ) / 2) / D * |endpointG x| :=
          mul_le_mul_of_nonneg_left hG0 hfactor
    _ ≤ |endpointK x| := hK
    _ ≤ |endpointR x| := endpointK_abs_le_endpointR_abs x

end StrictImprovement
end Zeta23

end
