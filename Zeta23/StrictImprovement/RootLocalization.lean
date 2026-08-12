/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.KernelRoots

/-!
# Root-adjacent derivative certificate

This module formalizes the differential core of the `2/1757` localization
argument.  It proves global monotonicity of each positive-interval numerator
and the exact rational derivative lower bound on the certified radius around
the first three offsets.

This is a source draft until checked by the pinned Lean toolchain recorded in
`LEAN_FORMALIZATION_PLAN.md`.
-/

noncomputable section

open MeasureTheory Real Set intervalIntegral

namespace Zeta23
namespace StrictImprovement

/-- Exact derivative expression for the offset numerator. -/
def offsetNumeratorDerivative (n : ℕ) (e : ℝ) : ℝ :=
  (1 + endpointKappa / 2) * Real.sin (e / 2)
    + (2 * Real.pi * (n : ℝ) + e) / 2 * Real.cos (e / 2)

theorem hasDerivAt_offsetNumerator (n : ℕ) (e : ℝ) :
    HasDerivAt (offsetNumerator n) (offsetNumeratorDerivative n e) e := by
  have harg := (hasDerivAt_id e).div_const 2
  have hsin := (Real.hasDerivAt_sin (e / 2)).comp e harg
  have hcos := (Real.hasDerivAt_cos (e / 2)).comp e harg
  have hcoef : HasDerivAt
      (fun y : ℝ => 2 * Real.pi * (n : ℝ) + y) 1 e := by
    simpa only [id_eq] using
      (hasDerivAt_id e).const_add (2 * Real.pi * (n : ℝ))
  unfold offsetNumerator offsetNumeratorDerivative
  have h := (hcoef.mul hsin).sub (hcos.const_mul endpointKappa)
  simp only [Function.comp_apply, id_eq] at h
  exact h.congr_deriv (by ring)

/-- On the whole positive zero interval the continuous numerator is strictly
increasing. -/
theorem offsetNumerator_strictMonoOn (n : ℕ) (hn : 1 ≤ n) :
    StrictMonoOn (offsetNumerator n) (Set.Icc 0 Real.pi) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) Real.pi)
    (continuous_offsetNumerator n).continuousOn ?_
  intro e he
  have heIoo : e ∈ Set.Ioo (0 : ℝ) Real.pi := by
    simpa [interior_Icc, Real.pi_pos.ne'] using he
  rw [(hasDerivAt_offsetNumerator n e).deriv]
  unfold offsetNumeratorDerivative
  have hsin : 0 < Real.sin (e / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact div_pos heIoo.1 (by norm_num)
    · nlinarith [heIoo.2, Real.pi_pos]
  have hcos : 0 < Real.cos (e / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [heIoo.1, Real.pi_pos]
    · nlinarith [heIoo.2, Real.pi_pos]
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnreal
  have hcoef : 0 < (2 * Real.pi * (n : ℝ) + e) / 2 := by
    have hmain : 0 < 2 * Real.pi * (n : ℝ) := by positivity
    nlinarith [heIoo.1]
  have hone : 0 < 1 + endpointKappa / 2 := by
    nlinarith [endpointKappa_pos]
  positivity

/-- A point in the certified radius around a first-three offset stays in the
small positive trigonometric range used by the rational cosine bound. -/
lemma root_neighborhood_bounds
    {n : ℕ} {hn : 1 ≤ n}
    (hlow : (1 : ℝ) / 8 < rootOffset n hn)
    {e : ℝ} (hdist : |e - rootOffset n hn| ≤ localizationRadius) :
    0 < e ∧ e < (53 : ℝ) / 120 := by
  have hdist' := abs_le.mp hdist
  have hr := localizationRadius_lt_one_div_twenty_four
  have hu := (rootOffset_mem n hn).2
  constructor <;> nlinarith

/-- Exact local cosine lower bound on every certified root neighborhood. -/
lemma local_cos_lower
    {n : ℕ} {hn : 1 ≤ n}
    (hlow : (1 : ℝ) / 8 < rootOffset n hn)
    {e : ℝ} (hdist : |e - rootOffset n hn| ≤ localizationRadius) :
    (112391 : ℝ) / 115200 < Real.cos (e / 2) := by
  have heb := root_neighborhood_bounds hlow hdist
  have htpos : 0 < e / 2 := by linarith
  have htlt : e / 2 < (53 : ℝ) / 240 := by linarith
  have hsum : 0 < (53 : ℝ) / 240 + e / 2 := by positivity
  have hprod :
      0 < ((53 : ℝ) / 240 - e / 2) * ((53 : ℝ) / 240 + e / 2) :=
    mul_pos (sub_pos.mpr htlt) hsum
  have hsq : (e / 2) ^ 2 < ((53 : ℝ) / 240) ^ 2 := by
    nlinarith
  have hcos := Real.one_sub_sq_div_two_lt_cos (ne_of_gt htpos)
  rw [← local_cos_rational]
  nlinarith

/-- Root-adjacent derivative lower bound with the exact rational constant
used by the three terminal interval fractions. -/
theorem root_neighborhood_derivative_lower
    {n : ℕ} {hn : 1 ≤ n}
    (hlow : (1 : ℝ) / 8 < rootOffset n hn)
    {e : ℝ} (hdist : |e - rootOffset n hn| ≤ localizationRadius) :
    3 * (n : ℝ) * ((112391 : ℝ) / 115200)
      ≤ offsetNumeratorDerivative n e := by
  have heb := root_neighborhood_bounds hlow hdist
  have hcos := local_cos_lower hlow hdist
  have hsin : 0 ≤ Real.sin (e / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · linarith [Real.pi_gt_three]
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnreal
  have hcoef :
      3 * (n : ℝ) < (2 * Real.pi * (n : ℝ) + e) / 2 := by
    have hpi_mul : 3 * (n : ℝ) < Real.pi * (n : ℝ) :=
      mul_lt_mul_of_pos_right Real.pi_gt_three hnpos
    nlinarith
  have hc0pos : 0 < (112391 : ℝ) / 115200 := by norm_num
  have hcoefpos : 0 < (2 * Real.pi * (n : ℝ) + e) / 2 :=
    lt_trans (mul_pos (by norm_num) hnpos) hcoef
  have hsecond :
      3 * (n : ℝ) * ((112391 : ℝ) / 115200)
        < (2 * Real.pi * (n : ℝ) + e) / 2 * Real.cos (e / 2) := by
    calc
      3 * (n : ℝ) * ((112391 : ℝ) / 115200)
          < (2 * Real.pi * (n : ℝ) + e) / 2 *
              ((112391 : ℝ) / 115200) :=
            mul_lt_mul_of_pos_right hcoef hc0pos
      _ < (2 * Real.pi * (n : ℝ) + e) / 2 * Real.cos (e / 2) :=
            mul_lt_mul_of_pos_left hcos hcoefpos
  have hfirst :
      0 ≤ (1 + endpointKappa / 2) * Real.sin (e / 2) := by
    exact mul_nonneg (by nlinarith [endpointKappa_pos]) hsin
  unfold offsetNumeratorDerivative
  linarith

/-- Fundamental-theorem identity for the offset numerator. -/
lemma integral_offsetNumeratorDerivative (n : ℕ) (a b : ℝ) :
    (∫ e in a..b, offsetNumeratorDerivative n e) =
      offsetNumerator n b - offsetNumerator n a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun e _ => hasDerivAt_offsetNumerator n e)
    (Continuous.intervalIntegrable
      (by unfold offsetNumeratorDerivative; fun_prop) a b)]

/-- Quantitative numerator lower bound at the right edge of a certified root
neighborhood. -/
lemma right_radius_numerator_lower
    {n : ℕ} {hn : 1 ≤ n}
    (hlow : (1 : ℝ) / 8 < rootOffset n hn) :
    3 * (n : ℝ) * ((112391 : ℝ) / 115200) * localizationRadius
      ≤ offsetNumerator n (rootOffset n hn + localizationRadius) := by
  have hrpos := localizationRadius_pos
  have hab : rootOffset n hn ≤ rootOffset n hn + localizationRadius := by
    linarith
  have hconst_int : IntervalIntegrable
      (fun _ : ℝ => 3 * (n : ℝ) * ((112391 : ℝ) / 115200))
      volume (rootOffset n hn) (rootOffset n hn + localizationRadius) :=
    intervalIntegrable_const
  have hderiv_int : IntervalIntegrable (offsetNumeratorDerivative n)
      volume (rootOffset n hn) (rootOffset n hn + localizationRadius) :=
    Continuous.intervalIntegrable
      (by unfold offsetNumeratorDerivative; fun_prop) _ _
  have hmono :
      (∫ _e in rootOffset n hn..(rootOffset n hn + localizationRadius),
        3 * (n : ℝ) * ((112391 : ℝ) / 115200))
        ≤ ∫ e in rootOffset n hn..(rootOffset n hn + localizationRadius),
          offsetNumeratorDerivative n e := by
    refine intervalIntegral.integral_mono_on hab hconst_int hderiv_int ?_
    intro e he
    apply root_neighborhood_derivative_lower hlow
    rw [abs_of_nonneg (by linarith [he.1] : 0 ≤ e - rootOffset n hn)]
    linarith [he.2]
  have hroot := rootOffset_numerator_zero n hn
  have hint := integral_offsetNumeratorDerivative n
    (rootOffset n hn) (rootOffset n hn + localizationRadius)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  rw [hint, hroot, sub_zero] at hmono
  nlinarith

/-- Quantitative numerator lower bound at the left edge of a certified root
neighborhood. -/
lemma left_radius_numerator_lower
    {n : ℕ} {hn : 1 ≤ n}
    (hlow : (1 : ℝ) / 8 < rootOffset n hn) :
    3 * (n : ℝ) * ((112391 : ℝ) / 115200) * localizationRadius
      ≤ -offsetNumerator n (rootOffset n hn - localizationRadius) := by
  have hrpos := localizationRadius_pos
  have hab : rootOffset n hn - localizationRadius ≤ rootOffset n hn := by
    linarith
  have hconst_int : IntervalIntegrable
      (fun _ : ℝ => 3 * (n : ℝ) * ((112391 : ℝ) / 115200))
      volume (rootOffset n hn - localizationRadius) (rootOffset n hn) :=
    intervalIntegrable_const
  have hderiv_int : IntervalIntegrable (offsetNumeratorDerivative n)
      volume (rootOffset n hn - localizationRadius) (rootOffset n hn) :=
    Continuous.intervalIntegrable
      (by unfold offsetNumeratorDerivative; fun_prop) _ _
  have hmono :
      (∫ _e in (rootOffset n hn - localizationRadius)..rootOffset n hn,
        3 * (n : ℝ) * ((112391 : ℝ) / 115200))
        ≤ ∫ e in (rootOffset n hn - localizationRadius)..rootOffset n hn,
          offsetNumeratorDerivative n e := by
    refine intervalIntegral.integral_mono_on hab hconst_int hderiv_int ?_
    intro e he
    apply root_neighborhood_derivative_lower hlow
    rw [abs_of_nonpos (by linarith [he.2] : e - rootOffset n hn ≤ 0)]
    linarith [he.1]
  have hroot := rootOffset_numerator_zero n hn
  have hint := integral_offsetNumeratorDerivative n
    (rootOffset n hn - localizationRadius) (rootOffset n hn)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  rw [hint, hroot, zero_sub] at hmono
  nlinarith

/-- Outside the certified radius, anywhere in the full positive zero
interval, monotonicity propagates the boundary lower bound. -/
theorem outside_radius_numerator_lower
    {n : ℕ} {hn : 1 ≤ n}
    (hlow : (1 : ℝ) / 8 < rootOffset n hn)
    {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) Real.pi)
    (hfar : localizationRadius ≤ |e - rootOffset n hn|) :
    3 * (n : ℝ) * ((112391 : ℝ) / 115200) * localizationRadius
      ≤ |offsetNumerator n e| := by
  let c : ℝ := 3 * (n : ℝ) * ((112391 : ℝ) / 115200) * localizationRadius
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnreal
  have hrpos := localizationRadius_pos
  have hcpos : 0 < c := by
    dsimp [c]
    exact mul_pos (mul_pos (mul_pos (by norm_num) hnpos) (by norm_num)) hrpos
  have hrsmall := localizationRadius_lt_one_div_twenty_four
  have hrootmem := rootOffset_mem n hn
  have hleftmem :
      rootOffset n hn - localizationRadius ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · nlinarith [hlow, hrsmall]
    · nlinarith [hrootmem.2, hrpos, Real.pi_gt_three]
  have hrightmem :
      rootOffset n hn + localizationRadius ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · nlinarith [hrootmem.1, hrpos]
    · nlinarith [hrootmem.2, hrsmall, Real.pi_gt_three]
  have hleft := left_radius_numerator_lower hlow
  have hright := right_radius_numerator_lower hlow
  have hmono := (offsetNumerator_strictMonoOn n hn).monotoneOn
  rcases le_total e (rootOffset n hn) with hel | her
  · have hfar' := hfar
    rw [abs_of_nonpos (sub_nonpos.mpr hel)] at hfar'
    have heleft : e ≤ rootOffset n hn - localizationRadius := by
      nlinarith
    have horder := hmono he hleftmem heleft
    have hneg : offsetNumerator n e < 0 := by
      dsimp [c] at hcpos ⊢
      nlinarith
    rw [abs_of_neg hneg]
    nlinarith
  · have hfar' := hfar
    rw [abs_of_nonneg (sub_nonneg.mpr her)] at hfar'
    have heright : rootOffset n hn + localizationRadius ≤ e := by
      nlinarith
    have horder := hmono hrightmem he heright
    have hpos : 0 < offsetNumerator n e := by
      dsimp [c] at hcpos ⊢
      nlinarith
    rw [abs_of_pos hpos]
    nlinarith

/-- Translating by `2*pi*n` changes the scalar numerator only by the unit
factor `cos(n*pi)`, so its absolute value is unchanged. -/
lemma endpointG_abs_eq_offsetNumerator_abs (n : ℕ) (e : ℝ) :
    |endpointG (2 * Real.pi * (n : ℝ) + e)| = |offsetNumerator n e| := by
  have harg :
      (2 * Real.pi * (n : ℝ) + e) / 2 =
        (n : ℝ) * Real.pi + e / 2 := by ring
  have hsin_n : Real.sin ((n : ℝ) * Real.pi) = 0 := by
    simpa using Real.sin_int_mul_pi (n : ℤ)
  have hcos_sq : Real.cos ((n : ℝ) * Real.pi) ^ 2 = 1 := by
    have hpyth := Real.sin_sq_add_cos_sq ((n : ℝ) * Real.pi)
    rw [hsin_n, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at hpyth
    exact hpyth
  have hcos_abs : |Real.cos ((n : ℝ) * Real.pi)| = 1 := by
    have habs_sq : |Real.cos ((n : ℝ) * Real.pi)| ^ 2 = 1 := by
      rw [sq_abs, hcos_sq]
    nlinarith [abs_nonneg (Real.cos ((n : ℝ) * Real.pi))]
  have hid :
      endpointG (2 * Real.pi * (n : ℝ) + e) =
        Real.cos ((n : ℝ) * Real.pi) * offsetNumerator n e := by
    unfold endpointG offsetNumerator
    rw [harg, Real.sin_add, Real.cos_add, hsin_n]
    ring
  rw [hid, abs_mul, hcos_abs, one_mul]

/-- Original-coordinate form of the outside-radius numerator certificate. -/
theorem positive_interval_outside_radius_G_lower
    {n : ℕ} {hn : 1 ≤ n}
    (hlow : (1 : ℝ) / 8 < rootOffset n hn)
    {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) Real.pi)
    (hfar : localizationRadius ≤ |e - rootOffset n hn|) :
    3 * (n : ℝ) * ((112391 : ℝ) / 115200) * localizationRadius
      ≤ |endpointG (2 * Real.pi * (n : ℝ) + e)| := by
  rw [endpointG_abs_eq_offsetNumerator_abs]
  exact outside_radius_numerator_lower hlow he hfar

/-- The rational closed-form prefactor converts any scalar-numerator bound
into a normalized-kernel bound. -/
lemma endpointK_abs_lower_of_G
    {x D : ℝ} (hx : x ^ 2 ≠ 2)
    (hdenpos : 0 < x ^ 2 - 2) (hdenD : x ^ 2 - 2 < D) :
    ((3 : ℝ) / 2) / D * |endpointG x| ≤ |endpointK x| := by
  have hDpos : 0 < D := lt_trans hdenpos hdenD
  have hnum : (3 : ℝ) / 2 ≤ 2 * Real.cos (ThmD.theta 1) := by
    nlinarith [three_fourths_le_endpointCos]
  have hfactorpos :
      0 < 2 * Real.cos (ThmD.theta 1) / (x ^ 2 - 2) := by
    have hcos := ThmD.cos_theta_pos (lam := (1 : ℝ)) (by norm_num) (by norm_num)
    positivity
  have hfactor :
      ((3 : ℝ) / 2) / D
        ≤ 2 * Real.cos (ThmD.theta 1) / (x ^ 2 - 2) := by
    calc
      ((3 : ℝ) / 2) / D ≤ ((3 : ℝ) / 2) / (x ^ 2 - 2) :=
        div_le_div_of_nonneg_left (by norm_num) hdenpos hdenD.le
      _ ≤ 2 * Real.cos (ThmD.theta 1) / (x ^ 2 - 2) :=
        div_le_div_of_nonneg_right hnum hdenpos.le
  rw [endpointK_closed_kappa hx]
  change ((3 : ℝ) / 2) / D * |endpointG x| ≤
    |(2 * Real.cos (ThmD.theta 1) / (x ^ 2 - 2)) * endpointG x|
  rw [abs_mul, abs_of_pos hfactorpos]
  exact mul_le_mul_of_nonneg_right hfactor (abs_nonneg (endpointG x))

/-- Denominator comparison on a positive zero interval. -/
lemma positive_interval_denominator_bounds
    (n : ℕ) (hn : 1 ≤ n) {e D : ℝ}
    (he : e ∈ Set.Icc (0 : ℝ) Real.pi)
    (hD : (((2 * n + 1 : ℕ) : ℝ) * Real.pi) ^ 2 - 2 < D) :
    let x := 2 * Real.pi * (n : ℝ) + e
    0 < x ^ 2 - 2 ∧ x ^ 2 - 2 < D := by
  dsimp
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hxpos : 0 < 2 * Real.pi * (n : ℝ) + e := by
    nlinarith [he.1, Real.pi_pos]
  have hxlarge : 6 < 2 * Real.pi * (n : ℝ) + e := by
    nlinarith [he.1, Real.pi_gt_three]
  have hupper :
      2 * Real.pi * (n : ℝ) + e
        ≤ (((2 * n + 1 : ℕ) : ℝ) * Real.pi) := by
    push_cast
    nlinarith [he.2, Real.pi_pos]
  have huppos : 0 < (((2 * n + 1 : ℕ) : ℝ) * Real.pi) := by
    positivity
  have hprod :
      0 ≤ ((((2 * n + 1 : ℕ) : ℝ) * Real.pi) -
          (2 * Real.pi * (n : ℝ) + e)) *
        ((((2 * n + 1 : ℕ) : ℝ) * Real.pi) +
          (2 * Real.pi * (n : ℝ) + e)) :=
    mul_nonneg (sub_nonneg.mpr hupper) (add_nonneg huppos.le hxpos.le)
  constructor <;> nlinarith

/-- Generic positive-interval kernel lower bound outside the root radius. -/
theorem positive_interval_outside_radius_K_lower
    {n : ℕ} {hn : 1 ≤ n}
    (hlow : (1 : ℝ) / 8 < rootOffset n hn)
    {e D : ℝ} (he : e ∈ Set.Icc (0 : ℝ) Real.pi)
    (hfar : localizationRadius ≤ |e - rootOffset n hn|)
    (hD : (((2 * n + 1 : ℕ) : ℝ) * Real.pi) ^ 2 - 2 < D) :
    ((3 : ℝ) / 2) / D *
        (3 * (n : ℝ) * ((112391 : ℝ) / 115200) * localizationRadius)
      ≤ |endpointK (2 * Real.pi * (n : ℝ) + e)| := by
  let x : ℝ := 2 * Real.pi * (n : ℝ) + e
  have hden := positive_interval_denominator_bounds n hn he hD
  have hx : x ^ 2 ≠ 2 := by
    dsimp [x] at hden ⊢
    nlinarith
  have hG := positive_interval_outside_radius_G_lower hlow he hfar
  have hK := endpointK_abs_lower_of_G (x := x) (D := D) hx hden.1 hden.2
  have hfactor_nonneg : 0 ≤ ((3 : ℝ) / 2) / D := by
    have hDpos := lt_trans hden.1 hden.2
    positivity
  calc
    ((3 : ℝ) / 2) / D *
        (3 * (n : ℝ) * ((112391 : ℝ) / 115200) * localizationRadius)
        ≤ ((3 : ℝ) / 2) / D * |endpointG x| :=
          mul_le_mul_of_nonneg_left hG hfactor_nonneg
    _ ≤ |endpointK x| := hK

theorem first_positive_interval_K_lower
    {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) Real.pi)
    (hfar : localizationRadius ≤ |e - epsilonOne|) :
    (561955 : ℝ) / 267275136 ≤ |endpointK (2 * Real.pi + e)| := by
  have h := positive_interval_outside_radius_K_lower
    (n := 1) (hn := by norm_num)
    (by simpa [epsilonOne] using
      (lt_trans one_eighth_lt_epsilonThree
        (epsilonThree_lt_epsilonTwo.trans epsilonTwo_lt_epsilonOne)))
    he (by simpa [epsilonOne] using hfar)
    (D := 87) (by simpa using first_positive_interval_denominator)
  norm_num [localizationRadius] at h ⊢
  convert h using 1 <;> ring

theorem second_positive_interval_K_lower
    {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) Real.pi)
    (hfar : localizationRadius ≤ |e - epsilonTwo|) :
    (112391 : ℝ) / 75267136 ≤ |endpointK (4 * Real.pi + e)| := by
  have h := positive_interval_outside_radius_K_lower
    (n := 2) (hn := by norm_num)
    (by simpa [epsilonTwo] using
      (lt_trans one_eighth_lt_epsilonThree epsilonThree_lt_epsilonTwo))
    he (by simpa [epsilonTwo] using hfar)
    (D := 245) (by simpa using second_positive_interval_denominator)
  norm_num [localizationRadius] at h ⊢
  convert h using 1 <;> ring

theorem third_positive_interval_K_lower
    {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) Real.pi)
    (hfar : localizationRadius ≤ |e - epsilonThree|) :
    (1685865 : ℝ) / 1480765696 ≤ |endpointK (6 * Real.pi + e)| := by
  have h := positive_interval_outside_radius_K_lower
    (n := 3) (hn := by norm_num)
    (by simpa [epsilonThree] using one_eighth_lt_epsilonThree)
    he (by simpa [epsilonThree] using hfar)
    (D := 482) (by simpa using third_positive_interval_denominator)
  norm_num [localizationRadius] at h ⊢
  convert h using 1 <;> ring

/-! ## The initial zero-free interval -/

/-- Evenness of the kernel integrand reduces the defining integral to the
nonnegative half interval. -/
lemma endpointK_eq_twice_half_integral (x : ℝ) :
    endpointK x = 2 *
      (∫ s in (0 : ℝ)..(1 / 2),
        ThmD.vStar 1 s * Real.cos (x * s)) := by
  have hcont : Continuous
      (fun s : ℝ => ThmD.vStar 1 s * Real.cos (x * s)) := by
    unfold ThmD.vStar
    fun_prop
  have hii : ∀ a b : ℝ, IntervalIntegrable
      (fun s : ℝ => ThmD.vStar 1 s * Real.cos (x * s)) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hsplit :
      (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
        ThmD.vStar 1 s * Real.cos (x * s)) =
      (∫ s in (-(1 : ℝ) / 2)..0,
        ThmD.vStar 1 s * Real.cos (x * s)) +
      (∫ s in (0 : ℝ)..(1 / 2),
        ThmD.vStar 1 s * Real.cos (x * s)) :=
    (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
  have hleft :
      (∫ s in (-(1 : ℝ) / 2)..0,
        ThmD.vStar 1 s * Real.cos (x * s)) =
      ∫ s in (0 : ℝ)..(1 / 2),
        ThmD.vStar 1 s * Real.cos (x * s) := by
    have hcomp := intervalIntegral.integral_comp_neg
      (a := (0 : ℝ)) (b := (1 : ℝ) / 2)
      (fun s : ℝ => ThmD.vStar 1 s * Real.cos (x * s))
    have heven :
        (∫ s in (0 : ℝ)..(1 / 2),
          ThmD.vStar 1 (-s) * Real.cos (x * (-s))) =
        ∫ s in (0 : ℝ)..(1 / 2),
          ThmD.vStar 1 s * Real.cos (x * s) := by
      apply intervalIntegral.integral_congr
      intro s _
      unfold ThmD.vStar
      simp only [mul_neg, Real.cos_neg]
    rw [← heven, hcomp]
    norm_num
  unfold endpointK
  rw [hsplit, hleft]
  ring

/-- Exact lower bound on the initial interval `[0,pi]`. -/
theorem endpointK_initial_interval_lower
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
    (165 : ℝ) / 512 ≤ endpointK x := by
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hpi_sq : Real.pi ^ 2 < (10 : ℝ) := by
    have h := pi_sq_lt_rational
    norm_num at h ⊢
    nlinarith
  have hpoint_quarter : ∀ s ∈ Set.Icc (0 : ℝ) (1 / 4),
      (165 : ℝ) / 256 ≤ ThmD.vStar 1 s * Real.cos (x * s) := by
    intro s hs
    have hsprod : 0 ≤ s * ((1 : ℝ) / 4 - s) :=
      mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
    have hs_sq : s ^ 2 ≤ (1 : ℝ) / 16 := by nlinarith
    have hsqrt_arg_sq : (Real.sqrt 2 * s) ^ 2 ≤ (1 : ℝ) / 8 := by
      rw [mul_pow, hsqrt_sq]
      nlinarith
    have hcos1base := Real.one_sub_sq_div_two_le_cos
      (x := Real.sqrt 2 * s)
    have hcos1 : (15 : ℝ) / 16 ≤ Real.cos (Real.sqrt 2 * s) := by
      nlinarith
    have hxs : x * s ≤ Real.pi / 4 := by
      calc
        x * s ≤ Real.pi * s := mul_le_mul_of_nonneg_right hx.2 hs.1
        _ ≤ Real.pi * ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hs.2 Real.pi_pos.le
        _ = Real.pi / 4 := by ring
    have hxs0 : 0 ≤ x * s := mul_nonneg hx.1 hs.1
    have hsqprod :
        0 ≤ (Real.pi / 4 - x * s) * (Real.pi / 4 + x * s) :=
      mul_nonneg (sub_nonneg.mpr hxs) (add_nonneg (by positivity) hxs0)
    have hxs_sq : (x * s) ^ 2 < (5 : ℝ) / 8 := by
      nlinarith
    have hcos2base := Real.one_sub_sq_div_two_le_cos (x := x * s)
    have hcos2 : (11 : ℝ) / 16 ≤ Real.cos (x * s) := by
      nlinarith
    have hcos1' :
        (15 : ℝ) / 16 ≤ Real.cos (Real.sqrt 2 * 1 * s) := by
      simpa only [mul_one] using hcos1
    unfold ThmD.vStar
    calc
      (165 : ℝ) / 256 = ((15 : ℝ) / 16) * ((11 : ℝ) / 16) := by norm_num
      _ ≤ Real.cos (Real.sqrt 2 * 1 * s) * Real.cos (x * s) := by
        apply mul_le_mul hcos1' hcos2 (by norm_num)
        nlinarith
  have hpoint_tail : ∀ s ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2),
      0 ≤ ThmD.vStar 1 s * Real.cos (x * s) := by
    intro s hs
    have hvs : 0 ≤ ThmD.vStar 1 s := by
      unfold ThmD.vStar
      apply Real.cos_nonneg_of_mem_Icc
      have harg0 : 0 ≤ Real.sqrt 2 * 1 * s := by
        have hs0 : 0 ≤ s := le_trans (by norm_num) hs.1
        exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (by norm_num)) hs0
      have hsqrt_le_two : Real.sqrt 2 ≤ 2 := by
        nlinarith [hsqrt_sq, Real.sqrt_nonneg 2]
      have harg_le_one : Real.sqrt 2 * 1 * s ≤ 1 := by
        calc
          Real.sqrt 2 * 1 * s ≤ 2 * s := by
            apply mul_le_mul_of_nonneg_right
            · nlinarith
            · linarith [hs.1]
          _ ≤ 1 := by nlinarith [hs.2]
      constructor
      · nlinarith [Real.pi_gt_three]
      · nlinarith [Real.pi_gt_three]
    have hxc : 0 ≤ Real.cos (x * s) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · have hxs0 : 0 ≤ x * s := mul_nonneg hx.1 (by linarith [hs.1])
        nlinarith [hxs0, Real.pi_pos]
      · have hxs : x * s ≤ Real.pi / 2 := by
          exact (mul_le_mul hx.2 hs.2 (by linarith [hs.1]) Real.pi_pos.le).trans_eq
            (by ring)
        exact hxs
    exact mul_nonneg hvs hxc
  have hcont : Continuous
      (fun s : ℝ => ThmD.vStar 1 s * Real.cos (x * s)) := by
    unfold ThmD.vStar
    fun_prop
  have hsplit :
      (∫ s in (0 : ℝ)..(1 / 2), ThmD.vStar 1 s * Real.cos (x * s)) =
      (∫ s in (0 : ℝ)..(1 / 4), ThmD.vStar 1 s * Real.cos (x * s)) +
      (∫ s in (1 / 4 : ℝ)..(1 / 2), ThmD.vStar 1 s * Real.cos (x * s)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hquarter :
      (165 : ℝ) / 1024 ≤
        ∫ s in (0 : ℝ)..(1 / 4), ThmD.vStar 1 s * Real.cos (x * s) := by
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 4)
      intervalIntegrable_const (hcont.intervalIntegrable _ _) hpoint_quarter
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    norm_num at hmono ⊢
    exact hmono
  have htail : 0 ≤
      ∫ s in (1 / 4 : ℝ)..(1 / 2), ThmD.vStar 1 s * Real.cos (x * s) :=
    intervalIntegral.integral_nonneg (by norm_num) hpoint_tail
  rw [endpointK_eq_twice_half_integral, hsplit]
  nlinarith

/-! ## The four alternating zero-free intervals -/

/-- On an alternating interval `[(2m-1)pi,2m*pi]`, the half-angle sine and
cosine have opposite signs after removing the integral multiple of `pi`.
The resulting scalar numerator therefore has absolute value at least `6/5`.
This statement is uniform in `m`; the later denominator estimate only needs
`m <= 4`. -/
theorem zero_free_interval_G_lower
    {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x ∈ Set.Icc
      ((2 * (m : ℝ) - 1) * Real.pi)
      ((2 * (m : ℝ)) * Real.pi)) :
    (6 : ℝ) / 5 ≤ |endpointG x| := by
  let t : ℝ := x / 2 - ((m : ℝ) - 1) * Real.pi
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmcast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm]
    norm_num
  have ht : t ∈ Set.Icc (Real.pi / 2) Real.pi := by
    dsimp [t]
    constructor
    · nlinarith [hx.1, Real.pi_pos]
    · nlinarith [hx.2, Real.pi_pos]
  have hsin : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (le_trans (by positivity) ht.1) ht.2
  have hcos : Real.cos t ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le ht.1
      (by nlinarith [ht.2, Real.pi_pos])
  have htrig_abs :
      |Real.sin t| ^ 2 + |Real.cos t| ^ 2 = 1 := by
    simpa only [sq_abs] using Real.sin_sq_add_cos_sq t
  have habs_sum : 1 ≤ |Real.sin t| + |Real.cos t| := by
    have hs0 := abs_nonneg (Real.sin t)
    have hc0 := abs_nonneg (Real.cos t)
    have hcross : 0 ≤ |Real.sin t| * |Real.cos t| := mul_nonneg hs0 hc0
    nlinarith
  have hxlarge : (6 : ℝ) / 5 ≤ x := by
    have hfactor : 1 ≤ 2 * (m : ℝ) - 1 := by nlinarith
    have hpi_le : Real.pi ≤ (2 * (m : ℝ) - 1) * Real.pi := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hfactor Real.pi_pos.le
    nlinarith [hx.1, hpi_le, Real.pi_gt_three]
  have hklarge : (6 : ℝ) / 5 ≤ endpointKappa :=
    six_fifths_lt_endpointKappa.le
  have hweighted :
      (6 : ℝ) / 5 ≤
        x * |Real.sin t| + endpointKappa * |Real.cos t| := by
    calc
      (6 : ℝ) / 5 ≤
          (6 : ℝ) / 5 * (|Real.sin t| + |Real.cos t|) := by
            nlinarith
      _ = (6 : ℝ) / 5 * |Real.sin t| +
          (6 : ℝ) / 5 * |Real.cos t| := by ring
      _ ≤ x * |Real.sin t| + endpointKappa * |Real.cos t| :=
        add_le_add
          (mul_le_mul_of_nonneg_right hxlarge (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hklarge (abs_nonneg _))
  have harg :
      x / 2 = t + (((m - 1 : ℕ) : ℝ)) * Real.pi := by
    dsimp [t]
    rw [hmcast]
    ring
  have hsin_shift :
      Real.sin (x / 2) =
        (-1 : ℝ) ^ (m - 1) * Real.sin t := by
    rw [harg]
    exact Real.sin_add_nat_mul_pi t (m - 1)
  have hcos_shift :
      Real.cos (x / 2) =
        (-1 : ℝ) ^ (m - 1) * Real.cos t := by
    rw [harg]
    exact Real.cos_add_nat_mul_pi t (m - 1)
  have hfactor_abs : |(-1 : ℝ) ^ (m - 1)| = 1 := by simp
  have hGfactor :
      endpointG x = (-1 : ℝ) ^ (m - 1) *
        (x * Real.sin t - endpointKappa * Real.cos t) := by
    unfold endpointG
    rw [hsin_shift, hcos_shift]
    ring
  have hinner_nonneg :
      0 ≤ x * Real.sin t - endpointKappa * Real.cos t := by
    have hx0 : 0 ≤ x := le_trans (by norm_num) hxlarge
    have hk0 : 0 ≤ endpointKappa := endpointKappa_pos.le
    nlinarith [mul_nonneg hx0 hsin, mul_nonpos_of_nonneg_of_nonpos hk0 hcos]
  have hweighted' := hweighted
  rw [abs_of_nonneg hsin, abs_of_nonpos hcos] at hweighted'
  rw [hGfactor, abs_mul, hfactor_abs, one_mul,
    abs_of_nonneg hinner_nonneg]
  nlinarith

/-- A common denominator bound converts the scalar estimate on all four
alternating intervals below `8*pi` into the exact `9/3155` kernel bound. -/
lemma endpointK_lower_of_global_gap_bounds
    {x : ℝ} (hxlow : Real.pi ≤ x) (hxhigh : x ≤ 8 * Real.pi)
    (hG : (6 : ℝ) / 5 ≤ |endpointG x|) :
    (9 : ℝ) / 3155 ≤ |endpointK x| := by
  have hxpos : 0 < x := lt_of_lt_of_le Real.pi_pos hxlow
  have hxlarge : 3 < x := lt_of_lt_of_le Real.pi_gt_three hxlow
  have hdenpos : 0 < x ^ 2 - 2 := by nlinarith
  have hsq_upper : x ^ 2 ≤ (8 * Real.pi) ^ 2 := by
    have hprod : 0 ≤ (8 * Real.pi - x) * (8 * Real.pi + x) :=
      mul_nonneg (sub_nonneg.mpr hxhigh)
        (add_nonneg (by positivity) hxpos.le)
    nlinarith
  have hdenupper : x ^ 2 - 2 < (631 : ℝ) := by
    nlinarith [pi_sq_lt_rational]
  have hxne : x ^ 2 ≠ 2 := by nlinarith
  have hK := endpointK_abs_lower_of_G
    (x := x) (D := (631 : ℝ)) hxne hdenpos hdenupper
  have hfactor_nonneg : 0 ≤ ((3 : ℝ) / 2) / 631 := by norm_num
  calc
    (9 : ℝ) / 3155 = ((3 : ℝ) / 2) / 631 * ((6 : ℝ) / 5) := by
      norm_num
    _ ≤ ((3 : ℝ) / 2) / 631 * |endpointG x| :=
      mul_le_mul_of_nonneg_left hG hfactor_nonneg
    _ ≤ |endpointK x| := hK

/-- Uniform exact kernel bound on the four alternating zero-free intervals
inside `[pi,8*pi]`. -/
theorem zero_free_interval_K_lower
    {m : ℕ} (hm : 1 ≤ m) (hm4 : m ≤ 4) {x : ℝ}
    (hx : x ∈ Set.Icc
      ((2 * (m : ℝ) - 1) * Real.pi)
      ((2 * (m : ℝ)) * Real.pi)) :
    (9 : ℝ) / 3155 ≤ |endpointK x| := by
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm4real : (m : ℝ) ≤ 4 := by exact_mod_cast hm4
  have hfactor_low : 1 ≤ 2 * (m : ℝ) - 1 := by nlinarith
  have hfactor_high : 2 * (m : ℝ) ≤ 8 := by nlinarith
  apply endpointK_lower_of_global_gap_bounds
  · simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hfactor_low Real.pi_pos.le).trans hx.1
  · exact hx.2.trans (mul_le_mul_of_nonneg_right hfactor_high Real.pi_pos.le)
  · exact zero_free_interval_G_lower hm hx

/-! ## Complete localization below `8*pi` -/

lemma first_positive_interval_localizes
    {x : ℝ} (hxlow : 2 * Real.pi ≤ x) (hxhigh : x ≤ 3 * Real.pi)
    (hsmall : |endpointK x| < correlationThreshold) :
    |x - zOne| < localizationRadius := by
  let e : ℝ := x - 2 * Real.pi
  have he : e ∈ Set.Icc (0 : ℝ) Real.pi := by
    dsimp [e]
    constructor <;> linarith
  have hxrepr : 2 * Real.pi + e = x := by
    dsimp [e]
    ring
  have hnear : |e - epsilonOne| < localizationRadius := by
    by_contra hnot
    have hfar : localizationRadius ≤ |e - epsilonOne| := le_of_not_gt hnot
    have hK := first_positive_interval_K_lower he hfar
    rw [hxrepr] at hK
    linarith [local_bound_one_gt_threshold]
  have hz : zOne = 2 * Real.pi + epsilonOne := by
    unfold zOne certifiedRoot epsilonOne
    ring
  rw [hz]
  dsimp [e] at hnear
  convert hnear using 1 <;> ring

lemma second_positive_interval_localizes
    {x : ℝ} (hxlow : 4 * Real.pi ≤ x) (hxhigh : x ≤ 5 * Real.pi)
    (hsmall : |endpointK x| < correlationThreshold) :
    |x - zTwo| < localizationRadius := by
  let e : ℝ := x - 4 * Real.pi
  have he : e ∈ Set.Icc (0 : ℝ) Real.pi := by
    dsimp [e]
    constructor <;> linarith
  have hxrepr : 4 * Real.pi + e = x := by
    dsimp [e]
    ring
  have hnear : |e - epsilonTwo| < localizationRadius := by
    by_contra hnot
    have hfar : localizationRadius ≤ |e - epsilonTwo| := le_of_not_gt hnot
    have hK := second_positive_interval_K_lower he hfar
    rw [hxrepr] at hK
    linarith [local_bound_two_gt_threshold]
  have hz : zTwo = 4 * Real.pi + epsilonTwo := by
    unfold zTwo certifiedRoot epsilonTwo
    ring
  rw [hz]
  dsimp [e] at hnear
  convert hnear using 1 <;> ring

lemma third_positive_interval_localizes
    {x : ℝ} (hxlow : 6 * Real.pi ≤ x) (hxhigh : x ≤ 7 * Real.pi)
    (hsmall : |endpointK x| < correlationThreshold) :
    |x - zThree| < localizationRadius := by
  let e : ℝ := x - 6 * Real.pi
  have he : e ∈ Set.Icc (0 : ℝ) Real.pi := by
    dsimp [e]
    constructor <;> linarith
  have hxrepr : 6 * Real.pi + e = x := by
    dsimp [e]
    ring
  have hnear : |e - epsilonThree| < localizationRadius := by
    by_contra hnot
    have hfar : localizationRadius ≤ |e - epsilonThree| := le_of_not_gt hnot
    have hK := third_positive_interval_K_lower he hfar
    rw [hxrepr] at hK
    linarith [local_bound_three_gt_threshold]
  have hz : zThree = 6 * Real.pi + epsilonThree := by
    unfold zThree certifiedRoot epsilonThree
    ring
  rw [hz]
  dsimp [e] at hnear
  convert hnear using 1 <;> ring

/-- Every point of `[0,8*pi]` at which the endpoint kernel is below the exact
threshold belongs to one of the certified neighborhoods of its first three
positive roots.  The proof exhausts the initial interval, three positive
root intervals, and four alternating zero-free intervals. -/
theorem small_endpointK_localizes_first_three
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (8 * Real.pi))
    (hsmall : |endpointK x| < correlationThreshold) :
    ∃ i : Fin 3, |x - firstThreeRoot i| < localizationRadius := by
  by_cases h1 : x ≤ Real.pi
  · have hK := endpointK_initial_interval_lower ⟨hx.1, h1⟩
    have hKabs : (165 : ℝ) / 512 ≤ |endpointK x| :=
      hK.trans (le_abs_self (endpointK x))
    exfalso
    linarith [initial_interval_bound_gt_threshold]
  have hpi : Real.pi ≤ x := (not_le.mp h1).le
  by_cases h2 : x ≤ 2 * Real.pi
  · have hgap := zero_free_interval_K_lower
      (m := 1) (by norm_num) (by norm_num) (x := x) (by
        norm_num
        exact ⟨hpi, h2⟩)
    exfalso
    linarith [zero_free_bound_gt_threshold]
  have h2pi : 2 * Real.pi ≤ x := (not_le.mp h2).le
  by_cases h3 : x ≤ 3 * Real.pi
  · refine ⟨0, ?_⟩
    change |x - zOne| < localizationRadius
    exact first_positive_interval_localizes h2pi h3 hsmall
  have h3pi : 3 * Real.pi ≤ x := (not_le.mp h3).le
  by_cases h4 : x ≤ 4 * Real.pi
  · have hgap := zero_free_interval_K_lower
      (m := 2) (by norm_num) (by norm_num) (x := x) (by
        norm_num
        exact ⟨h3pi, h4⟩)
    exfalso
    linarith [zero_free_bound_gt_threshold]
  have h4pi : 4 * Real.pi ≤ x := (not_le.mp h4).le
  by_cases h5 : x ≤ 5 * Real.pi
  · refine ⟨1, ?_⟩
    change |x - zTwo| < localizationRadius
    exact second_positive_interval_localizes h4pi h5 hsmall
  have h5pi : 5 * Real.pi ≤ x := (not_le.mp h5).le
  by_cases h6 : x ≤ 6 * Real.pi
  · have hgap := zero_free_interval_K_lower
      (m := 3) (by norm_num) (by norm_num) (x := x) (by
        norm_num
        exact ⟨h5pi, h6⟩)
    exfalso
    linarith [zero_free_bound_gt_threshold]
  have h6pi : 6 * Real.pi ≤ x := (not_le.mp h6).le
  by_cases h7 : x ≤ 7 * Real.pi
  · refine ⟨2, ?_⟩
    change |x - zThree| < localizationRadius
    exact third_positive_interval_localizes h6pi h7 hsmall
  have h7pi : 7 * Real.pi ≤ x := (not_le.mp h7).le
  have hgap := zero_free_interval_K_lower
    (m := 4) (by norm_num) (by norm_num) (x := x) (by
      norm_num
      exact ⟨h7pi, hx.2⟩)
  exfalso
  linarith [zero_free_bound_gt_threshold]

/-- Normalization at the origin can only increase absolute values, so the
same localization theorem holds for the normalized endpoint kernel `R`. -/
theorem small_endpointR_localizes_first_three
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (8 * Real.pi))
    (hsmall : |endpointR x| < correlationThreshold) :
    ∃ i : Fin 3, |x - firstThreeRoot i| < localizationRadius := by
  apply small_endpointK_localizes_first_three hx
  exact lt_of_le_of_lt (endpointK_abs_le_endpointR_abs x) hsmall

/-! ## The explicit three-point energy constant -/

/-- Squaring the exact correlation threshold gives the certified endpoint
three-point constant.  If all three correlations were below the threshold,
root localization and the triangle inequality would contradict the exact
`1/8` additive separation of the first three roots. -/
theorem endpoint_three_point_energy_lower
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 8 * Real.pi) :
    explicitDeltaLower ≤
      endpointR a ^ 2 + endpointR b ^ 2 + endpointR (a + b) ^ 2 := by
  by_contra hnot
  have henergy :
      endpointR a ^ 2 + endpointR b ^ 2 + endpointR (a + b) ^ 2 <
        explicitDeltaLower := lt_of_not_ge hnot
  have ha_sq : endpointR a ^ 2 < explicitDeltaLower := by
    nlinarith [sq_nonneg (endpointR b), sq_nonneg (endpointR (a + b))]
  have hb_sq : endpointR b ^ 2 < explicitDeltaLower := by
    nlinarith [sq_nonneg (endpointR a), sq_nonneg (endpointR (a + b))]
  have hab_sq : endpointR (a + b) ^ 2 < explicitDeltaLower := by
    nlinarith [sq_nonneg (endpointR a), sq_nonneg (endpointR b)]
  have hthreshold_pos : 0 < correlationThreshold := by
    norm_num [correlationThreshold]
  have ha_small : |endpointR a| < correlationThreshold := by
    have hsquare : |endpointR a| ^ 2 < correlationThreshold ^ 2 := by
      rw [sq_abs, threshold_sq_eq_delta]
      exact ha_sq
    nlinarith [abs_nonneg (endpointR a)]
  have hb_small : |endpointR b| < correlationThreshold := by
    have hsquare : |endpointR b| ^ 2 < correlationThreshold ^ 2 := by
      rw [sq_abs, threshold_sq_eq_delta]
      exact hb_sq
    nlinarith [abs_nonneg (endpointR b)]
  have hab_small : |endpointR (a + b)| < correlationThreshold := by
    have hsquare : |endpointR (a + b)| ^ 2 < correlationThreshold ^ 2 := by
      rw [sq_abs, threshold_sq_eq_delta]
      exact hab_sq
    nlinarith [abs_nonneg (endpointR (a + b))]
  have ha_mem : a ∈ Set.Icc (0 : ℝ) (8 * Real.pi) := by
    constructor
    · exact ha
    · linarith
  have hb_mem : b ∈ Set.Icc (0 : ℝ) (8 * Real.pi) := by
    constructor
    · exact hb
    · linarith
  have hab_mem : a + b ∈ Set.Icc (0 : ℝ) (8 * Real.pi) := by
    exact ⟨add_nonneg ha hb, hab⟩
  obtain ⟨i, hi⟩ := small_endpointR_localizes_first_three ha_mem ha_small
  obtain ⟨j, hj⟩ := small_endpointR_localizes_first_three hb_mem hb_small
  obtain ⟨k, hk⟩ := small_endpointR_localizes_first_three hab_mem hab_small
  have hidentity :
      firstThreeRoot i + firstThreeRoot j - firstThreeRoot k =
        (firstThreeRoot i - a) + (firstThreeRoot j - b) +
          ((a + b) - firstThreeRoot k) := by ring
  have htriangle :
      |firstThreeRoot i + firstThreeRoot j - firstThreeRoot k| ≤
        |firstThreeRoot i - a| + |firstThreeRoot j - b| +
          |(a + b) - firstThreeRoot k| := by
    rw [hidentity]
    calc
      |(firstThreeRoot i - a) + (firstThreeRoot j - b) +
          ((a + b) - firstThreeRoot k)| ≤
          |(firstThreeRoot i - a) + (firstThreeRoot j - b)| +
            |(a + b) - firstThreeRoot k| := abs_add_le _ _
      _ ≤ (|firstThreeRoot i - a| + |firstThreeRoot j - b|) +
            |(a + b) - firstThreeRoot k| :=
          add_le_add_right (abs_add_le _ _) _
  have hi' : |firstThreeRoot i - a| < localizationRadius := by
    simpa [abs_sub_comm] using hi
  have hj' : |firstThreeRoot j - b| < localizationRadius := by
    simpa [abs_sub_comm] using hj
  have hnear_sum :
      |firstThreeRoot i + firstThreeRoot j - firstThreeRoot k| <
        3 * localizationRadius := by
    linarith
  have hsep := firstThreeRoot_additive_separation i j k
  linarith [three_localizationRadius_lt_one_eighth]

end StrictImprovement
end Zeta23
