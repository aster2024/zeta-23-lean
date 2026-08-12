/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.EndpointKernel

/-!
# Exact analytic and rational inputs for the endpoint delta

This file begins the formalization of the root-localization certificate.  It
contains no numerical root approximation.  The first part proves the fifth
order upper Taylor bound for sine from two interval integrations and the
existing Mathlib cubic lower bound.  The second part records the exact rational
terminal inequalities consumed by the localization proof.

The zero classification, interval cover, and final compact-minimum theorem are
added after this analytic base.  This is a source draft until checked by the
pinned Lean toolchain in `LEAN_FORMALIZATION_PLAN.md`.
-/

noncomputable section

open MeasureTheory Real intervalIntegral

namespace Zeta23
namespace StrictImprovement

/-- Fourth-order upper Taylor polynomial for cosine. -/
def cosQuartic (x : ℝ) : ℝ := 1 - x ^ 2 / 2 + x ^ 4 / 24

/-- Fifth-order upper Taylor polynomial for sine. -/
def sinQuintic (x : ℝ) : ℝ := x - x ^ 3 / 6 + x ^ 5 / 120

/-- The cubic sine lower bound integrates to the fourth-order cosine upper
bound on the nonnegative half-line. -/
lemma cos_le_cosQuartic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ cosQuartic x := by
  have hpoly_int : IntervalIntegrable (fun u : ℝ => u - u ^ 3 / 6) volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hsin_int : IntervalIntegrable (fun u : ℝ => Real.sin u) volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hmono :
      (∫ u in (0 : ℝ)..x, u - u ^ 3 / 6)
        ≤ ∫ u in (0 : ℝ)..x, Real.sin u := by
    refine intervalIntegral.integral_mono_on hx hpoly_int hsin_int ?_
    intro u hu
    exact Real.sin_ge_sub_cube hu.1
  have hanti : ∀ u : ℝ,
      HasDerivAt (fun y : ℝ => y ^ 2 / 2 - y ^ 4 / 24)
        (u - u ^ 3 / 6) u := by
    intro u
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * u ^ 3) u := by
      simpa using hasDerivAt_pow 4 u
    have h := (h2.div_const 2).sub (h4.div_const 24)
    exact h.congr_deriv (by ring)
  have hpoly_eval :
      (∫ u in (0 : ℝ)..x, u - u ^ 3 / 6) = x ^ 2 / 2 - x ^ 4 / 24 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hanti u) hpoly_int]
    ring
  have hsin_eval :
      (∫ u in (0 : ℝ)..x, Real.sin u) = 1 - Real.cos x := by
    rw [integral_sin]
    simp
  unfold cosQuartic
  linarith

/-- Fifth-order sine upper bound, proved without a floating-point or Taylor
remainder oracle. -/
lemma sin_le_sinQuintic {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ sinQuintic x := by
  have hcos_int : IntervalIntegrable (fun u : ℝ => Real.cos u) volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hpoly_int : IntervalIntegrable cosQuartic volume 0 x :=
    Continuous.intervalIntegrable (by unfold cosQuartic; fun_prop) 0 x
  have hmono :
      (∫ u in (0 : ℝ)..x, Real.cos u)
        ≤ ∫ u in (0 : ℝ)..x, cosQuartic u := by
    refine intervalIntegral.integral_mono_on hx hcos_int hpoly_int ?_
    intro u hu
    exact cos_le_cosQuartic hu.1
  have hanti : ∀ u : ℝ, HasDerivAt sinQuintic (cosQuartic u) u := by
    intro u
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * u ^ 2) u := by
      simpa using hasDerivAt_pow 3 u
    have h5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * u ^ 4) u := by
      simpa using hasDerivAt_pow 5 u
    unfold sinQuintic cosQuartic
    have h := ((hasDerivAt_id u).sub (h3.div_const 6)).add
      (h5.div_const 120)
    exact h.congr_deriv (by ring)
  have hcos_eval :
      (∫ u in (0 : ℝ)..x, Real.cos u) = Real.sin x := by
    rw [integral_cos]
    simp
  have hpoly_eval :
      (∫ u in (0 : ℝ)..x, cosQuartic u) = sinQuintic x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hanti u) hpoly_int]
    simp [sinQuintic]
  linarith

/-- Exact endpoint identity `theta(1)^2 = 1/2`. -/
lemma endpointTheta_sq : ThmD.theta 1 ^ 2 = (1 : ℝ) / 2 := by
  have htheta : ThmD.theta 1 = Real.sqrt 2 / 2 := by
    have h := ThmD.sqrt2_mul_half (lam := (1 : ℝ))
    norm_num at h
    linarith
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [htheta]
  nlinarith

/-- Exact endpoint identity `sqrt 2 * theta(1) = 1`. -/
lemma sqrtTwo_mul_endpointTheta : Real.sqrt 2 * ThmD.theta 1 = 1 := by
  have htheta : ThmD.theta 1 = Real.sqrt 2 / 2 := by
    have h := ThmD.sqrt2_mul_half (lam := (1 : ℝ))
    norm_num at h
    linarith
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [htheta]
  nlinarith

/-- Rational endpoint cosine lower bound. -/
lemma three_fourths_le_endpointCos :
    (3 : ℝ) / 4 ≤ Real.cos (ThmD.theta 1) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := ThmD.theta 1)
  rw [endpointTheta_sq] at h
  norm_num at h ⊢
  exact h

/-- The exact rational upper bound for the endpoint root parameter. -/
theorem endpointKappa_le : endpointKappa ≤ (49 : ℝ) / 40 := by
  let th : ℝ := ThmD.theta 1
  have hth0 : 0 ≤ th := ThmD.theta_nonneg (lam := (1 : ℝ)) (by norm_num)
  have hsin : Real.sin th ≤ th - th ^ 3 / 6 + th ^ 5 / 120 := by
    simpa [sinQuintic] using sin_le_sinQuintic hth0
  have hcos : (3 : ℝ) / 4 ≤ Real.cos th := by
    have h := Real.one_sub_sq_div_two_le_cos (x := th)
    have hsq : th ^ 2 = (1 : ℝ) / 2 := by
      simpa [th] using endpointTheta_sq
    nlinarith
  have hcos_pos : 0 < Real.cos th := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hmul := mul_le_mul_of_nonneg_left hsin hsqrt_nonneg
  have hth_sq : th ^ 2 = (1 : ℝ) / 2 := by
    simpa [th] using endpointTheta_sq
  have hsqrt_th : Real.sqrt 2 * th = 1 := by
    simpa [th] using sqrtTwo_mul_endpointTheta
  have hnum :
      Real.sqrt 2 * Real.sin th ≤ (441 : ℝ) / 480 := by
    calc
      Real.sqrt 2 * Real.sin th
          ≤ Real.sqrt 2 * (th - th ^ 3 / 6 + th ^ 5 / 120) := hmul
      _ = (441 : ℝ) / 480 := by
        calc
          Real.sqrt 2 * (th - th ^ 3 / 6 + th ^ 5 / 120)
              = (Real.sqrt 2 * th) *
                  (1 - th ^ 2 / 6 + th ^ 4 / 120) := by ring
          _ = (441 : ℝ) / 480 := by
            rw [hsqrt_th, show th ^ 4 = (th ^ 2) ^ 2 by ring, hth_sq]
            norm_num
  unfold endpointKappa
  rw [Real.tan_eq_sin_div_cos, ← mul_div_assoc]
  apply (div_le_iff₀ hcos_pos).2
  nlinarith

/-- The unrounded strict rational lower bound supplied by the cubic sine and
quartic cosine estimates. -/
theorem eighty_eight_over_seventy_three_lt_endpointKappa :
    (88 : ℝ) / 73 < endpointKappa := by
  let th : ℝ := ThmD.theta 1
  have hth_pos : 0 < th := ThmD.theta_pos (lam := (1 : ℝ)) (by norm_num)
  have hth_sq : th ^ 2 = (1 : ℝ) / 2 := by
    simpa [th] using endpointTheta_sq
  have hsqrt_th : Real.sqrt 2 * th = 1 := by
    simpa [th] using sqrtTwo_mul_endpointTheta
  have hsin0 := Real.sin_gt_sub_cube hth_pos
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hnum : (11 : ℝ) / 12 < Real.sqrt 2 * Real.sin th := by
    have hmul := mul_lt_mul_of_pos_left hsin0 hsqrt_pos
    calc
      (11 : ℝ) / 12
          = Real.sqrt 2 * (th - th ^ 3 / 6) := by
              symm
              calc
                Real.sqrt 2 * (th - th ^ 3 / 6)
                    = (Real.sqrt 2 * th) * (1 - th ^ 2 / 6) := by ring
                _ = (11 : ℝ) / 12 := by rw [hsqrt_th, hth_sq]; norm_num
      _ < Real.sqrt 2 * Real.sin th := hmul
  have hquartic : cosQuartic th = (73 : ℝ) / 96 := by
    unfold cosQuartic
    rw [show th ^ 4 = (th ^ 2) ^ 2 by ring, hth_sq]
    norm_num
  have hcos_upper : Real.cos th ≤ (73 : ℝ) / 96 := by
    rw [← hquartic]
    exact cos_le_cosQuartic hth_pos.le
  have hcos_pos : 0 < Real.cos th := by
    exact ThmD.cos_theta_pos (lam := (1 : ℝ)) (by norm_num) (by norm_num)
  unfold endpointKappa
  rw [Real.tan_eq_sin_div_cos, ← mul_div_assoc]
  apply (lt_div_iff₀ hcos_pos).2
  nlinarith

/-- The coarser historical lower bound retained for downstream compatibility. -/
theorem six_fifths_lt_endpointKappa : (6 : ℝ) / 5 < endpointKappa := by
  nlinarith [eighty_eight_over_seventy_three_lt_endpointKappa]

/-- A division-safe upper bound for tangent, obtained from `sin x ≤ x` and
`cos x ≥ 1 - x^2/2`. -/
lemma tan_le_quadratic_fraction {x : ℝ}
    (hx : 0 ≤ x) (hden : 0 < 1 - x ^ 2 / 2) :
    Real.tan x ≤ x / (1 - x ^ 2 / 2) := by
  have hsin : Real.sin x ≤ x := Real.sin_le hx
  have hcos_lower : 1 - x ^ 2 / 2 ≤ Real.cos x :=
    Real.one_sub_sq_div_two_le_cos
  have hcos_pos : 0 < Real.cos x := lt_of_lt_of_le hden hcos_lower
  rw [Real.tan_eq_sin_div_cos]
  calc
    Real.sin x / Real.cos x ≤ x / Real.cos x :=
      div_le_div_of_nonneg_right hsin hcos_pos.le
    _ ≤ x / (1 - x ^ 2 / 2) :=
      div_le_div_of_nonneg_left hx hden hcos_lower

/-- Exact tangent upper bound used at the third-root test point. -/
lemma tan_one_sixteenth_le : Real.tan ((1 : ℝ) / 16) ≤ 32 / 511 := by
  have h := tan_le_quadratic_fraction (x := (1 : ℝ) / 16)
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Exact tangent lower bound used at the first-root test point. -/
lemma tan_one_fifth_gt : (76 : ℝ) / 375 < Real.tan ((1 : ℝ) / 5) := by
  have hsin := Real.sin_gt_sub_cube (x := (1 : ℝ) / 5) (by norm_num)
  have hcos := cos_le_cosQuartic (x := (1 : ℝ) / 5) (by norm_num)
  have hcos_pos : 0 < Real.cos ((1 : ℝ) / 5) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_gt_three]
    · nlinarith [Real.pi_gt_three]
  have hquartic : cosQuartic ((1 : ℝ) / 5) = (14701 : ℝ) / 15000 := by
    norm_num [cosQuartic]
  rw [hquartic] at hcos
  rw [Real.tan_eq_sin_div_cos]
  apply (lt_div_iff₀ hcos_pos).2
  nlinarith

/-- The test immediately to the right of the third nominal center remains
below `kappa`; this is the exact input for `epsilon_3 > 1/8`. -/
lemma third_root_test_lt_endpointKappa :
    (6 * Real.pi + (1 : ℝ) / 8) * Real.tan ((1 : ℝ) / 16)
      < endpointKappa := by
  have hpi : Real.pi < (3927 : ℝ) / 1250 := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h
  have htan0 : 0 ≤ Real.tan ((1 : ℝ) / 16) := by
    have h := Real.le_tan (x := (1 : ℝ) / 16) (by norm_num)
      (by nlinarith [Real.pi_gt_three])
    nlinarith
  have hfirst :
      (6 * Real.pi + (1 : ℝ) / 8) * Real.tan ((1 : ℝ) / 16)
        ≤ (6 * ((3927 : ℝ) / 1250) + 1 / 8) *
          Real.tan ((1 : ℝ) / 16) := by
    apply mul_le_mul_of_nonneg_right _ htan0
    nlinarith
  have hsecond :
      (6 * ((3927 : ℝ) / 1250) + 1 / 8) *
          Real.tan ((1 : ℝ) / 16)
        ≤ (6 * ((3927 : ℝ) / 1250) + 1 / 8) * (32 / 511) := by
    exact mul_le_mul_of_nonneg_left tan_one_sixteenth_le (by norm_num)
  calc
    (6 * Real.pi + (1 : ℝ) / 8) * Real.tan ((1 : ℝ) / 16)
        ≤ (6 * ((3927 : ℝ) / 1250) + 1 / 8) *
          Real.tan ((1 : ℝ) / 16) := hfirst
    _ ≤ (6 * ((3927 : ℝ) / 1250) + 1 / 8) * (32 / 511) := hsecond
    _ < (6 : ℝ) / 5 := by norm_num
    _ < endpointKappa := six_fifths_lt_endpointKappa

/-- The test immediately to the right of the first nominal center lies above
`kappa`; this is the exact input for `epsilon_1 < 2/5`. -/
lemma endpointKappa_lt_first_root_test :
    endpointKappa <
      (2 * Real.pi + (2 : ℝ) / 5) * Real.tan ((1 : ℝ) / 5) := by
  have hx : (32 : ℝ) / 5 < 2 * Real.pi + 2 / 5 := by
    nlinarith [Real.pi_gt_three]
  have htan_pos : 0 < Real.tan ((1 : ℝ) / 5) := by
    nlinarith [tan_one_fifth_gt]
  have hscale :
      (32 : ℝ) / 5 * (76 / 375)
        < (2 * Real.pi + 2 / 5) * Real.tan ((1 : ℝ) / 5) := by
    calc
      (32 : ℝ) / 5 * (76 / 375)
          < (32 : ℝ) / 5 * Real.tan ((1 : ℝ) / 5) :=
            mul_lt_mul_of_pos_left tan_one_fifth_gt (by norm_num)
      _ < (2 * Real.pi + 2 / 5) * Real.tan ((1 : ℝ) / 5) :=
            mul_lt_mul_of_pos_right hx htan_pos
  calc
    endpointKappa ≤ (49 : ℝ) / 40 := endpointKappa_le
    _ < (32 : ℝ) / 5 * (76 / 375) := by norm_num
    _ < (2 * Real.pi + 2 / 5) * Real.tan ((1 : ℝ) / 5) := hscale

/-! ## Exact rational terminal ledger -/

def localizationRadius : ℝ := 1000 / 24001
def correlationThreshold : ℝ := 2 / 1757
def explicitDeltaLower : ℝ := 4 / 3087049
def explicitEtaLower : ℝ := 1 / 250050969

lemma localizationRadius_pos : 0 < localizationRadius := by
  norm_num [localizationRadius]

lemma localizationRadius_lt_one_div_twenty_four :
    localizationRadius < (1 : ℝ) / 24 := by
  norm_num [localizationRadius]

lemma three_localizationRadius_lt_one_eighth :
    3 * localizationRadius < (1 : ℝ) / 8 := by
  norm_num [localizationRadius]

lemma first_root_test_rational :
    (32 : ℝ) / 5 * (1 / 5 + 1 / 375) = 2432 / 1875 := by
  norm_num

lemma first_root_test_gt_kappa_upper : (49 : ℝ) / 40 < 2432 / 1875 := by
  norm_num

lemma local_cos_rational :
    1 - ((53 : ℝ) / 240) ^ 2 / 2 = 112391 / 115200 := by
  norm_num

/-- Exact rational square bound for pi, using Mathlib's certified four-decimal
upper bound rather than a floating-point evaluation. -/
lemma pi_sq_lt_rational :
    Real.pi ^ 2 < ((3927 : ℝ) / 1250) ^ 2 := by
  have hpi : Real.pi < (3927 : ℝ) / 1250 := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h
  have hsum : 0 < (3927 : ℝ) / 1250 + Real.pi := by
    nlinarith [Real.pi_pos]
  have hprod :
      0 < ((3927 : ℝ) / 1250 - Real.pi) *
        ((3927 : ℝ) / 1250 + Real.pi) :=
    mul_pos (sub_pos.mpr hpi) hsum
  nlinarith

lemma first_positive_interval_denominator :
    (3 * Real.pi) ^ 2 - 2 < (87 : ℝ) := by
  nlinarith [pi_sq_lt_rational]

lemma second_positive_interval_denominator :
    (5 * Real.pi) ^ 2 - 2 < (245 : ℝ) := by
  nlinarith [pi_sq_lt_rational]

lemma third_positive_interval_denominator :
    (7 * Real.pi) ^ 2 - 2 < (482 : ℝ) := by
  nlinarith [pi_sq_lt_rational]

lemma local_bound_one_gt_threshold :
    correlationThreshold < (561955 : ℝ) / 267275136 := by
  norm_num [correlationThreshold]

lemma local_bound_two_gt_threshold :
    correlationThreshold < (112391 : ℝ) / 75267136 := by
  norm_num [correlationThreshold]

lemma local_bound_three_gt_threshold :
    correlationThreshold < (1685865 : ℝ) / 1480765696 := by
  norm_num [correlationThreshold]

lemma initial_interval_bound_gt_threshold :
    correlationThreshold < (165 : ℝ) / 512 := by
  norm_num [correlationThreshold]

lemma zero_free_bound_gt_threshold :
    correlationThreshold < (9 : ℝ) / 3155 := by
  norm_num [correlationThreshold]

lemma threshold_sq_eq_delta :
    correlationThreshold ^ 2 = explicitDeltaLower := by
  norm_num [correlationThreshold, explicitDeltaLower]

lemma delta_gap_eq_eta :
    explicitDeltaLower / 9 * ((1 : ℝ) / 6) ^ 2 = explicitEtaLower := by
  norm_num [explicitDeltaLower, explicitEtaLower]

end StrictImprovement
end Zeta23
