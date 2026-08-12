/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WiderRootNeighborhood
import Zeta23.StrictImprovement.EndpointTaylorRefinement

/-!
# Six-root localization below `12 * pi`

This module turns the exact strip and neighborhood estimates into a complete
cover of `[0, 12 * pi]`.  The first five positive half-periods are handled by
root monotonicity; the alternating half-periods use the existing sign lemma;
the last half-period is split at offset `-1/8` because the sixth positive root
lies just to the right of `12 * pi`.

No floating-point approximation or sampled root enclosure is used here.  This
remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open MeasureTheory Real Set intervalIntegral

namespace Zeta23
namespace StrictImprovement

/-- On a positive half-period, a point outside the radius-`1/8` root
neighborhood has scalar numerator at least `L_n / 8`.  The proof explicitly
handles the case in which the formal left boundary of the neighborhood is
negative: that branch is then impossible for `e >= 0`. -/
theorem wider_positive_interval_outside_radius_G_lower
    (i : Fin 6) {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) Real.pi)
    (hfar : widerRadius ≤ |e - firstSixOffset i|) :
    widerDerivativeLower (firstSixIndex i) * widerRadius ≤
      |endpointG (2 * Real.pi * (firstSixIndex i : ℝ) + e)| := by
  let n := firstSixIndex i
  let eps := firstSixOffset i
  let L := widerDerivativeLower n
  have hn : 1 ≤ n := firstSixIndex_pos i
  have heps := firstSixOffset_mem i
  have hroot : offsetNumerator n eps = 0 := by
    simpa [n, eps] using firstSixOffset_numerator_zero i
  have hrootMem : eps ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · exact heps.1.le
    · nlinarith [heps.2, Real.pi_gt_three]
  have hLpos : 0 < L := by
    simpa [n, L] using widerDerivativeLower_pos i
  have hrho : widerRadius = (1 : ℝ) / 8 := rfl
  have hrhoPos : 0 < widerRadius := widerRadius_pos
  have hmono := (offsetNumerator_strictMonoOn n hn).monotoneOn
  have hnum : L * widerRadius ≤ |offsetNumerator n e| := by
    rcases le_total e eps with hleft | hright
    · have hfar' := hfar
      rw [abs_of_nonpos (sub_nonpos.mpr hleft)] at hfar'
      let l : ℝ := eps - widerRadius
      have hel : e ≤ l := by
        dsimp [l]
        linarith
      have hlMem : l ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor
        · exact he.1.trans hel
        · dsimp [l]
          nlinarith [heps.2, Real.pi_gt_three, hrhoPos]
      have hldist : |l - eps| ≤ widerRadius := by
        dsimp [l]
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hlin := wider_neighborhood_numerator_linear i hldist
      have hlroot := hmono hlMem hrootMem (by
        dsimp [l]
        linarith)
      have hlNonpos : offsetNumerator n l ≤ 0 := by
        rw [hroot] at hlroot
        exact hlroot
      have helOrder := hmono he hlMem hel
      have heNonpos : offsetNumerator n e ≤ 0 := helOrder.trans hlNonpos
      rw [abs_of_nonpos hlNonpos] at hlin
      rw [abs_of_nonpos heNonpos]
      have hdistEq : |l - eps| = widerRadius := by
        dsimp [l]
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [hdistEq] at hlin
      dsimp [n, eps, L] at hlin helOrder ⊢
      nlinarith
    · have hfar' := hfar
      rw [abs_of_nonneg (sub_nonneg.mpr hright)] at hfar'
      let r : ℝ := eps + widerRadius
      have hre : r ≤ e := by
        dsimp [r]
        linarith
      have hrMem : r ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor
        · dsimp [r]
          nlinarith [heps.1, hrhoPos]
        · dsimp [r]
          rw [hrho]
          nlinarith [heps.2, Real.pi_gt_three]
      have hrdist : |r - eps| ≤ widerRadius := by
        dsimp [r]
        rw [show eps + widerRadius - eps = widerRadius by ring,
          abs_of_nonneg hrhoPos.le]
      have hlin := wider_neighborhood_numerator_linear i hrdist
      have hrootr := hmono hrootMem hrMem (by
        dsimp [r]
        linarith)
      have hrNonneg : 0 ≤ offsetNumerator n r := by
        rw [hroot] at hrootr
        exact hrootr
      have hreOrder := hmono hrMem he hre
      have heNonneg : 0 ≤ offsetNumerator n e := hrNonneg.trans hreOrder
      rw [abs_of_nonneg hrNonneg] at hlin
      rw [abs_of_nonneg heNonneg]
      have hdistEq : |r - eps| = widerRadius := by
        dsimp [r]
        rw [show eps + widerRadius - eps = widerRadius by ring,
          abs_of_nonneg hrhoPos.le]
      rw [hdistEq] at hlin
      dsimp [n, eps, L] at hlin hreOrder ⊢
      nlinarith
  rw [endpointG_abs_eq_offsetNumerator_abs]
  simpa [n, L] using hnum

/-- Exact kernel exclusion on each of the first five positive half-periods. -/
theorem wider_positive_interval_outside_radius_K_lower
    (i : Fin 5) {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) Real.pi)
    (hfar : widerRadius ≤
      |e - firstSixOffset ⟨i, Nat.lt_trans i.isLt (by norm_num)⟩|) :
    widerCorrelationThreshold <
      |endpointK
        (2 * Real.pi * (((i : ℕ) + 1 : ℕ) : ℝ) + e)| := by
  let j : Fin 6 := ⟨i, Nat.lt_trans i.isLt (by norm_num)⟩
  let n : ℕ := firstSixIndex j
  let x : ℝ := 2 * Real.pi * (n : ℝ) + e
  let A : ℝ := (22 * (2 * n + 1) : ℝ) / 7
  let D : ℝ := A ^ 2
  have hn : 1 ≤ n := firstSixIndex_pos j
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpiUpper : Real.pi < (22 : ℝ) / 7 := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h
  have hfactorPos : 0 < (2 * n + 1 : ℝ) := by
    positivity
  have hAupper : ((2 * n + 1 : ℕ) : ℝ) * Real.pi < A := by
    dsimp [A]
    push_cast
    nlinarith [mul_pos (sub_pos.mpr hpiUpper) hfactorPos]
  have hApos : 0 < A := lt_of_lt_of_le
    (mul_pos (by positivity) Real.pi_pos) hAupper.le
  have hDcond :
      (((2 * n + 1 : ℕ) : ℝ) * Real.pi) ^ 2 - 2 < D := by
    have hprod :
        0 < (A - ((2 * n + 1 : ℕ) : ℝ) * Real.pi) *
          (A + ((2 * n + 1 : ℕ) : ℝ) * Real.pi) :=
      mul_pos (sub_pos.mpr hAupper)
        (add_pos hApos (mul_pos (by positivity) Real.pi_pos))
    dsimp [D]
    nlinarith
  have hden := positive_interval_denominator_bounds n hn he hDcond
  have hxne : x ^ 2 ≠ 2 := by
    dsimp [x] at hden ⊢
    nlinarith
  have hG := wider_positive_interval_outside_radius_G_lower j he (by
    simpa [j] using hfar)
  have hK := endpointK_abs_lower_of_G
    (x := x) (D := D) hxne (by simpa [x] using hden.1)
      (by simpa [x] using hden.2)
  have hfactor : 0 ≤ ((3 : ℝ) / 2) / D := by
    dsimp [D]
    positivity
  have hrat := wider_positive_outside_rational i
  have hnEq : n = (i : ℕ) + 1 := by rfl
  have hxEq : x = 2 * Real.pi * (((i : ℕ) + 1 : ℕ) : ℝ) + e := by
    simp [x, hnEq]
  calc
    widerCorrelationThreshold
        < ((3 : ℝ) / 2) / D *
            (widerDerivativeLower n * widerRadius) := by
          dsimp [D, A]
          rw [hnEq]
          convert hrat using 1 <;> ring
    _ ≤ ((3 : ℝ) / 2) / D * |endpointG x| :=
      mul_le_mul_of_nonneg_left (by simpa [x] using hG) hfactor
    _ ≤ |endpointK x| := hK
    _ = |endpointK
        (2 * Real.pi * (((i : ℕ) + 1 : ℕ) : ℝ) + e)| := by rw [hxEq]

/-- The refined endpoint lower bound strengthens the common scalar-numerator
bound on every alternating zero-free half-period.  This is the same sign
decomposition as `zero_free_interval_G_lower`, retained in the wider layer so
the frozen three-root route is unchanged. -/
theorem wider_zero_free_interval_G_lower
    {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x ∈ Set.Icc
      ((2 * (m : ℝ) - 1) * Real.pi)
      ((2 * (m : ℝ)) * Real.pi)) :
    (592688 : ℝ) / 490449 ≤ |endpointG x| := by
  let t : ℝ := x / 2 - ((m : ℝ) - 1) * Real.pi
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmcast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm]
    norm_num
  have ht : t ∈ Set.Icc (Real.pi / 2) Real.pi := by
    dsimp [t]
    constructor <;> nlinarith [Real.pi_pos]
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
  have hxlarge : (592688 : ℝ) / 490449 ≤ x := by
    have hfactor : 1 ≤ 2 * (m : ℝ) - 1 := by nlinarith
    have hpi_le : Real.pi ≤ (2 * (m : ℝ) - 1) * Real.pi :=
      mul_le_mul_of_nonneg_right hfactor Real.pi_pos.le
    have hcpi : (592688 : ℝ) / 490449 < Real.pi := by
      nlinarith [Real.pi_gt_three]
    exact hcpi.le.trans (hpi_le.trans hx.1)
  have hklarge : (592688 : ℝ) / 490449 ≤ endpointKappa :=
    endpointKappa_refined_lower
  have hweighted :
      (592688 : ℝ) / 490449 ≤
        x * |Real.sin t| + endpointKappa * |Real.cos t| := by
    calc
      (592688 : ℝ) / 490449 ≤
          (592688 : ℝ) / 490449 *
            (|Real.sin t| + |Real.cos t|) := by
              nlinarith
      _ = (592688 : ℝ) / 490449 * |Real.sin t| +
          (592688 : ℝ) / 490449 * |Real.cos t| := by ring
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
    nlinarith [mul_nonneg hx0 hsin,
      mul_nonpos_of_nonneg_of_nonpos hk0 hcos]
  have hweighted' := hweighted
  rw [abs_of_nonneg hsin, abs_of_nonpos hcos] at hweighted'
  rw [hGfactor, abs_mul, hfactor_abs, one_mul,
    abs_of_nonneg hinner_nonneg]
  nlinarith

/-- Exact exclusion on the first five alternating zero-free half-periods. -/
theorem wider_zero_free_interval_K_lower
    (i : Fin 5) {x : ℝ}
    (hx : x ∈ Set.Icc
      ((2 * (((i : ℕ) + 1 : ℕ) : ℝ) - 1) * Real.pi)
      ((2 * (((i : ℕ) + 1 : ℕ) : ℝ)) * Real.pi)) :
    widerCorrelationThreshold ≤ |endpointK x| := by
  let m : ℕ := (i : ℕ) + 1
  let A : ℝ := 44 * (m : ℝ) / 7
  let D : ℝ := A ^ 2
  have hm : 1 ≤ m := by omega
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpiUpper : Real.pi < (22 : ℝ) / 7 := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h
  have hx' : x ∈ Set.Icc
      ((2 * (m : ℝ) - 1) * Real.pi)
      ((2 * (m : ℝ)) * Real.pi) := by
    simpa [m] using hx
  have hxpos : 0 < x := by
    have hfactor : 0 < 2 * (m : ℝ) - 1 := by nlinarith
    exact lt_of_lt_of_le (mul_pos hfactor Real.pi_pos) hx'.1
  have hxlarge : 2 < x := by
    nlinarith [hx'.1, Real.pi_gt_three, hmReal]
  have hxupper : x < A := by
    have hscale : 2 * (m : ℝ) * Real.pi < 44 * (m : ℝ) / 7 := by
      have hmPos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hmReal
      nlinarith [mul_pos (sub_pos.mpr hpiUpper) hmPos]
    exact hx'.2.trans_lt hscale
  have hApos : 0 < A := lt_trans hxpos hxupper
  have hdenpos : 0 < x ^ 2 - 2 := by nlinarith
  have hdenD : x ^ 2 - 2 < D := by
    have hprod : 0 < (A - x) * (A + x) :=
      mul_pos (sub_pos.mpr hxupper) (add_pos hApos hxpos)
    dsimp [D]
    nlinarith
  have hxne : x ^ 2 ≠ 2 := by nlinarith
  have hG := wider_zero_free_interval_G_lower hm hx'
  have hK := endpointK_abs_lower_of_G
    (x := x) (D := D) hxne hdenpos hdenD
  have hfactor : 0 ≤ ((3 : ℝ) / 2) / D := by
    dsimp [D]
    positivity
  have hrat := wider_zero_free_rational i
  have hmEq : m = (i : ℕ) + 1 := rfl
  calc
    widerCorrelationThreshold
        ≤ ((3 : ℝ) / 2) / D * ((592688 : ℝ) / 490449) := by
          dsimp [D, A]
          rw [hmEq]
          convert hrat using 1 <;> ring
    _ ≤ ((3 : ℝ) / 2) / D * |endpointG x| :=
      mul_le_mul_of_nonneg_left hG hfactor
    _ ≤ |endpointK x| := hK

/-! ## The final half-period `[11*pi, 12*pi]` -/

/-- Cubic Taylor control gives a uniform sine lower bound on the part of the
final half-period whose distance to `12*pi` is at least `1/8`. -/
lemma wider_final_sine_lower {u : ℝ}
    (hu0 : (1 : ℝ) / 16 ≤ u) (hu1 : u ≤ Real.pi / 2) :
    (1 : ℝ) / 17 < Real.sin u := by
  have huNonneg : 0 ≤ u := le_trans (by norm_num) hu0
  have hpiUpper : Real.pi < (22 : ℝ) / 7 := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h
  have huUpper : u < (11 : ℝ) / 7 := by nlinarith
  have hsin := Real.sin_ge_sub_cube huNonneg
  by_cases hhalf : u ≤ (1 : ℝ) / 2
  · have hsq : u ^ 2 ≤ (1 : ℝ) / 4 := by
      have hprod : 0 ≤ ((1 : ℝ) / 2 - u) * ((1 : ℝ) / 2 + u) :=
        mul_nonneg (sub_nonneg.mpr hhalf) (add_nonneg (by norm_num) huNonneg)
      nlinarith
    have hcube : u ^ 3 ≤ u / 4 := by
      have hmul := mul_le_mul_of_nonneg_left hsq huNonneg
      nlinarith
    nlinarith
  · have hhalf' : (1 : ℝ) / 2 < u := lt_of_not_ge hhalf
    have hsq : u ^ 2 < (121 : ℝ) / 49 := by
      have hprod :
          0 < ((11 : ℝ) / 7 - u) * ((11 : ℝ) / 7 + u) :=
        mul_pos (sub_pos.mpr huUpper) (add_pos (by norm_num) huNonneg)
      nlinarith
    have hcube : u ^ 3 < (121 : ℝ) / 49 * u := by
      have hmul := mul_lt_mul_of_pos_left hsq (lt_of_lt_of_le (by norm_num) hu0)
      nlinarith
    nlinarith

/-- On the far part of the last half-period the two terms of the scalar
numerator have the same sign, yielding the exact `33/17` lower bound. -/
theorem wider_last_zero_free_far_G_lower
    {x : ℝ} (hx : x ∈ Set.Icc (11 * Real.pi) (12 * Real.pi))
    (hfar : x - 12 * Real.pi ≤ -widerRadius) :
    (33 : ℝ) / 17 < |endpointG x| := by
  let e : ℝ := x - 12 * Real.pi
  let u : ℝ := -e / 2
  have he : e ∈ Set.Icc (-Real.pi) 0 := by
    dsimp [e]
    constructor <;> linarith
  have hefar : e ≤ -(1 : ℝ) / 8 := by
    simpa [e, widerRadius] using hfar
  have hu0 : (1 : ℝ) / 16 ≤ u := by
    dsimp [u]
    linarith
  have hu1 : u ≤ Real.pi / 2 := by
    dsimp [u]
    linarith [he.1]
  have huNonneg : 0 ≤ u := le_trans (by norm_num) hu0
  have hsin := wider_final_sine_lower hu0 hu1
  have hcos : 0 ≤ Real.cos u := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [Real.pi_pos]
    · exact hu1
  have harg : x / 2 = -u + (6 : ℝ) * Real.pi := by
    dsimp [u, e]
    ring
  have hsinShift : Real.sin (x / 2) = -Real.sin u := by
    rw [harg, Real.sin_add_nat_mul_pi]
    simp
  have hcosShift : Real.cos (x / 2) = Real.cos u := by
    rw [harg, Real.cos_add_nat_mul_pi]
    simp
  have hx33 : 33 < x := by
    nlinarith [hx.1, Real.pi_gt_three]
  have hxpos : 0 < x := by linarith
  have hxs : (33 : ℝ) / 17 < x * Real.sin u := by
    calc
      (33 : ℝ) / 17 < x * ((1 : ℝ) / 17) := by nlinarith
      _ < x * Real.sin u := mul_lt_mul_of_pos_left hsin hxpos
  have hkc : 0 ≤ endpointKappa * Real.cos u :=
    mul_nonneg endpointKappa_pos.le hcos
  have hinner : (33 : ℝ) / 17 <
      x * Real.sin u + endpointKappa * Real.cos u :=
    hxs.trans_le (le_add_of_nonneg_right hkc)
  have hG : endpointG x =
      -(x * Real.sin u + endpointKappa * Real.cos u) := by
    unfold endpointG
    rw [hsinShift, hcosShift]
    ring
  rw [hG, abs_neg, abs_of_pos (lt_trans (by norm_num) hinner)]
  exact hinner

theorem wider_last_zero_free_far_K_lower
    {x : ℝ} (hx : x ∈ Set.Icc (11 * Real.pi) (12 * Real.pi))
    (hfar : x - 12 * Real.pi ≤ -widerRadius) :
    widerCorrelationThreshold < |endpointK x| := by
  let D : ℝ := ((264 : ℝ) / 7) ^ 2
  have hpiUpper : Real.pi < (22 : ℝ) / 7 := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h
  have hxpos : 0 < x := lt_of_lt_of_le (by
    nlinarith [Real.pi_gt_three]) hx.1
  have hxlarge : 2 < x := by nlinarith
  have hxupper : x < (264 : ℝ) / 7 := by
    exact hx.2.trans_lt (by nlinarith)
  have hdenpos : 0 < x ^ 2 - 2 := by nlinarith
  have hdenD : x ^ 2 - 2 < D := by
    have hprod : 0 < ((264 : ℝ) / 7 - x) * ((264 : ℝ) / 7 + x) :=
      mul_pos (sub_pos.mpr hxupper) (add_pos (by norm_num) hxpos)
    dsimp [D]
    nlinarith
  have hxne : x ^ 2 ≠ 2 := by nlinarith
  have hG := wider_last_zero_free_far_G_lower hx hfar
  have hK := endpointK_abs_lower_of_G
    (x := x) (D := D) hxne hdenpos hdenD
  have hfactor : 0 ≤ ((3 : ℝ) / 2) / D := by
    dsimp [D]
    positivity
  calc
    widerCorrelationThreshold
        < ((3 : ℝ) / 2) / D * ((33 : ℝ) / 17) := by
          simpa [D] using wider_last_zero_free_far_rational
    _ < ((3 : ℝ) / 2) / D * |endpointG x| :=
      mul_lt_mul_of_pos_left hG (by positivity)
    _ ≤ |endpointK x| := hK

/-- If the last-half-period point lies to the right of offset `-1/8` but is
still at least radius `1/8` from the sixth root, integrate the enlarged-strip
derivative all the way to that root. -/
theorem wider_last_zero_free_short_G_lower
    {x : ℝ} (hx : x ∈ Set.Icc (11 * Real.pi) (12 * Real.pi))
    (hnearLeft : -widerRadius < x - 12 * Real.pi)
    (hfar : widerRadius ≤ |x - firstSixRoot 5|) :
    widerDerivativeLower 6 * widerRadius ≤ |endpointG x| := by
  let e : ℝ := x - 12 * Real.pi
  let eps : ℝ := firstSixOffset 5
  let L : ℝ := widerDerivativeLower 6
  have he : e ∈ Set.Icc (-Real.pi) 0 := by
    dsimp [e]
    constructor <;> linarith
  have heps := firstSixOffset_mem 5
  have hrootEq : firstSixRoot 5 = 12 * Real.pi + eps := by
    simpa [eps, firstSixIndex] using firstSixRoot_eq 5
  have hdistEq : x - firstSixRoot 5 = e - eps := by
    rw [hrootEq]
    dsimp [e]
    ring
  have heroot : e ≤ eps := by nlinarith [he.2, heps.1]
  have hfar' := hfar
  rw [hdistEq, abs_of_nonpos (sub_nonpos.mpr heroot)] at hfar'
  have hlen : widerRadius ≤ eps - e := hfar'
  have helow : -(1 : ℝ) / 8 ≤ e := by
    simpa [e, widerRadius] using hnearLeft.le
  have heupper : eps ≤ (21 : ℝ) / 40 := by nlinarith [heps.2]
  have hLpos : 0 < L := by
    simpa [L, firstSixIndex] using widerDerivativeLower_pos (5 : Fin 6)
  have hconstInt : IntervalIntegrable (fun _ : ℝ => L) volume e eps :=
    intervalIntegrable_const
  have hderivInt : IntervalIntegrable (offsetNumeratorDerivative 6)
      volume e eps :=
    Continuous.intervalIntegrable
      (by unfold offsetNumeratorDerivative; fun_prop) e eps
  have hmono :
      (∫ _u in e..eps, L) ≤
        ∫ u in e..eps, offsetNumeratorDerivative 6 u := by
    refine intervalIntegral.integral_mono_on heroot hconstInt hderivInt ?_
    intro u hu
    apply wider_offset_derivative_lower (n := 6) (by norm_num)
    exact ⟨helow.trans hu.1, hu.2.trans heupper⟩
  have hint := integral_offsetNumeratorDerivative 6 e eps
  have hroot : offsetNumerator 6 eps = 0 := by
    simpa [eps, firstSixIndex] using firstSixOffset_numerator_zero (5 : Fin 6)
  rw [intervalIntegral.integral_const, smul_eq_mul, hint, hroot, zero_sub] at hmono
  have hnumNeg : offsetNumerator 6 e < 0 := by
    have hpositive : 0 < L * (eps - e) :=
      mul_pos hLpos (lt_of_lt_of_le widerRadius_pos hlen)
    nlinarith
  have hnum : L * widerRadius ≤ |offsetNumerator 6 e| := by
    rw [abs_of_neg hnumNeg]
    nlinarith
  have hxrepr : 12 * Real.pi + e = x := by
    dsimp [e]
    ring
  have hGid := endpointG_abs_eq_offsetNumerator_abs 6 e
  have hcoord : 2 * Real.pi * (6 : ℝ) + e = x := by
    rw [hxrepr]
    ring
  rw [hcoord] at hGid
  rw [hGid]
  simpa [L] using hnum

theorem wider_last_zero_free_short_K_lower
    {x : ℝ} (hx : x ∈ Set.Icc (11 * Real.pi) (12 * Real.pi))
    (hnearLeft : -widerRadius < x - 12 * Real.pi)
    (hfar : widerRadius ≤ |x - firstSixRoot 5|) :
    widerCorrelationThreshold < |endpointK x| := by
  let D : ℝ := ((264 : ℝ) / 7) ^ 2
  have hpiUpper : Real.pi < (22 : ℝ) / 7 := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h
  have hxpos : 0 < x := lt_of_lt_of_le (by
    nlinarith [Real.pi_gt_three]) hx.1
  have hxlarge : 2 < x := by nlinarith
  have hxupper : x < (264 : ℝ) / 7 := hx.2.trans_lt (by nlinarith)
  have hdenpos : 0 < x ^ 2 - 2 := by nlinarith
  have hdenD : x ^ 2 - 2 < D := by
    have hprod : 0 < ((264 : ℝ) / 7 - x) * ((264 : ℝ) / 7 + x) :=
      mul_pos (sub_pos.mpr hxupper) (add_pos (by norm_num) hxpos)
    dsimp [D]
    nlinarith
  have hxne : x ^ 2 ≠ 2 := by nlinarith
  have hG := wider_last_zero_free_short_G_lower hx hnearLeft hfar
  have hK := endpointK_abs_lower_of_G
    (x := x) (D := D) hxne hdenpos hdenD
  have hfactor : 0 ≤ ((3 : ℝ) / 2) / D := by
    dsimp [D]
    positivity
  calc
    widerCorrelationThreshold
        < ((3 : ℝ) / 2) / D *
            (widerDerivativeLower 6 * widerRadius) := by
          simpa [D] using wider_last_zero_free_short_rational
    _ ≤ ((3 : ℝ) / 2) / D * |endpointG x| :=
      mul_le_mul_of_nonneg_left hG hfactor
    _ ≤ |endpointK x| := hK

/-- The entire final half-period is excluded unless the point lies within
`1/8` of the sixth root. -/
theorem wider_final_half_interval_localizes
    {x : ℝ} (hx : x ∈ Set.Icc (11 * Real.pi) (12 * Real.pi))
    (hsmall : |endpointK x| < widerCorrelationThreshold) :
    |x - firstSixRoot 5| < widerRadius := by
  by_contra hnot
  have hfar : widerRadius ≤ |x - firstSixRoot 5| := le_of_not_gt hnot
  by_cases hleft : x - 12 * Real.pi ≤ -widerRadius
  · have hK := wider_last_zero_free_far_K_lower hx hleft
    linarith
  · have hK := wider_last_zero_free_short_K_lower hx (lt_of_not_ge hleft) hfar
    linarith

/-! ## Complete cover below `12*pi` -/

theorem wider_positive_half_interval_localizes
    (i : Fin 5) {x : ℝ}
    (hx : x ∈ Set.Icc
      (2 * Real.pi * (((i : ℕ) + 1 : ℕ) : ℝ))
      ((2 * (((i : ℕ) + 1 : ℕ) : ℝ) + 1) * Real.pi))
    (hsmall : |endpointK x| < widerCorrelationThreshold) :
    |x - firstSixRoot ⟨i, Nat.lt_trans i.isLt (by norm_num)⟩| <
      widerRadius := by
  let j : Fin 6 := ⟨i, Nat.lt_trans i.isLt (by norm_num)⟩
  let n : ℕ := (i : ℕ) + 1
  let e : ℝ := x - 2 * Real.pi * (n : ℝ)
  have he : e ∈ Set.Icc (0 : ℝ) Real.pi := by
    dsimp [e, n]
    constructor <;> nlinarith [hx.1, hx.2]
  have hnear : |e - firstSixOffset j| < widerRadius := by
    by_contra hnot
    have hfar : widerRadius ≤ |e - firstSixOffset j| := le_of_not_gt hnot
    have hK := wider_positive_interval_outside_radius_K_lower
      i he (by simpa [j] using hfar)
    have hxrepr :
        2 * Real.pi * (((i : ℕ) + 1 : ℕ) : ℝ) + e = x := by
      dsimp [e, n]
      ring
    rw [hxrepr] at hK
    linarith
  have hroot : firstSixRoot j =
      2 * Real.pi * (n : ℝ) + firstSixOffset j := by
    have h := firstSixRoot_eq j
    simpa [j, n, firstSixIndex] using h
  change |x - firstSixRoot j| < widerRadius
  rw [hroot]
  dsimp [e, n] at hnear
  convert hnear using 1 <;> ring

/-- Every point of `[0,12*pi]` with endpoint kernel below
`1815107/989072150` lies in one
of the six certified radius-`1/8` neighborhoods. -/
theorem small_endpointK_localizes_first_six
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (12 * Real.pi))
    (hsmall : |endpointK x| < widerCorrelationThreshold) :
    ∃ i : Fin 6, |x - firstSixRoot i| < widerRadius := by
  by_cases h1 : x ≤ Real.pi
  · have hK := endpointK_initial_interval_lower ⟨hx.1, h1⟩
    have hKabs : (165 : ℝ) / 512 ≤ |endpointK x| :=
      hK.trans (le_abs_self (endpointK x))
    exfalso
    norm_num [widerCorrelationThreshold] at hsmall hKabs
    linarith
  have hpi : Real.pi ≤ x := (not_le.mp h1).le
  by_cases h2 : x ≤ 2 * Real.pi
  · have hgap := wider_zero_free_interval_K_lower
      (i := (0 : Fin 5)) (x := x) (by
        simpa using (show x ∈ Set.Icc Real.pi (2 * Real.pi) from ⟨hpi, h2⟩))
    exfalso
    linarith
  have h2pi : 2 * Real.pi ≤ x := (not_le.mp h2).le
  by_cases h3 : x ≤ 3 * Real.pi
  · refine ⟨0, ?_⟩
    change |x - firstSixRoot (0 : Fin 6)| < widerRadius
    exact wider_positive_half_interval_localizes
      (i := (0 : Fin 5)) ⟨h2pi, h3⟩ hsmall
  have h3pi : 3 * Real.pi ≤ x := (not_le.mp h3).le
  by_cases h4 : x ≤ 4 * Real.pi
  · have hgap := wider_zero_free_interval_K_lower
      (i := (1 : Fin 5)) (x := x) (by
        simpa using (show x ∈ Set.Icc (3 * Real.pi) (4 * Real.pi) from
          ⟨h3pi, h4⟩))
    exfalso
    linarith
  have h4pi : 4 * Real.pi ≤ x := (not_le.mp h4).le
  by_cases h5 : x ≤ 5 * Real.pi
  · refine ⟨1, ?_⟩
    change |x - firstSixRoot (1 : Fin 6)| < widerRadius
    exact wider_positive_half_interval_localizes
      (i := (1 : Fin 5)) ⟨h4pi, h5⟩ hsmall
  have h5pi : 5 * Real.pi ≤ x := (not_le.mp h5).le
  by_cases h6 : x ≤ 6 * Real.pi
  · have hgap := wider_zero_free_interval_K_lower
      (i := (2 : Fin 5)) (x := x) (by
        simpa using (show x ∈ Set.Icc (5 * Real.pi) (6 * Real.pi) from
          ⟨h5pi, h6⟩))
    exfalso
    linarith
  have h6pi : 6 * Real.pi ≤ x := (not_le.mp h6).le
  by_cases h7 : x ≤ 7 * Real.pi
  · refine ⟨2, ?_⟩
    change |x - firstSixRoot (2 : Fin 6)| < widerRadius
    exact wider_positive_half_interval_localizes
      (i := (2 : Fin 5)) ⟨h6pi, h7⟩ hsmall
  have h7pi : 7 * Real.pi ≤ x := (not_le.mp h7).le
  by_cases h8 : x ≤ 8 * Real.pi
  · have hgap := wider_zero_free_interval_K_lower
      (i := (3 : Fin 5)) (x := x) (by
        simpa using (show x ∈ Set.Icc (7 * Real.pi) (8 * Real.pi) from
          ⟨h7pi, h8⟩))
    exfalso
    linarith
  have h8pi : 8 * Real.pi ≤ x := (not_le.mp h8).le
  by_cases h9 : x ≤ 9 * Real.pi
  · refine ⟨3, ?_⟩
    change |x - firstSixRoot (3 : Fin 6)| < widerRadius
    exact wider_positive_half_interval_localizes
      (i := (3 : Fin 5)) ⟨h8pi, h9⟩ hsmall
  have h9pi : 9 * Real.pi ≤ x := (not_le.mp h9).le
  by_cases h10 : x ≤ 10 * Real.pi
  · have hgap := wider_zero_free_interval_K_lower
      (i := (4 : Fin 5)) (x := x) (by
        simpa using (show x ∈ Set.Icc (9 * Real.pi) (10 * Real.pi) from
          ⟨h9pi, h10⟩))
    exfalso
    linarith
  have h10pi : 10 * Real.pi ≤ x := (not_le.mp h10).le
  by_cases h11 : x ≤ 11 * Real.pi
  · refine ⟨4, ?_⟩
    change |x - firstSixRoot (4 : Fin 6)| < widerRadius
    exact wider_positive_half_interval_localizes
      (i := (4 : Fin 5)) ⟨h10pi, h11⟩ hsmall
  have h11pi : 11 * Real.pi ≤ x := (not_le.mp h11).le
  refine ⟨5, ?_⟩
  change |x - firstSixRoot (5 : Fin 6)| < widerRadius
  exact wider_final_half_interval_localizes ⟨h11pi, hx.2⟩ hsmall

/-- Normalization at the origin only enlarges absolute correlations. -/
theorem small_endpointR_localizes_first_six
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (12 * Real.pi))
    (hsmall : |endpointR x| < widerCorrelationThreshold) :
    ∃ i : Fin 6, |x - firstSixRoot i| < widerRadius := by
  apply small_endpointK_localizes_first_six hx
  exact lt_of_le_of_lt (endpointK_abs_le_endpointR_abs x) hsmall

end StrictImprovement
end Zeta23

end
