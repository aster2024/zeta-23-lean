/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Functional

/-!
# The endpoint Montgomery--Taylor correlation kernel

This file isolates the exact real Fourier kernel used by the strict simple-zero
candidate.  The apparent poles at `x = ± sqrt 2` are removable; the rational
closed form is therefore stated away from `x ^ 2 = 2`, while positivity of the
normalizing value is proved directly from the already formalized endpoint
profile.

This is a source draft until it has been checked by the pinned Lean toolchain
recorded in `LEAN_FORMALIZATION_PLAN.md`.
-/

noncomputable section

open Real intervalIntegral

namespace Zeta23
namespace StrictImprovement

/-- The real endpoint Fourier kernel
`K(x) = integral_[-1/2,1/2] cos(sqrt 2 * s) cos(x * s) ds`.

The imaginary part of the corresponding complex Fourier integral vanishes by
parity, so this is the real kernel appearing in the Parseval bridge. -/
def endpointK (x : ℝ) : ℝ :=
  ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
    ThmD.vStar 1 s * Real.cos (x * s)

/-- The endpoint kernel normalized at the origin. -/
def endpointR (x : ℝ) : ℝ := endpointK x / endpointK 0

/-- The endpoint constant `kappa = sqrt 2 * tan(1 / sqrt 2)`. -/
def endpointKappa : ℝ :=
  Real.sqrt 2 * Real.tan (ThmD.theta 1)

/-- Numerator of the division-safe closed kernel after extracting the positive
factor `2 cos(theta(1))`. -/
def endpointG (x : ℝ) : ℝ :=
  x * Real.sin (x / 2) - endpointKappa * Real.cos (x / 2)

/-- Tangent form of the root equation on intervals avoiding odd multiples of
`pi`. -/
def endpointRootEquation (x : ℝ) : ℝ := x * Real.tan (x / 2)

/-- Symmetric cosine integral on the unit interval. -/
lemma intervalIntegral_cos_mul (c : ℝ) (hc : c ≠ 0) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (c * s))
      = 2 * Real.sin (c / 2) / c := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos hc, integral_cos,
    smul_eq_mul]
  have hp : c * (1 / 2 : ℝ) = c / 2 := by ring
  have hm : c * (-(1 : ℝ) / 2) = -(c / 2) := by ring
  rw [hp, hm, Real.sin_neg]
  field_simp
  ring

/-- Product-to-sum representation of the endpoint kernel. -/
lemma endpointK_eq_average_integrals (x : ℝ) :
    endpointK x =
      ((∫ s in (-(1 : ℝ) / 2)..(1 / 2),
          Real.cos ((Real.sqrt 2 - x) * s))
        + (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
          Real.cos ((Real.sqrt 2 + x) * s))) / 2 := by
  unfold endpointK ThmD.vStar
  rw [← intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro s _
  change Real.cos (Real.sqrt 2 * 1 * s) * Real.cos (x * s) =
    (Real.cos ((Real.sqrt 2 - x) * s) +
      Real.cos ((Real.sqrt 2 + x) * s)) / 2
  rw [show Real.sqrt 2 * 1 * s = Real.sqrt 2 * s by ring,
    show (Real.sqrt 2 - x) * s = Real.sqrt 2 * s - x * s by ring,
    show (Real.sqrt 2 + x) * s = Real.sqrt 2 * s + x * s by ring,
    Real.cos_sub, Real.cos_add]
  ring

/-- Sine-fraction form of the endpoint kernel away from its two removable
singularities. -/
theorem endpointK_eq_sine_fractions
    {x : ℝ}
    (hminus : Real.sqrt 2 - x ≠ 0)
    (hplus : Real.sqrt 2 + x ≠ 0) :
    endpointK x =
      Real.sin ((Real.sqrt 2 - x) / 2) / (Real.sqrt 2 - x)
        + Real.sin ((Real.sqrt 2 + x) / 2) / (Real.sqrt 2 + x) := by
  rw [endpointK_eq_average_integrals,
    intervalIntegral_cos_mul (Real.sqrt 2 - x) hminus,
    intervalIntegral_cos_mul (Real.sqrt 2 + x) hplus]
  ring

/-- The division-safe closed form used by the root-localization argument. -/
theorem endpointK_closed
    {x : ℝ} (hx : x ^ 2 ≠ 2) :
    endpointK x =
      2 * (x * Real.sin (x / 2) * Real.cos (Real.sqrt 2 / 2)
        - Real.sqrt 2 * Real.cos (x / 2) * Real.sin (Real.sqrt 2 / 2)) /
          (x ^ 2 - 2) := by
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hminus : Real.sqrt 2 - x ≠ 0 := by
    intro h
    have : x = Real.sqrt 2 := by linarith
    apply hx
    rw [this, hsqrt_sq]
  have hplus : Real.sqrt 2 + x ≠ 0 := by
    intro h
    have : x = -Real.sqrt 2 := by linarith
    apply hx
    rw [this, neg_sq, hsqrt_sq]
  rw [endpointK_eq_sine_fractions hminus hplus]
  have harg_minus :
      (Real.sqrt 2 - x) / 2 = Real.sqrt 2 / 2 - x / 2 := by ring
  have harg_plus :
      (Real.sqrt 2 + x) / 2 = Real.sqrt 2 / 2 + x / 2 := by ring
  rw [harg_minus, harg_plus, Real.sin_sub, Real.sin_add]
  field_simp
  ring_nf at hsqrt_sq ⊢
  have hsqrt_cube : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt_sq]
  rw [hsqrt_sq, hsqrt_cube]
  ring

/-- Paper form of the closed expression, with the positive cosine factor and
`kappa` separated. -/
theorem endpointK_closed_kappa
    {x : ℝ} (hx : x ^ 2 ≠ 2) :
    endpointK x =
      2 * Real.cos (ThmD.theta 1) / (x ^ 2 - 2) *
        (x * Real.sin (x / 2) - endpointKappa * Real.cos (x / 2)) := by
  have htheta : ThmD.theta 1 = Real.sqrt 2 / 2 := by
    have h := ThmD.sqrt2_mul_half (lam := (1 : ℝ))
    norm_num at h
    linarith
  have hcos : Real.cos (ThmD.theta 1) ≠ 0 :=
    ne_of_gt (ThmD.cos_theta_pos (lam := (1 : ℝ)) (by norm_num) (by norm_num))
  have hcos' : Real.cos (Real.sqrt 2 / 2) ≠ 0 := by
    rw [← htheta]
    exact hcos
  rw [endpointK_closed hx, endpointKappa, Real.tan_eq_sin_div_cos, htheta]
  field_simp [hcos']

/-- The endpoint root parameter is strictly positive. -/
theorem endpointKappa_pos : 0 < endpointKappa := by
  have htheta_pos : 0 < ThmD.theta 1 :=
    ThmD.theta_pos (lam := (1 : ℝ)) (by norm_num)
  have htheta_lt : ThmD.theta 1 < Real.pi / 2 :=
    ThmD.theta_lt_pi_div_two (lam := (1 : ℝ)) (by norm_num) (by norm_num)
  have htan : 0 < Real.tan (ThmD.theta 1) := by
    have h := Real.lt_tan htheta_pos htheta_lt
    linarith
  unfold endpointKappa
  positivity

/-- Away from the removable points, zeros of the endpoint kernel are exactly
zeros of its scalar numerator `endpointG`. -/
theorem endpointK_eq_zero_iff_endpointG_eq_zero
    {x : ℝ} (hx : x ^ 2 ≠ 2) :
    endpointK x = 0 ↔ endpointG x = 0 := by
  rw [endpointK_closed_kappa hx]
  unfold endpointG
  have hcos : Real.cos (ThmD.theta 1) ≠ 0 :=
    ne_of_gt (ThmD.cos_theta_pos (lam := (1 : ℝ)) (by norm_num) (by norm_num))
  have hden : x ^ 2 - 2 ≠ 0 := sub_ne_zero.mpr hx
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hfactor | hg
    · exact False.elim
        ((div_ne_zero (mul_ne_zero (by norm_num) hcos) hden) hfactor)
    · exact hg
  · intro hg
    rw [hg, mul_zero]

/-- On a point where `cos(x/2)` is nonzero, the numerator equation is the
usual tangent equation `x tan(x/2) = kappa`. -/
theorem endpointG_eq_zero_iff_rootEquation
    {x : ℝ} (hcos : Real.cos (x / 2) ≠ 0) :
    endpointG x = 0 ↔ endpointRootEquation x = endpointKappa := by
  unfold endpointG endpointRootEquation
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  constructor <;> intro h <;> linarith

/-- Exact derivative of the scalar root numerator. -/
theorem hasDerivAt_endpointG (x : ℝ) :
    HasDerivAt endpointG
      ((1 + endpointKappa / 2) * Real.sin (x / 2)
        + x / 2 * Real.cos (x / 2)) x := by
  have harg : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (y / 2))
      (Real.cos (x / 2) * (1 / 2)) x := by
    convert (Real.hasDerivAt_sin (x / 2)).comp x harg using 1 <;> ring
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (y / 2))
      (-Real.sin (x / 2) * (1 / 2)) x := by
    convert (Real.hasDerivAt_cos (x / 2)).comp x harg using 1 <;> ring
  unfold endpointG
  have h := ((hasDerivAt_id x).mul hsin).sub
    (hcos.const_mul endpointKappa)
  simpa only [id_eq] using h.congr_deriv (by ring)

/-- Differentiability of the scalar root numerator. -/
theorem differentiable_endpointG : Differentiable ℝ endpointG := by
  intro x
  exact (hasDerivAt_endpointG x).differentiableAt

/-- Exact value of the normalizing denominator. -/
theorem endpointK_zero :
    endpointK 0 = Real.sqrt 2 * Real.sin (ThmD.theta 1) := by
  have hKa : endpointK 0 = ThmD.aStar 1 := by
    unfold endpointK ThmD.aStar
    simp
  rw [hKa, ThmD.aStar_eq (lam := (1 : ℝ)) (by norm_num)]
  ring

/-- The normalizing denominator is strictly positive. -/
theorem endpointK_zero_pos : 0 < endpointK 0 := by
  rw [endpointK_zero]
  have hsin := ThmD.sin_theta_pos (lam := (1 : ℝ)) (by norm_num) (by norm_num)
  positivity

/-- The endpoint normalizing denominator is at most one.  This is the precise
normalization direction used when a lower bound for `|endpointK x|` is
transferred to `|endpointR x|`. -/
theorem endpointK_zero_le_one : endpointK 0 ≤ 1 := by
  have hsin : Real.sin (ThmD.theta 1) ≤ ThmD.theta 1 :=
    Real.sin_le (ThmD.theta_nonneg (lam := (1 : ℝ)) (by norm_num))
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hmul := mul_le_mul_of_nonneg_left hsin hsqrt_nonneg
  have htheta : ThmD.theta 1 = Real.sqrt 2 / 2 := by
    have h := ThmD.sqrt2_mul_half (lam := (1 : ℝ))
    norm_num at h
    linarith
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [endpointK_zero]
  calc
    Real.sqrt 2 * Real.sin (ThmD.theta 1)
        ≤ Real.sqrt 2 * ThmD.theta 1 := hmul
    _ = 1 := by rw [htheta]; nlinarith

/-- The endpoint cosine weight is nonnegative on its whole support. -/
lemma endpointWeight_nonneg {s : ℝ}
    (hs : s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ ThmD.vStar 1 s := by
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_le_two : Real.sqrt 2 ≤ 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 2)]
  have hlower : -(Real.pi / 2) ≤ Real.sqrt 2 * 1 * s := by
    have hmul := mul_le_mul_of_nonneg_left hs.1 hsqrt_nonneg
    nlinarith [Real.pi_gt_three]
  have hupper : Real.sqrt 2 * 1 * s ≤ Real.pi / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hs.2 hsqrt_nonneg
    nlinarith [Real.pi_gt_three]
  unfold ThmD.vStar
  exact Real.cos_nonneg_of_mem_Icc ⟨hlower, hupper⟩

/-- The absolute value of an endpoint Fourier coefficient is bounded by the
zero-frequency mass of its nonnegative weight. -/
theorem endpointK_abs_le_zero (x : ℝ) : |endpointK x| ≤ endpointK 0 := by
  let f : ℝ → ℝ := fun s => ThmD.vStar 1 s * Real.cos (x * s)
  let w : ℝ → ℝ := fun s => ThmD.vStar 1 s
  have hfcont : Continuous f := by
    dsimp [f]
    unfold ThmD.vStar
    fun_prop
  have hwcont : Continuous w := by
    dsimp [w]
    unfold ThmD.vStar
    fun_prop
  have hpoint : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2), |f s| ≤ w s := by
    intro s hs
    have hw : 0 ≤ w s := by
      dsimp [w]
      exact endpointWeight_nonneg hs
    dsimp [f]
    rw [abs_mul, abs_of_nonneg hw]
    exact mul_le_of_le_one_right hw (Real.abs_cos_le_one (x * s))
  have habs :
      |(∫ s in (-(1 : ℝ) / 2)..(1 / 2), f s)| ≤
        ∫ s in (-(1 : ℝ) / 2)..(1 / 2), |f s| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have hmono :
      (∫ s in (-(1 : ℝ) / 2)..(1 / 2), |f s|) ≤
        ∫ s in (-(1 : ℝ) / 2)..(1 / 2), w s := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      (hfcont.abs.intervalIntegrable _ _) (hwcont.intervalIntegrable _ _) hpoint
  unfold endpointK
  dsimp [f, w] at habs hmono ⊢
  simpa only [zero_mul, Real.cos_zero, mul_one] using habs.trans hmono

/-- Normalization at the origin. -/
@[simp] theorem endpointR_zero : endpointR 0 = 1 := by
  unfold endpointR
  exact div_self (ne_of_gt endpointK_zero_pos)

/-- Since `0 < K(0) ≤ 1`, normalization can only increase absolute values. -/
theorem endpointK_abs_le_endpointR_abs (x : ℝ) :
    |endpointK x| ≤ |endpointR x| := by
  rw [endpointR, abs_div, abs_of_pos endpointK_zero_pos]
  apply (le_div_iff₀ endpointK_zero_pos).2
  exact mul_le_of_le_one_right (abs_nonneg (endpointK x)) endpointK_zero_le_one

/-- Every normalized endpoint correlation has absolute value at most one. -/
theorem endpointR_abs_le_one (x : ℝ) : |endpointR x| ≤ 1 := by
  rw [endpointR, abs_div, abs_of_pos endpointK_zero_pos,
    div_le_one endpointK_zero_pos]
  exact endpointK_abs_le_zero x

/-- The endpoint kernel is even. -/
@[simp] theorem endpointK_neg (x : ℝ) : endpointK (-x) = endpointK x := by
  unfold endpointK
  apply intervalIntegral.integral_congr
  intro s _
  change ThmD.vStar 1 s * Real.cos ((-x) * s) =
    ThmD.vStar 1 s * Real.cos (x * s)
  rw [neg_mul, Real.cos_neg]

/-- The normalized endpoint kernel is even. -/
@[simp] theorem endpointR_neg (x : ℝ) : endpointR (-x) = endpointR x := by
  unfold endpointR
  rw [endpointK_neg]

end StrictImprovement
end Zeta23
