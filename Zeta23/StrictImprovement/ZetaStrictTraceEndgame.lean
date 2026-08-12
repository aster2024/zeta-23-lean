/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaStrictEndgame
import Zeta23.StrictImprovement.ZetaStrictFixedLambda

/-!
# Theorem-D trace endgame with the strict gain retained

This is the strict analogue of `ThmD.thmD_mult2_abstract`.  The frozen proof
is reused term for term, except that

* the positive quadratic gain is retained on the left;
* the width-three boundary is retained on the right and separately required
  to be `o(N)`.

Thus neither new term can be hidden inside the old seam/trace error.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace Zeta23
namespace StrictImprovement

open Assembly

/-- Multiplicity-aware Theorem D, `c=2`, with a retained linear gain. -/
theorem strict_thmD_mult2_abstract
    (Z : ZeroConfig) (Hpaper : PaperInputs Z)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : ThmD.TracesBoundsD P aT bT JT trG trG2
      (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto
      (fun T => ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T))
      atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (theta₀ : ℝ → ℝ)
    (hTail : ∀ᶠ T in atTop,
      TailInputs Z (P.atD T) T (theta₀ T))
    (htheta₀ : ∃ C : ℝ, ∀ᶠ T in atTop,
      theta₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop,
      (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop,
      Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = trG T ∧
      (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0))
    (gain boundary : ℝ → ℝ) {eta : ℝ}
    (hSeam : ∀ᶠ T in atTop,
      4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
          frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
          2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ) -
          theta₀ T / ((P.atD T).a T * (P.atD T).L T) *
            (4 + 2 * Real.sqrt
                (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
              theta₀ T / ((P.atD T).a T * (P.atD T).L T)) +
          gain T
        ≤ Z.N0s T (2 * T) + boundary T)
    (hboundary : boundary =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)))
    (hgain : ∀ᶠ T in atTop,
      eta * (Z.N T (2 * T) : ℝ) ≤ gain T) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - c⁻¹ + eta - eps) * (Z.N T (2 * T) : ℝ) ≤
        Z.N0s T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Ctheta, htheta⟩ := htheta₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T =>
    (ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T =>
    C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => theta₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T =>
    (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ) +
      B T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) +
        |cinv T - c⁻¹| * N T with herr
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  have hmain : ∀ᶠ T in atTop,
      (2 - c⁻¹) * N T - err T + gain T ≤
        (Z.N0s T (2 * T) : ℝ) + boundary T := by
    filter_upwards [hSeam, hTail, hGzGp, hId, ha,
        eventually_ge_atTop T₁, eventually_ge_atTop T₂,
        eventually_ge_atTop (0 : ℝ), Assembly.eventually_l_pos,
        Assembly.eventually_calE_nonneg P hlam0
          (zero_le_one.trans hP.one_le_w)]
      with T hA hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos : 0 < aT T := by linarith [ha2.1]
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) =
        (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]
      rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) =
        ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]
      rfl
    have haL : (P.atD T).a T * (P.atD T).L T =
        aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA
    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      ThmD.trGhat_sub_N_le hapos hLpos (by simpa only using htr1 T hT₁)
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤
        cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤
          C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have heq : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T =
          trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [heq]
      simp only [hR₂]
      linarith
    have hB0 : 0 ≤ B T :=
      div_nonneg hTl.theta_nonneg (mul_pos hapos hLpos).le
    have hstrict := N0simple_lower_c_with_gain hB0 hA htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hdrift :
        (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤
          (2 - cinv T) * N T := by
      have hmul := mul_le_mul_of_nonneg_right
        (le_abs_self (cinv T - c⁻¹)) hN0
      linarith
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at hstrict hdrift ⊢
    linarith
  have hNtop : Tendsto N atTop atTop := Assembly.tendsto_N_atTop Z Hpaper.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1 : ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]
      nlinarith [ha2.1]
    have h := isLittleO_of_bdd_mul hbd
      (Assembly.isLittleO_N_of_isLittleO_Tl Z Hpaper.RvM
        (Assembly.isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact h.congr_left fun T => by simp only [hR₁]; ring
  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually
        (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))]
      with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1 : ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]
    exact h.2
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have h := hcinvO.mul (isBigO_refl N atTop)
      simpa using h
    have h := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (h.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop]
        (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, Assembly.eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO
      (Assembly.isLittleO_N_of_isLittleO_Tl Z Hpaper.RvM
        Assembly.isLittleO_sqrt_mul_l_Tl)
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto
        (fun T => 2 * |Ctheta| *
          (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (Assembly.tendsto_theta_over_L P hlam0 hlam1).const_mul
        (2 * |Ctheta|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, Assembly.eventually_l_pos]
        with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, Assembly.eventually_l_pos, htheta,
          eventually_gt_atTop (0 : ℝ)]
        with T hTl ha2 hl hthetaT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos hLpos)]
      calc
        theta₀ T ≤ Ctheta * l T * T ^ (P.lam / 2 - 1) := hthetaT
        _ ≤ |Ctheta| * l T * T ^ (P.lam / 2 - 1) := by
          gcongr
          exact le_abs_self _
        _ = |Ctheta| *
            (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by
          field_simp
        _ ≤ (2 * |Ctheta| *
            (l T * T ^ (P.lam / 2 - 1) / P.L T)) *
              (aT T * P.L T) := by
          have heq : |Ctheta| *
              (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T =
            (2 * |Ctheta| *
              (l T * T ^ (P.lam / 2 - 1) / P.L T)) *
                (1 / 2 * P.L T) := by ring
          rw [heq]
          gcongr
          exact ha2.1
  have o5 := Assembly.err_isLittleO
    (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ))
    (B := B) (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have hzero : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using hzero.abs
  have herr_o : err =o[atTop] N := o5.add o6
  have hNnonneg : ∀ᶠ T in atTop, 0 ≤ N T :=
    Eventually.of_forall fun T => Nat.cast_nonneg _
  have hfinal := eps_form_of_isLittleO_with_gain
    hmain hNnonneg herr_o
      (by simpa [hNdef] using hboundary)
      (by simpa [hNdef] using hgain)
  simpa [hNdef, add_assoc] using hfinal

end StrictImprovement
end Zeta23

end
