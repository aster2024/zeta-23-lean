/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WideRepairZetaLocalDefect
import Zeta23.StrictImprovement.ZetaCoreDensity
import Zeta23.StrictImprovement.ZetaDensityTransfer

/-! # Linear density supplied by the mixed repaired packing -/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace StrictImprovement

theorem wideRepair_quadratic_core_gain_lower
    {s N D scale h d r u q : ℝ}
    (hs : 0 < s) (hN : 0 < N) (hu : 0 < u)
    (hscale : 0 ≤ scale)
    (hslo : h * N ≤ s) (hshi : s ≤ u * N)
    (hD : D ≤ d * N) (hconst : (13 : ℝ) / 5 ≤ r * N)
    (hq : q = h - (13 : ℝ) / 40 * d - r) (hq0 : 0 ≤ q) :
    scale ^ 2 / (25600 * s) *
        max 0 (s - (13 : ℝ) / 40 * D - 13 / 5) ^ 2 ≥
      scale ^ 2 * q ^ 2 / (25600 * u) * N := by
  have hqN0 : 0 ≤ q * N := mul_nonneg hq0 hN.le
  have ha : q * N ≤ s - (13 : ℝ) / 40 * D - 13 / 5 := by
    rw [hq]
    nlinarith
  have ha0 : 0 ≤ s - (13 : ℝ) / 40 * D - 13 / 5 := hqN0.trans ha
  rw [max_eq_right ha0]
  have hsq : (q * N) ^ 2 ≤
      (s - (13 : ℝ) / 40 * D - 13 / 5) ^ 2 :=
    pow_le_pow_left₀ hqN0 ha 2
  have hscaleSq : 0 ≤ scale ^ 2 := sq_nonneg _
  have hnum : scale ^ 2 * (q * N) ^ 2 ≤
      scale ^ 2 * (s - (13 : ℝ) / 40 * D - 13 / 5) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hscaleSq
  rw [show scale ^ 2 / (25600 * s) *
      (s - (13 : ℝ) / 40 * D - 13 / 5) ^ 2 =
      scale ^ 2 * (s - (13 : ℝ) / 40 * D - 13 / 5) ^ 2 /
        (25600 * s) by ring]
  apply (le_div_iff₀ (mul_pos (by norm_num) hs)).2
  calc
    scale ^ 2 * q ^ 2 / (25600 * u) * N * (25600 * s) =
        scale ^ 2 * q ^ 2 * N * s / u := by
      field_simp [hu.ne']
    _ ≤ scale ^ 2 * q ^ 2 * N * (u * N) / u := by
      gcongr
    _ = scale ^ 2 * (q * N) ^ 2 := by
      field_simp [hu.ne']
    _ ≤ scale ^ 2 *
        (s - (13 : ℝ) / 40 * D - 13 / 5) ^ 2 := hnum

theorem eventually_wideRepairAtDCoreGain_ge_of_bounds
    (Z : ZeroConfig) (P : Params) {scale h d r u q : ℝ}
    (hscale : 0 ≤ scale) (hh : 0 < h) (hu : 0 < u)
    (hq : q = h - (13 : ℝ) / 40 * d - r) (hq0 : 0 ≤ q)
    (hN : ∀ᶠ T in atTop, 0 < (Z.N T (2 * T) : ℝ))
    (hslo : ∀ᶠ T in atTop,
      h * (Z.N T (2 * T) : ℝ) ≤
        (Fintype.card (CoreSimpleLabel Z T 3) : ℝ))
    (hshi : ∀ᶠ T in atTop,
      (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) ≤
        u * (Z.N T (2 * T) : ℝ))
    (hD : ∀ᶠ T in atTop,
      coreBinD T (P.atD T) ≤ d * (Z.N T (2 * T) : ℝ))
    (hconst : ∀ᶠ T in atTop,
      (13 : ℝ) / 5 ≤ r * (Z.N T (2 * T) : ℝ)) :
    ∀ᶠ T in atTop,
      (scale ^ 2 * q ^ 2 / (25600 * u)) *
          (Z.N T (2 * T) : ℝ) ≤
        wideRepairAtDCoreGain Z T P scale := by
  filter_upwards [hN, hslo, hshi, hD, hconst]
    with T hNT hsloT hshiT hDT hconstT
  let s : ℝ := Fintype.card (CoreSimpleLabel Z T 3)
  have hs : 0 < s := by
    have : 0 < h * (Z.N T (2 * T) : ℝ) := mul_pos hh hNT
    exact this.trans_le hsloT
  have hgain := wideRepair_quadratic_core_gain_lower
    hs hNT hu hscale hsloT hshiT hDT hconstT hq hq0
  simpa [wideRepairAtDCoreGain, s] using hgain

theorem eventually_wideRepairAtDCoreGain_ge_fixed_eps
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z)
    (P : Params) (hP : P.Valid)
    (hconj : ∀ᶠ T in atTop, ZeroSide.PhiHatConj T (P.atD T))
    {H scale eps : ℝ}
    (hbase : ∀ eps' > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (H - eps') * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T))
    (heps : 0 < eps)
    (hH : 0 < H - eps)
    (hscale : 0 ≤ scale)
    (hq0 : 0 ≤ H - eps - (13 : ℝ) / 40 * (P.lam + eps) - eps) :
    ∀ᶠ T in atTop,
      (scale ^ 2 *
          (H - eps - (13 : ℝ) / 40 * (P.lam + eps) - eps) ^ 2 /
          (25600 * (1 + eps))) * (Z.N T (2 * T) : ℝ) ≤
        wideRepairAtDCoreGain Z T P scale := by
  have hNtop := Assembly.tendsto_N_atTop Z hR
  have hN : ∀ᶠ T in atTop, 0 < (Z.N T (2 * T) : ℝ) :=
    hNtop.eventually_gt_atTop 0
  have hslo := coreCard_lower_from_simple_epsilon_form Z hR
    (fun T => P.atD T) hconj hbase eps heps
  have hshi := eventually_coreCard_le_one_add Z hR
    (fun T => P.atD T) hconj heps
  have hDraw := eventually_coreBinD_le Z hR P heps
  have hD : ∀ᶠ T in atTop,
      coreBinD T (P.atD T) ≤
        (P.lam + eps) * (Z.N T (2 * T) : ℝ) := by
    filter_upwards [hDraw] with T h
    simpa [coreBinD, Params.atD_L] using h
  have hconst : ∀ᶠ T in atTop,
      (13 : ℝ) / 5 ≤ eps * (Z.N T (2 * T) : ℝ) := by
    filter_upwards [hNtop.eventually_ge_atTop ((13 / 5) / eps)] with T h
    have h' : (13 : ℝ) / 5 ≤ (Z.N T (2 * T) : ℝ) * eps :=
      (div_le_iff₀ heps).mp h
    nlinarith
  exact eventually_wideRepairAtDCoreGain_ge_of_bounds Z P
    hscale hH (by linarith) rfl hq0 hN hslo hshi hD hconst

end StrictImprovement
end Zeta23

end
