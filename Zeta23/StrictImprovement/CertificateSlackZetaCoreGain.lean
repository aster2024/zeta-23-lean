/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.CertificateSlackZetaAtD
import Zeta23.StrictImprovement.ZetaCoreDensity
import Zeta23.StrictImprovement.ZetaDensityTransfer
import Zeta23.StrictImprovement.WiderQuadraticGain

/-!
# Linear density supplied by the full-certificate spectral packing
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace StrictImprovement

/-- Exact quadratic gain for bins of width `264/7`. -/
def certificateSlackSpectralAtDCoreGain
    (Z : ZeroConfig) (T : ℝ) (P : Params) (m : ℝ) : ℝ :=
  m / (16 * (Fintype.card (CoreSimpleLabel Z T 3) : ℝ)) *
    max 0 ((Fintype.card (CoreSimpleLabel Z T 3) : ℝ) -
      (7 * Real.pi / 44) * coreBinD T (P.atD T) - 3) ^ 2

/-- Abstract density lower bound with packing loss `(7*pi/44)D`. -/
theorem eventually_certificateSlackSpectralAtDCoreGain_ge_of_bounds
    (Z : ZeroConfig) (P : Params) {m h d r u q : ℝ}
    (hm : 0 ≤ m) (hh : 0 < h) (hu : 0 < u)
    (hq : q = h - (7 * Real.pi / 44) * d - r) (hq0 : 0 ≤ q)
    (hN : ∀ᶠ T in atTop, 0 < (Z.N T (2 * T) : ℝ))
    (hslo : ∀ᶠ T in atTop,
      h * (Z.N T (2 * T) : ℝ) ≤
        (Fintype.card (CoreSimpleLabel Z T 3) : ℝ))
    (hshi : ∀ᶠ T in atTop,
      (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) ≤
        u * (Z.N T (2 * T) : ℝ))
    (hD : ∀ᶠ T in atTop,
      coreBinD T (P.atD T) ≤ d * (Z.N T (2 * T) : ℝ))
    (hconst : ∀ᶠ T in atTop, 3 ≤ r * (Z.N T (2 * T) : ℝ)) :
    ∀ᶠ T in atTop,
      (m * q ^ 2 / (16 * u)) * (Z.N T (2 * T) : ℝ) ≤
        certificateSlackSpectralAtDCoreGain Z T P m := by
  filter_upwards [hN, hslo, hshi, hD, hconst]
    with T hNT hsloT hshiT hDT hconstT
  let s : ℝ := Fintype.card (CoreSimpleLabel Z T 3)
  let Dparam : ℝ := (7 * Real.pi / 22) * coreBinD T (P.atD T)
  let dparam : ℝ := (7 * Real.pi / 22) * d
  have hcoef : 0 ≤ (7 * Real.pi / 22 : ℝ) := by positivity
  have hs : 0 < s := by
    have : 0 < h * (Z.N T (2 * T) : ℝ) := mul_pos hh hNT
    exact this.trans_le hsloT
  have hDT' : Dparam ≤ dparam * (Z.N T (2 * T) : ℝ) := by
    dsimp [Dparam, dparam]
    calc
      (7 * Real.pi / 22) * coreBinD T (P.atD T)
          ≤ (7 * Real.pi / 22) *
              (d * (Z.N T (2 * T) : ℝ)) := mul_le_mul_of_nonneg_left hDT hcoef
      _ = ((7 * Real.pi / 22) * d) *
          (Z.N T (2 * T) : ℝ) := by ring
  have hq' : q = h - dparam / 2 - r := by
    calc
      q = h - (7 * Real.pi / 44) * d - r := hq
      _ = h - dparam / 2 - r := by
        dsimp [dparam]
        ring
  have hgain := wider_quadratic_core_gain_lower
    hs hNT hu (show 0 ≤ m / 2 by positivity) (le_refl (m / 2))
    hsloT hshiT hDT' hconstT hq' hq0
  have hDhalf : Dparam / 2 =
      (7 * Real.pi / 44) * coreBinD T (P.atD T) := by
    dsimp [Dparam]
    ring
  calc
    (m * q ^ 2 / (16 * u)) * (Z.N T (2 * T) : ℝ) =
        ((m / 2) * q ^ 2 / (8 * u)) *
          (Z.N T (2 * T) : ℝ) := by ring
    _ ≤ (m / 2) / (8 * s) *
        max 0 (s - Dparam / 2 - 3) ^ 2 := hgain
    _ = certificateSlackSpectralAtDCoreGain Z T P m := by
      rw [hDhalf]
      dsimp [certificateSlackSpectralAtDCoreGain, s]
      ring

/-- Concrete fixed-epsilon gain for the widened rational bins. -/
theorem eventually_certificateSlackSpectralAtDCoreGain_ge_fixed_eps
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z)
    (P : Params) (hP : P.Valid)
    (hconj : ∀ᶠ T in atTop, ZeroSide.PhiHatConj T (P.atD T))
    {H m eps : ℝ}
    (hbase : ∀ eps' > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (H - eps') * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T))
    (heps : 0 < eps)
    (hH : 0 < H - eps)
    (hm : 0 ≤ m)
    (hq0 : 0 ≤ H - eps -
      (7 * Real.pi / 44) * (P.lam + eps) - eps) :
    ∀ᶠ T in atTop,
      (m * (H - eps - (7 * Real.pi / 44) * (P.lam + eps) - eps) ^ 2 /
          (16 * (1 + eps))) * (Z.N T (2 * T) : ℝ) ≤
        certificateSlackSpectralAtDCoreGain Z T P m := by
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
      3 ≤ eps * (Z.N T (2 * T) : ℝ) := by
    filter_upwards [hNtop.eventually_ge_atTop (3 / eps)] with T h
    have h' : 3 ≤ (Z.N T (2 * T) : ℝ) * eps :=
      (div_le_iff₀ heps).mp h
    nlinarith
  exact eventually_certificateSlackSpectralAtDCoreGain_ge_of_bounds Z P
    hm hH (by linarith) rfl hq0 hN hslo hshi hD hconst

end StrictImprovement
end Zeta23

end
