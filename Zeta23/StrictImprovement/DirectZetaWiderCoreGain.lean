/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.DirectZetaWiderAtD
import Zeta23.StrictImprovement.ZetaCoreDensity
import Zeta23.StrictImprovement.ZetaDensityTransfer
import Zeta23.StrictImprovement.WiderQuadraticGain

/-!
# Linear density supplied by the direct four-point certificate
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace StrictImprovement

/-- The exact quadratic gain associated with the direct four-point local
defect. -/
def directAtDCoreGain (Z : ZeroConfig) (T : ℝ) (P : Params) : ℝ :=
  directAtDLocalDelta T P /
      (8 * (Fintype.card (CoreSimpleLabel Z T 3) : ℝ)) *
    max 0 ((Fintype.card (CoreSimpleLabel Z T 3) : ℝ) -
      coreBinD T (P.atD T) / 2 - 3) ^ 2

/-- Abstract lower bound for the direct quadratic gain. -/
theorem eventually_directAtDCoreGain_ge_of_bounds
    (Z : ZeroConfig) (P : Params)
    {delta₀ h d r u q : ℝ}
    (hdelta₀ : 0 ≤ delta₀) (hh : 0 < h) (hu : 0 < u)
    (hq : q = h - d / 2 - r) (hq0 : 0 ≤ q)
    (hN : ∀ᶠ T in atTop, 0 < (Z.N T (2 * T) : ℝ))
    (hdelta : ∀ᶠ T in atTop, delta₀ ≤ directAtDLocalDelta T P)
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
      (delta₀ * q ^ 2 / (8 * u)) * (Z.N T (2 * T) : ℝ) ≤
        directAtDCoreGain Z T P := by
  filter_upwards [hN, hdelta, hslo, hshi, hD, hconst]
    with T hNT hdeltaT hsloT hshiT hDT hconstT
  let s : ℝ := Fintype.card (CoreSimpleLabel Z T 3)
  have hs : 0 < s := by
    have : 0 < h * (Z.N T (2 * T) : ℝ) := mul_pos hh hNT
    exact this.trans_le hsloT
  have hgain := wider_quadratic_core_gain_lower
    hs hNT hu hdelta₀ hdeltaT hsloT hshiT hDT hconstT hq hq0
  simpa [directAtDCoreGain, s] using hgain

/-- Concrete fixed-epsilon direct gain. -/
theorem eventually_directAtDCoreGain_ge_fixed_eps
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z)
    (P : Params) (hP : P.Valid)
    (hconj : ∀ᶠ T in atTop, ZeroSide.PhiHatConj T (P.atD T))
    {H delta₀ eps : ℝ}
    (hbase : ∀ eps' > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (H - eps') * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T))
    (heps : 0 < eps)
    (hH : 0 < H - eps)
    (hdelta₀ : 0 ≤ delta₀)
    (hdeltaLim : delta₀ <
      directFourEnergyLower / 2 - 18 * (1 - P.lam))
    (hq0 : 0 ≤ H - eps - (P.lam + eps) / 2 - eps) :
    ∀ᶠ T in atTop,
      (delta₀ * (H - eps - (P.lam + eps) / 2 - eps) ^ 2 /
          (8 * (1 + eps))) * (Z.N T (2 * T) : ℝ) ≤
        directAtDCoreGain Z T P := by
  have hNtop := Assembly.tendsto_N_atTop Z hR
  have hN : ∀ᶠ T in atTop, 0 < (Z.N T (2 * T) : ℝ) :=
    hNtop.eventually_gt_atTop 0
  have hdelta : ∀ᶠ T in atTop, delta₀ ≤ directAtDLocalDelta T P :=
    (eventually_directAtDLocalDelta_gt hP hdeltaLim).mono fun T h => h.le
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
  exact eventually_directAtDCoreGain_ge_of_bounds Z P
    hdelta₀ hH (by linarith) rfl hq0 hN hdelta hslo hshi hD hconst

end StrictImprovement
end Zeta23

end
