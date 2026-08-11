/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaWiderStrictSeamEventually
import Zeta23.ThmD.Mult

/-!
# The concrete width-six zeta package at fixed lambda

This specializes the four-point machinery to Mathlib's zeta zero
configuration.  It supplies the wider strict seam, its explicit linear gain,
and the unchanged frozen tail-rate interface at every admissible fixed taper.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Filter Asymptotics Topology Real Matrix RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

/-- Abbreviation for the complete finite-height width-six strict seam. -/
def WiderStrictSeamAt (Z : ZeroConfig) (P : Params) (theta₀ : ℝ → ℝ)
    (T : ℝ) : Prop :=
  4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
      frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
      2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ) -
      theta₀ T / ((P.atD T).a T * (P.atD T).L T) *
        (4 + 2 * Real.sqrt
            (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
          theta₀ T / ((P.atD T).a T * (P.atD T).L T)) +
      widerAtDCoreGain Z T P
    ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3

/-- Concrete fixed-`lam`, fixed-internal-epsilon wider strict package. -/
theorem zeta_wider_strict_package_fixed_lam
    {lam delta₀ eps : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (heps : 0 < eps)
    (hH : 0 < ThmD.HD lam - eps)
    (hdelta₀ : 0 ≤ delta₀)
    (hdeltaLim : delta₀ < widerDeltaLower - 18 * (1 - lam))
    (hq0 : 0 ≤ ThmD.HD lam - eps - (lam + eps) / 2 - eps) :
    let P := paramsOf stdProfile lam
    ∃ theta₀ : ℝ → ℝ,
      (∀ᶠ T in atTop,
        Assembly.TailInputs zetaZeroConfig (P.atD T) T (theta₀ T)) ∧
      (∃ C : ℝ, ∀ᶠ T in atTop,
        theta₀ T ≤ C * l T * T ^ (lam / 2 - 1)) ∧
      (∀ᶠ T in atTop,
        WiderStrictSeamAt zetaZeroConfig P theta₀ T) ∧
      (∀ᶠ T in atTop,
        (delta₀ * (ThmD.HD lam - eps - (lam + eps) / 2 - eps) ^ 2 /
            (8 * (1 + eps))) * (Ncount T (2 * T) : ℝ) ≤
          widerAtDCoreGain zetaZeroConfig T P) := by
  dsimp
  let P : Params := paramsOf stdProfile lam
  have hP : P.Valid := by
    dsimp [P]
    exact paramsOf_valid taperProfile_stdProfile hlam0 hlam1.le
  have hbase : ∀ eps' > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD lam - eps') *
          (zetaZeroConfig.N T (2 * T) : ℝ) ≤
        zetaZeroConfig.N0s T (2 * T) := by
    simpa [P, paramsOf] using ThmD.thmD_simple_mult_lam hlam0 hlam1
  have hconj : ∀ᶠ T in atTop,
      ZeroSide.PhiHatConj T (P.atD T) :=
    Eventually.of_forall fun T z =>
      GzGp.phiHat_conj (P.atD T) T z
  have hNonempty : ∀ᶠ T in atTop,
      Nonempty (CoreSimpleLabel zetaZeroConfig T 3) := by
    apply eventually_core_nonempty_from_simple_epsilon_form
      zetaZeroConfig paperInputs_zeta.RvM (fun T => P.atD T)
      hconj (H := ThmD.HD lam)
    · linarith
    · exact hbase
  obtain ⟨theta₀, hTail, htheta⟩ :=
    ThmD.eventually_tailPackageD zetaZeroConfig paperInputs_zeta hP
  have hdeltaPos : 18 * (1 - P.lam) < widerDeltaLower := by
    have hpos : 0 < widerDeltaLower - 18 * (1 - lam) :=
      hdelta₀.trans_lt hdeltaLim
    have : 18 * (1 - lam) < widerDeltaLower := by linarith
    simpa [P, paramsOf] using this
  have hseam := eventually_seamA_mult2_atD_with_wider_explicit_gain
    zetaZeroConfig P hP theta₀ hTail hNonempty hdeltaPos
  have hgain := eventually_widerAtDCoreGain_ge_fixed_eps
    zetaZeroConfig paperInputs_zeta.RvM P hP hconj
    hbase heps hH hdelta₀ (by simpa [P, paramsOf] using hdeltaLim)
      (by simpa [P, paramsOf] using hq0)
  refine ⟨theta₀, hTail, ?_, ?_, ?_⟩
  · simpa [P, paramsOf] using htheta
  · simpa [WiderStrictSeamAt] using hseam
  · simpa [P, paramsOf] using hgain

end StrictImprovement
end Zeta23

end
