/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7FullSpectralZetaStrictSeamEventually
import Zeta23.ThmD.Mult

/-! # Salvaged q7 superbin zeta package at fixed taper -/

noncomputable section

open Filter Asymptotics Topology Real Matrix RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

def Q7FullSpectralStrictSeamAt (Z : ZeroConfig) (P : Params)
    (theta0 : ℝ → ℝ) (scale T : ℝ) : Prop :=
  4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
      frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
      2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ) -
      theta0 T / ((P.atD T).a T * (P.atD T).L T) *
        (4 + 2 * Real.sqrt
            (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
          theta0 T / ((P.atD T).a T * (P.atD T).L T)) +
      q7FullSpectralAtDCoreGain Z T P scale
    ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3

theorem zeta_q7FullSpectral_strict_package_fixed_lam
    (hcertificates : Q7FullSpectralEndpointCertificates)
    {lam scale eps : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (heps : 0 < eps)
    (hH : 0 < ThmD.HD lam - eps)
    (hscale : 0 ≤ scale)
    (hmargin3 : scale * wideRepairRewardThree +
        (9 * Real.sqrt 3 / 2) * (1 - lam) < wideRepairRewardThree)
    (hmargin4 : scale * wideRepairRewardFour +
        6 * Real.sqrt 3 * (1 - lam) < wideRepairRewardFour)
    (hmargin5 : scale * wideRepairRewardFive +
        (15 * Real.sqrt 5 / 2) * (1 - lam) < wideRepairRewardFive)
    (hmargin6 : scale * q7FullSpectralSixReward +
        9 * Real.sqrt 6 * (1 - lam) < q7FullSpectralSixReward)
    (hmargin7 : scale * q7FullSpectralSevenReward +
        (21 * Real.sqrt 7 / 2) * (1 - lam) < q7FullSpectralSevenReward)
    (hq0 : 0 ≤ ThmD.HD lam - eps -
      q7FullSpectralPackingLoss * (lam + eps) - eps) :
    let P := paramsOf stdProfile lam
    ∃ theta0 : ℝ → ℝ,
      (∀ᶠ T in atTop,
        Assembly.TailInputs zetaZeroConfig (P.atD T) T (theta0 T)) ∧
      (∃ C : ℝ, ∀ᶠ T in atTop,
        theta0 T ≤ C * l T * T ^ (lam / 2 - 1)) ∧
      (∀ᶠ T in atTop,
        Q7FullSpectralStrictSeamAt zetaZeroConfig P theta0 scale T) ∧
      (∀ᶠ T in atTop,
        (scale ^ 2 * wideRepairAlpha ^ 2 *
            (ThmD.HD lam - eps -
              q7FullSpectralPackingLoss * (lam + eps) - eps) ^ 2 /
            (1 + eps)) * (Ncount T (2 * T) : ℝ) ≤
          q7FullSpectralAtDCoreGain zetaZeroConfig T P scale) := by
  dsimp
  let P : Params := paramsOf stdProfile lam
  have hP : P.Valid := by
    dsimp [P]
    exact paramsOf_valid taperProfile_stdProfile hlam0 hlam1.le
  have hbase : ∀ eps' > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (ThmD.HD lam - eps') *
          (zetaZeroConfig.N T (2 * T) : ℝ) ≤
        zetaZeroConfig.N0s T (2 * T) := by
    simpa [P, paramsOf] using ThmD.thmD_simple_mult_lam hlam0 hlam1
  have hconj : ∀ᶠ T in atTop, ZeroSide.PhiHatConj T (P.atD T) :=
    Eventually.of_forall fun T z => GzGp.phiHat_conj (P.atD T) T z
  have hNonempty : ∀ᶠ T in atTop,
      Nonempty (CoreSimpleLabel zetaZeroConfig T 3) := by
    apply eventually_core_nonempty_from_simple_epsilon_form
      zetaZeroConfig paperInputs_zeta.RvM (fun T => P.atD T)
      hconj (H := ThmD.HD lam)
    · linarith
    · exact hbase
  obtain ⟨theta0, hTail, htheta⟩ :=
    ThmD.eventually_tailPackageD zetaZeroConfig paperInputs_zeta hP
  have hseam := eventually_seamA_mult2_atD_with_q7FullSpectral_gain
    hcertificates zetaZeroConfig P hP theta0 hTail hNonempty hscale
      (by simpa [P, paramsOf] using hmargin3)
      (by simpa [P, paramsOf] using hmargin4)
      (by simpa [P, paramsOf] using hmargin5)
      (by simpa [P, paramsOf] using hmargin6)
      (by simpa [P, paramsOf] using hmargin7)
  have hgain := eventually_q7FullSpectralAtDCoreGain_ge_fixed_eps
    zetaZeroConfig paperInputs_zeta.RvM P hP hconj
    hbase heps hH hscale (by simpa [P, paramsOf] using hq0)
  refine ⟨theta0, hTail, ?_, ?_, ?_⟩
  · simpa [P, paramsOf] using htheta
  · simpa [Q7FullSpectralStrictSeamAt] using hseam
  · simpa [P, paramsOf] using hgain

end StrictImprovement
end Zeta23

end
