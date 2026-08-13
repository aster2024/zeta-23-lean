/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.CertificateSlackZetaStrictSeamEventually
import Zeta23.ThmD.Mult

/-!
# Full-certificate zeta package at fixed taper
-/

noncomputable section

open Filter Asymptotics Topology Real Matrix RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

/-- Abbreviation for the widened-bin finite-height spectral seam. -/
def CertificateSlackSpectralStrictSeamAt (Z : ZeroConfig) (P : Params)
    (theta0 : ℝ → ℝ) (m T : ℝ) : Prop :=
  4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
      frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
      2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ) -
      theta0 T / ((P.atD T).a T * (P.atD T).L T) *
        (4 + 2 * Real.sqrt
            (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
          theta0 T / ((P.atD T).a T * (P.atD T).L T)) +
      certificateSlackSpectralAtDCoreGain Z T P m
    ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3

/-- Complete fixed-taper package relative to the explicit full-domain
spectral certificate. -/
theorem zeta_certificate_slack_spectral_strict_package_fixed_lam
    (hcertificate : SpectralFourEndpointSlackCertificate)
    {lam m eps : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (heps : 0 < eps)
    (hH : 0 < ThmD.HD lam - eps)
    (hm : 0 ≤ m)
    (hmarginLim : Real.sqrt m + 6 * Real.sqrt 3 * (1 - lam) <
      Real.sqrt spectralFourMassLower)
    (hq0 : 0 ≤ ThmD.HD lam - eps -
      (7 * Real.pi / 44) * (lam + eps) - eps) :
    let P := paramsOf stdProfile lam
    ∃ theta0 : ℝ → ℝ,
      (∀ᶠ T in atTop,
        Assembly.TailInputs zetaZeroConfig (P.atD T) T (theta0 T)) ∧
      (∃ C : ℝ, ∀ᶠ T in atTop,
        theta0 T ≤ C * l T * T ^ (lam / 2 - 1)) ∧
      (∀ᶠ T in atTop,
        CertificateSlackSpectralStrictSeamAt
          zetaZeroConfig P theta0 m T) ∧
      (∀ᶠ T in atTop,
        (m * (ThmD.HD lam - eps -
              (7 * Real.pi / 44) * (lam + eps) - eps) ^ 2 /
            (16 * (1 + eps))) * (Ncount T (2 * T) : ℝ) ≤
          certificateSlackSpectralAtDCoreGain zetaZeroConfig T P m) := by
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
  obtain ⟨theta0, hTail, htheta⟩ :=
    ThmD.eventually_tailPackageD zetaZeroConfig paperInputs_zeta hP
  have hseam :=
    eventually_seamA_mult2_atD_with_certificate_slack_spectral_gain
      hcertificate zetaZeroConfig P hP theta0 hTail hNonempty hm
        (by simpa [P, paramsOf] using hmarginLim)
  have hgain := eventually_certificateSlackSpectralAtDCoreGain_ge_fixed_eps
    zetaZeroConfig paperInputs_zeta.RvM P hP hconj
    hbase heps hH hm (by simpa [P, paramsOf] using hq0)
  refine ⟨theta0, hTail, ?_, ?_, ?_⟩
  · simpa [P, paramsOf] using htheta
  · simpa [CertificateSlackSpectralStrictSeamAt] using hseam
  · simpa [P, paramsOf] using hgain

end StrictImprovement
end Zeta23

end
