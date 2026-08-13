/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.DirectZetaWiderStrictSeamEventually
import Zeta23.ThmD.Mult

/-!
# Direct-certificate zeta package at fixed taper
-/

noncomputable section

open Filter Asymptotics Topology Real Matrix RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

/-- Abbreviation for the direct finite-height seam. -/
def DirectStrictSeamAt (Z : ZeroConfig) (P : Params) (theta₀ : ℝ → ℝ)
    (T : ℝ) : Prop :=
  4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
      frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
      2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ) -
      theta₀ T / ((P.atD T).a T * (P.atD T).L T) *
        (4 + 2 * Real.sqrt
            (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
          theta₀ T / ((P.atD T).a T * (P.atD T).L T)) +
      directAtDCoreGain Z T P
    ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3

/-- Complete fixed-taper package relative to the explicit direct endpoint
certificate. -/
theorem zeta_direct_strict_package_fixed_lam
    (hcertificate : DirectFourEndpointCertificate)
    {lam delta₀ eps : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (heps : 0 < eps)
    (hH : 0 < ThmD.HD lam - eps)
    (hdelta₀ : 0 ≤ delta₀)
    (hdeltaLim : delta₀ <
      directFourEnergyLower / 2 - 18 * (1 - lam))
    (hq0 : 0 ≤ ThmD.HD lam - eps - (lam + eps) / 2 - eps) :
    let P := paramsOf stdProfile lam
    ∃ theta₀ : ℝ → ℝ,
      (∀ᶠ T in atTop,
        Assembly.TailInputs zetaZeroConfig (P.atD T) T (theta₀ T)) ∧
      (∃ C : ℝ, ∀ᶠ T in atTop,
        theta₀ T ≤ C * l T * T ^ (lam / 2 - 1)) ∧
      (∀ᶠ T in atTop,
        DirectStrictSeamAt zetaZeroConfig P theta₀ T) ∧
      (∀ᶠ T in atTop,
        (delta₀ * (ThmD.HD lam - eps - (lam + eps) / 2 - eps) ^ 2 /
            (8 * (1 + eps))) * (Ncount T (2 * T) : ℝ) ≤
          directAtDCoreGain zetaZeroConfig T P) := by
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
  have hdeltaPos : 18 * (1 - P.lam) < directFourEnergyLower / 2 := by
    have hpos : 0 < directFourEnergyLower / 2 - 18 * (1 - lam) :=
      hdelta₀.trans_lt hdeltaLim
    have : 18 * (1 - lam) < directFourEnergyLower / 2 := by linarith
    simpa [P, paramsOf] using this
  have hseam := eventually_seamA_mult2_atD_with_direct_explicit_gain
    hcertificate zetaZeroConfig P hP theta₀ hTail hNonempty hdeltaPos
  have hgain := eventually_directAtDCoreGain_ge_fixed_eps
    zetaZeroConfig paperInputs_zeta.RvM P hP hconj
    hbase heps hH hdelta₀ (by simpa [P, paramsOf] using hdeltaLim)
      (by simpa [P, paramsOf] using hq0)
  refine ⟨theta₀, hTail, ?_, ?_, ?_⟩
  · simpa [P, paramsOf] using htheta
  · simpa [DirectStrictSeamAt] using hseam
  · simpa [P, paramsOf] using hgain

end StrictImprovement
end Zeta23

end
