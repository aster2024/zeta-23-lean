/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.CertificateSlackCoreFour
import Zeta23.StrictImprovement.ZetaAtDCorrelation

/-!
# Full-certificate spectral mass at a fixed taper
-/

noncomputable section

open Filter Topology Real
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

/-- Every packed `264/7`-bin four-tuple satisfies the spectral trace-norm
lower bound whenever its square-root margin absorbs the finite/full error. -/
theorem packedCoreCertificateSlackFour_atD_spectral_local_traceNorm
    (hcertificate : SpectralFourEndpointSlackCertificate)
    (Z : ZeroConfig) {T : ℝ} {P : Params} (hP : P.Valid)
    (hconj : PhiHatConj T (P.atD T))
    (hreal : PhiHatReal T (P.atD T))
    (hF : PrimeSide.LocalHypsCoreW (ThmD.cDT P.ϱ P.lam)
      ((P.atD T).toSetting T) ((P.atD T).localFun T))
    (hT : 0 < T)
    (hc : 0 < (P.atD T).a T * (P.atD T).L T ^ 2)
    (hbudget :
      coreTailBudget (ThmD.cDT P.ϱ P.lam) ((P.atD T).toSetting T) 3 <
        (P.atD T).a T * (P.atD T).L T ^ 2)
    (hwL : 16 * P.w ≤ P.L T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 (P.atD T) hconj z)
    {m : ℝ} (hm : 0 ≤ m)
    (hmargin : Real.sqrt m + 2 * Real.sqrt 3 *
        localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
          (12 * P.w / P.L T + 3 * (1 - P.lam)) ≤
      Real.sqrt spectralFourMassLower)
    (q : PackedFour (coreCertificateSlackEnumeration Z T 3 (P.atD T)
      (by simpa using (show 0 < P.L T by linarith [hP.one_le_w]))
      (by norm_num))) :
    2 * Real.sqrt m ≤ Tail.traceNorm
      ((gramDeviation_isHermitian
        (normalizedCoreVec Z T 3 (P.atD T) hconj)).submatrix
          (packedFourIndex
            (coreCertificateSlackEnumeration Z T 3 (P.atD T)
              (by simpa using
                (show 0 < P.L T by linarith [hP.one_le_w]))
              (by norm_num)) q)) := by
  have hL : 0 < (P.atD T).L T := by
    simpa using (show 0 < P.L T by linarith [hP.one_le_w])
  have heps : 0 ≤ 12 * P.w / P.L T + 3 * (1 - P.lam) := by
    have hL' : 0 < P.L T := by linarith [hP.one_le_w]
    have hw0 : 0 ≤ P.w := by linarith [hP.one_le_w]
    have hlam0 : 0 ≤ 1 - P.lam := sub_nonneg.mpr hP.lam_le_one
    have hfinite0 : 0 ≤ 12 * P.w / P.L T :=
      div_nonneg (mul_nonneg (by norm_num) hw0) hL'.le
    nlinarith
  apply packedCoreCertificateSlackFour_spectral_traceNorm_lower
    Z T (P.atD T) hconj hcertificate (ThmD.cDT P.ϱ P.lam)
    hreal hF hT hc hbudget hL hpos heps hm
  · intro z z'
    simpa only [Params.atD_L, coreScaledOrdinate] using
      (fullCoreCorrelation_atD_close_endpointR Z hP hwL z z')
  · exact hmargin

end StrictImprovement
end Zeta23

end
