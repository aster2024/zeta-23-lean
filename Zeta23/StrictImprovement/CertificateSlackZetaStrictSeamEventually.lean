/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.CertificateSlackZetaSeamAtD
import Zeta23.StrictImprovement.CertificateSlackZetaCoreGain
import Zeta23.StrictImprovement.ZetaLocalDeltaLimit

/-!
# Eventual seam for the full certificate domain

The local stability cost is unchanged; only the packing coefficient changes.
-/

noncomputable section

open Filter Topology Real Matrix RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

/-- The widened-bin spectral seam holds eventually for a fixed admissible
spectral mass. -/
theorem eventually_seamA_mult2_atD_with_certificate_slack_spectral_gain
    (hcertificate : SpectralFourEndpointSlackCertificate)
    (Z : ZeroConfig) (P : Params) (hP : P.Valid)
    (theta0 : ℝ → ℝ)
    (hTail : ∀ᶠ T in atTop,
      Assembly.TailInputs Z (P.atD T) T (theta0 T))
    (hNonempty : ∀ᶠ T in atTop,
      Nonempty (CoreSimpleLabel Z T 3))
    {m : ℝ} (hm : 0 ≤ m)
    (hmarginLim : Real.sqrt m + 6 * Real.sqrt 3 * (1 - P.lam) <
      Real.sqrt spectralFourMassLower) :
    ∀ᶠ T in atTop,
      4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
          frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
          2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ) -
          theta0 T / ((P.atD T).a T * (P.atD T).L T) *
            (4 + 2 * Real.sqrt
                (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
              theta0 T / ((P.atD T).a T * (P.atD T).L T)) +
          certificateSlackSpectralAtDCoreGain Z T P m
        ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3 := by
  obtain ⟨T0, hlocal⟩ := ThmD.localHypsCoreD_eventually hP
  have hLtop := ThmD.tendsto_L hP
  have haRange := ThmD.eventually_aD_range hP
  have herr := (tendsto_atDLocalCorrelationError hP).const_mul
    (2 * Real.sqrt 3)
  have hconst : Tendsto (fun _ : ℝ => Real.sqrt m) atTop
      (nhds (Real.sqrt m)) := tendsto_const_nhds
  have hmarginTendsto : Tendsto
      (fun T => Real.sqrt m + 2 * Real.sqrt 3 *
        localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
          (12 * P.w / P.L T + 3 * (1 - P.lam)))
      atTop (nhds (Real.sqrt m + 6 * Real.sqrt 3 * (1 - P.lam))) := by
    have hsum := hconst.add herr
    have hend : Real.sqrt m +
        (2 * Real.sqrt 3) * (3 * (1 - P.lam)) =
          Real.sqrt m + 6 * Real.sqrt 3 * (1 - P.lam) := by ring
    rw [← hend]
    simpa only using hsum
  have hmarginEv : ∀ᶠ T in atTop,
      Real.sqrt m + 2 * Real.sqrt 3 *
          localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
            (12 * P.w / P.L T + 3 * (1 - P.lam)) <
        Real.sqrt spectralFourMassLower :=
    hmarginTendsto.eventually (Iio_mem_nhds hmarginLim)
  filter_upwards [hTail, hNonempty, eventually_ge_atTop T0,
      hLtop.eventually_ge_atTop (16 * P.w),
      hLtop.eventually_gt_atTop ((ThmD.cDT P.ϱ P.lam) ^ 2),
      haRange, hmarginEv, eventually_gt_atTop (0 : ℝ)]
    with T hTl hne hT0 h16 hlarge haD hmarginT hT
  letI : Nonempty (CoreSimpleLabel Z T 3) := hne
  have hFcore := hlocal T hT0
  have hF : PrimeSide.LocalHypsCoreW (ThmD.cDT P.ϱ P.lam)
      ((P.atD T).toSetting T) ((P.atD T).localFun T) := by
    simpa [Params.atD_toSetting, Params.atD_localFun T hP] using
      hFcore.toCoreW
  have hL : 0 < P.L T := by
    simpa [Params.atD_toSetting, Params.toSetting_L] using hF.L_pos
  have hLD : 0 < (P.atD T).L T := by simpa using hL
  have ha : 0 < (P.atD T).a T := by linarith [haD.1]
  have hc : 0 < (P.atD T).a T * (P.atD T).L T ^ 2 :=
    mul_pos ha (sq_pos_of_pos hLD)
  have hlargeF : (ThmD.cDT P.ϱ P.lam) ^ 2 <
      ((P.atD T).toSetting T).L := by
    simpa [Params.atD_toSetting, Params.toSetting_L] using hlarge
  have htailHalf := coreTailBudget_three_lt_half_L_sq hF hlargeF
  have hscale : (P.atD T).L T ^ 2 / 2 ≤
      (P.atD T).a T * (P.atD T).L T ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right haD.1
      (sq_nonneg ((P.atD T).L T))
    nlinarith
  have hbudget :
      coreTailBudget (ThmD.cDT P.ϱ P.lam)
          ((P.atD T).toSetting T) 3 <
        (P.atD T).a T * (P.atD T).L T ^ 2 :=
    htailHalf.trans_le hscale
  let hconj : PhiHatConj T (P.atD T) :=
    fun z => GzGp.phiHat_conj (P.atD T) T z
  let hreal : PhiHatReal T (P.atD T) :=
    fun r => GzGp.phiHat_ofReal (P.atD T) T r
  have hpos : ∀ z,
      0 < finiteCoreWeight Z T 3 (P.atD T) hconj z := by
    intro z
    have hz := z.2
    simp only [coreSimple, Finset.mem_filter] at hz
    have hrhoLe := rho_core_le_budget hF hT
      (show (1 : ℝ) < 3 by norm_num) hz.2
    exact finiteCoreWeight_pos_of_rho_lt Z T 3 (P.atD T) hconj
      hreal hc z (hrhoLe.trans_lt hbudget)
  have h8 : 8 * P.w ≤ P.L T := by
    nlinarith [hP.one_le_w]
  have hPois : PoissonSq T (P.atD T) := ThmD.poissonSqD hP h8
  have hseam := seamA_mult2_atD_with_certificate_slack_spectral_gain
    hcertificate Z hP hconj hreal hPois hF hTl hT hc hbudget h16 hpos
      hm hmarginT.le
  simpa [certificateSlackSpectralAtDCoreGain] using hseam

end StrictImprovement
end Zeta23

end
