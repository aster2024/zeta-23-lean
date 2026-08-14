/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q6SuperbinZetaSeamAtD
import Zeta23.StrictImprovement.Q6SuperbinZetaCoreGain
import Zeta23.StrictImprovement.ZetaLocalDeltaLimit

/-! # Eventual q6 superbin seam at fixed taper -/

noncomputable section

open Filter Topology Real Matrix RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

theorem eventually_seamA_mult2_atD_with_q6Superbin_gain
    (hcertificates : Q6SuperbinEndpointCertificates)
    (Z : ZeroConfig) (P : Params) (hP : P.Valid)
    (theta0 : ℝ → ℝ)
    (hTail : ∀ᶠ T in atTop,
      Assembly.TailInputs Z (P.atD T) T (theta0 T))
    (hNonempty : ∀ᶠ T in atTop,
      Nonempty (CoreSimpleLabel Z T 3))
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hmargin3 : scale * wideRepairRewardThree +
        (9 * Real.sqrt 3 / 2) * (1 - P.lam) < wideRepairRewardThree)
    (hmargin4 : scale * wideRepairRewardFour +
        6 * Real.sqrt 3 * (1 - P.lam) < wideRepairRewardFour)
    (hmargin5 : scale * wideRepairRewardFive +
        (15 * Real.sqrt 5 / 2) * (1 - P.lam) < wideRepairRewardFive)
    (hmargin6 : scale * q6SuperbinReward +
        9 * Real.sqrt 6 * (1 - P.lam) < q6SuperbinReward) :
    ∀ᶠ T in atTop,
      4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
          frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
          2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ) -
          theta0 T / ((P.atD T).a T * (P.atD T).L T) *
            (4 + 2 * Real.sqrt
                (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
              theta0 T / ((P.atD T).a T * (P.atD T).L T)) +
          q6SuperbinAtDCoreGain Z T P scale
        ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3 := by
  obtain ⟨T0, hlocal⟩ := ThmD.localHypsCoreD_eventually hP
  have hLtop := ThmD.tendsto_L hP
  have haRange := ThmD.eventually_aD_range hP
  have herr := tendsto_atDLocalCorrelationError hP
  have hmargin3Tendsto : Tendsto
      (fun T => scale * wideRepairRewardThree +
        (3 * Real.sqrt 3 / 2) *
          localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
            (12 * P.w / P.L T + 3 * (1 - P.lam))) atTop
      (nhds (scale * wideRepairRewardThree +
        (9 * Real.sqrt 3 / 2) * (1 - P.lam))) := by
    have hconst : Tendsto
        (fun _ : ℝ => scale * wideRepairRewardThree) atTop
        (nhds (scale * wideRepairRewardThree)) := tendsto_const_nhds
    have hsum := hconst.add (herr.const_mul (3 * Real.sqrt 3 / 2))
    have hend : scale * wideRepairRewardThree +
        (3 * Real.sqrt 3 / 2) * (3 * (1 - P.lam)) =
          scale * wideRepairRewardThree +
            (9 * Real.sqrt 3 / 2) * (1 - P.lam) := by ring
    rw [← hend]
    simpa only using hsum
  have hmargin4Tendsto : Tendsto
      (fun T => scale * wideRepairRewardFour + 2 * Real.sqrt 3 *
          localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
            (12 * P.w / P.L T + 3 * (1 - P.lam))) atTop
      (nhds (scale * wideRepairRewardFour +
        6 * Real.sqrt 3 * (1 - P.lam))) := by
    have hconst : Tendsto
        (fun _ : ℝ => scale * wideRepairRewardFour) atTop
        (nhds (scale * wideRepairRewardFour)) := tendsto_const_nhds
    have hsum := hconst.add (herr.const_mul (2 * Real.sqrt 3))
    have hend : scale * wideRepairRewardFour +
        (2 * Real.sqrt 3) * (3 * (1 - P.lam)) =
          scale * wideRepairRewardFour +
            6 * Real.sqrt 3 * (1 - P.lam) := by ring
    rw [← hend]
    simpa only using hsum
  have hmargin5Tendsto : Tendsto
      (fun T => scale * wideRepairRewardFive +
        (5 * Real.sqrt 5 / 2) *
          localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
            (12 * P.w / P.L T + 3 * (1 - P.lam))) atTop
      (nhds (scale * wideRepairRewardFive +
        (15 * Real.sqrt 5 / 2) * (1 - P.lam))) := by
    have hconst : Tendsto
        (fun _ : ℝ => scale * wideRepairRewardFive) atTop
        (nhds (scale * wideRepairRewardFive)) := tendsto_const_nhds
    have hsum := hconst.add (herr.const_mul (5 * Real.sqrt 5 / 2))
    have hend : scale * wideRepairRewardFive +
        (5 * Real.sqrt 5 / 2) * (3 * (1 - P.lam)) =
          scale * wideRepairRewardFive +
            (15 * Real.sqrt 5 / 2) * (1 - P.lam) := by ring
    rw [← hend]
    simpa only using hsum
  have hmargin6Tendsto : Tendsto
      (fun T => scale * q6SuperbinReward + 3 * Real.sqrt 6 *
          localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
            (12 * P.w / P.L T + 3 * (1 - P.lam))) atTop
      (nhds (scale * q6SuperbinReward +
        9 * Real.sqrt 6 * (1 - P.lam))) := by
    have hconst : Tendsto
        (fun _ : ℝ => scale * q6SuperbinReward) atTop
        (nhds (scale * q6SuperbinReward)) := tendsto_const_nhds
    have hsum := hconst.add (herr.const_mul (3 * Real.sqrt 6))
    have hend : scale * q6SuperbinReward +
        (3 * Real.sqrt 6) * (3 * (1 - P.lam)) =
          scale * q6SuperbinReward +
            9 * Real.sqrt 6 * (1 - P.lam) := by ring
    rw [← hend]
    simpa only using hsum
  have hmargin3Ev := hmargin3Tendsto.eventually (Iio_mem_nhds hmargin3)
  have hmargin4Ev := hmargin4Tendsto.eventually (Iio_mem_nhds hmargin4)
  have hmargin5Ev := hmargin5Tendsto.eventually (Iio_mem_nhds hmargin5)
  have hmargin6Ev := hmargin6Tendsto.eventually (Iio_mem_nhds hmargin6)
  filter_upwards [hTail, hNonempty, eventually_ge_atTop T0,
      hLtop.eventually_ge_atTop (16 * P.w),
      hLtop.eventually_gt_atTop ((ThmD.cDT P.ϱ P.lam) ^ 2),
      haRange, hmargin3Ev, hmargin4Ev, hmargin5Ev, hmargin6Ev,
      eventually_gt_atTop (0 : ℝ)]
    with T hTl hne hT0 h16 hlarge haD hm3 hm4 hm5 hm6 hT
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
  have hscaleMass : (P.atD T).L T ^ 2 / 2 ≤
      (P.atD T).a T * (P.atD T).L T ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right haD.1
      (sq_nonneg ((P.atD T).L T))
    nlinarith
  have hbudget :
      coreTailBudget (ThmD.cDT P.ϱ P.lam)
          ((P.atD T).toSetting T) 3 <
        (P.atD T).a T * (P.atD T).L T ^ 2 :=
    htailHalf.trans_le hscaleMass
  let hconj : PhiHatConj T (P.atD T) :=
    fun z => GzGp.phiHat_conj (P.atD T) T z
  let hreal : PhiHatReal T (P.atD T) :=
    fun r => GzGp.phiHat_ofReal (P.atD T) T r
  have hpos : ∀ z, 0 < finiteCoreWeight Z T 3 (P.atD T) hconj z := by
    intro z
    have hz := z.2
    simp only [coreSimple, Finset.mem_filter] at hz
    have hrhoLe := rho_core_le_budget hF hT
      (show (1 : ℝ) < 3 by norm_num) hz.2
    exact finiteCoreWeight_pos_of_rho_lt Z T 3 (P.atD T) hconj
      hreal hc z (hrhoLe.trans_lt hbudget)
  have h8 : 8 * P.w ≤ P.L T := by nlinarith [hP.one_le_w]
  have hPois : PoissonSq T (P.atD T) := ThmD.poissonSqD hP h8
  have hseam := seamA_mult2_atD_with_q6Superbin_gain
    hcertificates Z hP hconj hreal hPois hF hTl hT hc hbudget h16 hpos
      hscale hm3.le hm4.le hm5.le hm6.le
  simpa [q6SuperbinAtDCoreGain] using hseam

end StrictImprovement
end Zeta23

end
