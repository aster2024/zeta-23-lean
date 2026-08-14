/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaStrictTraceEndgame
import Zeta23.StrictImprovement.Q6SuperbinZetaStrictFixedLambda

/-! # Q6 superbin strict improvement at fixed taper -/

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace Zeta23
namespace StrictImprovement

theorem zeta_q6Superbin_strict_simple_fixed_lam
    (hcertificates : Q6SuperbinEndpointCertificates)
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
    (hmargin6 : scale * q6SuperbinReward +
        9 * Real.sqrt 6 * (1 - lam) < q6SuperbinReward)
    (hq0 : 0 ≤ ThmD.HD lam - eps -
      q6SuperbinPackingLoss * (lam + eps) - eps) :
    ∀ outer > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (ThmD.HD lam + scale ^ 2 * wideRepairAlpha ^ 2 *
          (ThmD.HD lam - eps -
            q6SuperbinPackingLoss * (lam + eps) - eps) ^ 2 /
            (1 + eps) - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  let P : Params := paramsOf stdProfile lam
  have hP : P.Valid := by
    dsimp [P]
    exact paramsOf_valid taperProfile_stdProfile hlam0 hlam1.le
  obtain ⟨theta0, hTail, htheta, hSeam, hgain⟩ :=
    zeta_q6Superbin_strict_package_fixed_lam hcertificates
      hlam0 hlam1 heps hH hscale hmargin3 hmargin4 hmargin5 hmargin6 hq0
  have hLoc : ThmD.LocalHypsCoreDEventually P :=
    ThmD.localHypsCoreD_eventually hP
  have hTr := ThmD.tracesBoundsD_concrete
    (Z := zetaZeroConfig) hP paperInputs_zeta hLoc
  have hc := ThmD.tendsto_cRatio_concrete hP zetaZeroConfig
  have hc0 := ThmD.cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop,
      1 / 2 ≤ (ThmD.concreteDataD P zetaZeroConfig).aT T ∧
        (ThmD.concreteDataD P zetaZeroConfig).aT T ≤ 1 :=
    (ThmD.concreteFactsD hP paperInputs_zeta hLoc).ab_range.mono
      fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨A0, hA0, hlocalCount⟩ := paperInputs_zeta.RvM.local_count
  have hNII := Tail.eventually_NII_le zetaZeroConfig hA0 hlocalCount
  have hGzGp := ThmD.eventually_GzGpD
    zetaZeroConfig paperInputs_zeta hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T =
          (ThmD.concreteDataD P zetaZeroConfig).trG T ∧
      (P.atD T).trGtildeSq T =
          (ThmD.concreteDataD P zetaZeroConfig).trG2 T ∧
      (P.atD T).a T =
          (ThmD.concreteDataD P zetaZeroConfig).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP,
        Params.atD_a T hP⟩
  have hcalE := Assembly.calE_tendsto_zero P hP.lam_pos
    hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have hboundary := excludedSimpleCount_three_isLittleO
    zetaZeroConfig paperInputs_zeta.RvM
  have hstrict := strict_thmD_mult2_abstract
    zetaZeroConfig paperInputs_zeta P hP
    (by simpa [P, paramsOf] using hlam1)
    _ _ _ _ _ hTr hc0 hc ha theta0 hTail
    (by simpa [P, paramsOf] using htheta) hNII hGzGp hId hcalE
    (fun T => q6SuperbinAtDCoreGain zetaZeroConfig T P scale)
    (fun T => (excludedSimpleCount zetaZeroConfig T 3 : ℝ))
    (by simpa [Q6SuperbinStrictSeamAt] using hSeam)
    hboundary
    (by simpa [P, paramsOf] using hgain)
  simpa [P, paramsOf, ThmD.HD, one_div, add_assoc] using hstrict

end StrictImprovement
end Zeta23

end
