/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaStrictTraceEndgame

/-!
# Unconditional strict improvement at fixed lambda

This file instantiates the strict trace endgame with the frozen concrete
Theorem-D trace package for Mathlib's zeta function.  Every internal epsilon
and every gain coefficient remains explicit.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace Zeta23
namespace StrictImprovement

/-- At every admissible fixed `lam`, `delta0`, and internal `eps`, the zeta
simple-on-line density improves by the displayed positive quadratic amount. -/
theorem zeta_strict_simple_fixed_lam
    {lam delta₀ eps : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (heps : 0 < eps)
    (hH : 0 < ThmD.HD lam - eps)
    (hdelta₀ : 0 ≤ delta₀)
    (hdeltaLim : delta₀ < explicitDeltaLower - 18 * (1 - lam))
    (hq0 : 0 ≤ ThmD.HD lam - eps - (lam + eps) / 2 - eps) :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD lam +
          delta₀ * (ThmD.HD lam - eps - (lam + eps) / 2 - eps) ^ 2 /
            (9 * (1 + eps)) - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  let P : Params := paramsOf stdProfile lam
  have hP : P.Valid := by
    dsimp [P]
    exact paramsOf_valid taperProfile_stdProfile hlam0 hlam1.le
  obtain ⟨theta₀, hTail, htheta, hSeam, hgain⟩ :=
    zeta_strict_package_fixed_lam
      hlam0 hlam1 heps hH hdelta₀ hdeltaLim hq0
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
  obtain ⟨A₀, hA₀, hlocalCount⟩ := paperInputs_zeta.RvM.local_count
  have hNII := Tail.eventually_NII_le zetaZeroConfig hA₀ hlocalCount
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
    _ _ _ _ _ hTr hc0 hc ha theta₀ hTail
    (by simpa [P, paramsOf] using htheta) hNII hGzGp hId hcalE
    (fun T => atDCoreGain zetaZeroConfig T P)
    (fun T => (excludedSimpleCount zetaZeroConfig T 3 : ℝ))
    (by simpa [StrictSeamAt] using hSeam)
    hboundary
    (by simpa [P, paramsOf] using hgain)
  simpa [P, paramsOf, ThmD.HD, one_div, add_assoc] using hstrict

end StrictImprovement
end Zeta23

end
