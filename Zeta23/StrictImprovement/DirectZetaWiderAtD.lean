/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.DirectCoreFourEnergy
import Zeta23.StrictImprovement.ZetaAtDCorrelation
import Zeta23.StrictImprovement.ZetaLocalDeltaLimit

/-!
# Direct four-point energy at fixed taper

This specializes the explicit four-coordinate certificate interface to the
concrete `atD` correlation family.  The only non-kernel input remains the
explicit argument `hcertificate : DirectFourEndpointCertificate`.
-/

noncomputable section

open Filter Topology Real
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

/-- The finite-height direct four-point defect after full-kernel and
finite/full normalization errors. -/
def directAtDLocalDelta (T : ℝ) (P : Params) : ℝ :=
  directFourEnergyLower / 2 -
    6 * localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
      (12 * P.w / P.L T + 3 * (1 - P.lam))

/-- Every packed width-six four-tuple satisfies the direct certified local
energy inequality. -/
theorem packedCoreFour_atD_direct_local_energy
    (hcertificate : DirectFourEndpointCertificate)
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
    (q : PackedFour (coreWidthSixEnumeration Z T 3 (P.atD T)
      (by simpa using (show 0 < P.L T by linarith [hP.one_le_w]))
      (by norm_num))) :
    2 * directAtDLocalDelta T P ≤
      fourCorrelationEnergy
        (normalizedCoreVec Z T 3 (P.atD T) hconj)
        (packedFourIndex
          (coreWidthSixEnumeration Z T 3 (P.atD T)
            (by simpa using (show 0 < P.L T by linarith [hP.one_le_w]))
            (by norm_num))) q := by
  unfold directAtDLocalDelta
  have hL : 0 < (P.atD T).L T := by
    simpa using (show 0 < P.L T by linarith [hP.one_le_w])
  have heps : 0 ≤ 12 * P.w / P.L T + 3 * (1 - P.lam) := by
    have hL' : 0 < P.L T := by linarith [hP.one_le_w]
    have hw0 : 0 ≤ P.w := by linarith [hP.one_le_w]
    have hlam0 : 0 ≤ 1 - P.lam := sub_nonneg.mpr hP.lam_le_one
    have hfinite0 : 0 ≤ 12 * P.w / P.L T :=
      div_nonneg (mul_nonneg (by norm_num) hw0) hL'.le
    nlinarith
  apply packedCoreFour_direct_local_energy Z T (P.atD T) hconj
    hcertificate (ThmD.cDT P.ϱ P.lam)
    hreal hF hT hc hbudget hL hpos heps
  intro z z'
  simpa only [Params.atD_L, coreScaledOrdinate] using
    (fullCoreCorrelation_atD_close_endpointR Z hP hwL z z')

/-- Fixed-taper limit of the direct local defect. -/
theorem tendsto_directAtDLocalDelta
    {P : Params} (hP : P.Valid) :
    Tendsto (fun T => directAtDLocalDelta T P) atTop
      (𝒩 (directFourEnergyLower / 2 - 18 * (1 - P.lam))) := by
  have herr := (tendsto_atDLocalCorrelationError hP).const_mul 6
  have hconst : Tendsto (fun _ : ℝ => directFourEnergyLower / 2) atTop
      (𝒩 (directFourEnergyLower / 2)) := tendsto_const_nhds
  have hlim := hconst.sub herr
  have hend : directFourEnergyLower / 2 - 6 * (3 * (1 - P.lam)) =
      directFourEnergyLower / 2 - 18 * (1 - P.lam) := by ring
  rw [← hend]
  simpa only [directAtDLocalDelta] using hlim

/-- Every constant strictly below the direct fixed-taper limit is eventually
a valid local defect. -/
theorem eventually_directAtDLocalDelta_gt
    {P : Params} (hP : P.Valid) {delta0 : ℝ}
    (hdelta : delta0 < directFourEnergyLower / 2 - 18 * (1 - P.lam)) :
    ∀ᶠ T in atTop, delta0 < directAtDLocalDelta T P :=
  (tendsto_directAtDLocalDelta hP).eventually (eventually_gt_nhds hdelta)

/-- The direct local defect is eventually positive whenever the taper loss is
smaller than half the certified endpoint energy. -/
theorem eventually_directAtDLocalDelta_pos
    {P : Params} (hP : P.Valid)
    (hlam : 18 * (1 - P.lam) < directFourEnergyLower / 2) :
    ∀ᶠ T in atTop, 0 < directAtDLocalDelta T P := by
  exact eventually_directAtDLocalDelta_gt hP (by linarith)

end StrictImprovement
end Zeta23

end
