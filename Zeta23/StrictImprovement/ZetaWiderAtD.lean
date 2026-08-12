/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.CoreFourEnergy
import Zeta23.StrictImprovement.ZetaAtDCorrelation
import Zeta23.StrictImprovement.ZetaLocalDeltaLimit

/-!
# The concrete `atD` four-point energy and its fixed-taper limit

This is the width-six, four-point counterpart of `ZetaAtDCorrelation.lean`.
It introduces no new analytic input: the same full-correlation comparison and
the same finite/full normalization error are inserted into the exact local
four-point theorem.

At fixed taper `lam`, the local constant tends exactly to

`widerDeltaLower - 18 * (1 - lam)`.

The factor `18` remains `6 * 3`: four-point double counting changes the
rank--trace coefficient downstream, but it does not change the six-edge
stability loss inside one local block.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Filter Topology Real
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

/-- The exact fixed-height defect surviving the full-kernel and finite/full
normalization errors in the width-six four-point route. -/
def widerAtDLocalDelta (T : ℝ) (P : Params) : ℝ :=
  widerDeltaLower -
    6 * localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
      (12 * P.w / P.L T + 3 * (1 - P.lam))

/-- Every canonical packed width-six four-tuple for the concrete `atD` family
has at least twice the wider local defect as its six-edge energy. -/
theorem packedCoreFour_atD_local_energy
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
    2 * widerAtDLocalDelta T P ≤
      fourCorrelationEnergy
        (normalizedCoreVec Z T 3 (P.atD T) hconj)
        (packedFourIndex
          (coreWidthSixEnumeration Z T 3 (P.atD T)
            (by simpa using (show 0 < P.L T by linarith [hP.one_le_w]))
            (by norm_num))) q := by
  unfold widerAtDLocalDelta
  have hL : 0 < (P.atD T).L T := by
    simpa using (show 0 < P.L T by linarith [hP.one_le_w])
  have heps : 0 ≤ 12 * P.w / P.L T + 3 * (1 - P.lam) := by
    have hL' : 0 < P.L T := by linarith [hP.one_le_w]
    have hw0 : 0 ≤ P.w := by linarith [hP.one_le_w]
    have hlam0 : 0 ≤ 1 - P.lam := sub_nonneg.mpr hP.lam_le_one
    have hfinite0 : 0 ≤ 12 * P.w / P.L T :=
      div_nonneg (mul_nonneg (by norm_num) hw0) hL'.le
    nlinarith
  apply packedCoreFour_local_energy Z T (P.atD T) hconj
    (ThmD.cDT P.ϱ P.lam)
    hreal hF hT hc hbudget hL hpos heps
  · intro z z'
    simpa only [Params.atD_L, coreScaledOrdinate] using
      (fullCoreCorrelation_atD_close_endpointR Z hP hwL z z')

/-- Fixed-`lam` limit of the wider local energy constant. -/
theorem tendsto_widerAtDLocalDelta
    {P : Params} (hP : P.Valid) :
    Tendsto (fun T => widerAtDLocalDelta T P) atTop
      (𝓝 (widerDeltaLower - 18 * (1 - P.lam))) := by
  have herr := (tendsto_atDLocalCorrelationError hP).const_mul 6
  have hconst : Tendsto (fun _ : ℝ => widerDeltaLower) atTop
      (𝓝 widerDeltaLower) := tendsto_const_nhds
  have hlim := hconst.sub herr
  have hend : widerDeltaLower - 6 * (3 * (1 - P.lam)) =
      widerDeltaLower - 18 * (1 - P.lam) := by ring
  rw [← hend]
  simpa only [widerAtDLocalDelta] using hlim

/-- Any constant strictly below the limiting wider defect is eventually a
valid local lower bound. -/
theorem eventually_widerAtDLocalDelta_gt
    {P : Params} (hP : P.Valid) {delta0 : ℝ}
    (hdelta : delta0 < widerDeltaLower - 18 * (1 - P.lam)) :
    ∀ᶠ T in atTop, delta0 < widerAtDLocalDelta T P :=
  (tendsto_widerAtDLocalDelta hP).eventually (eventually_gt_nhds hdelta)

/-- The wider local defect is eventually positive whenever the fixed endpoint
loss is smaller than the exact wider root-separation constant. -/
theorem eventually_widerAtDLocalDelta_pos
    {P : Params} (hP : P.Valid)
    (hlam : 18 * (1 - P.lam) < widerDeltaLower) :
    ∀ᶠ T in atTop, 0 < widerAtDLocalDelta T P := by
  exact eventually_widerAtDLocalDelta_gt hP (by linarith)

end StrictImprovement
end Zeta23

end
