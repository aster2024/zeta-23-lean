/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaAtDCorrelation
import Zeta23.ThmD.ZeroSideD

/-!
# The fixed-`lam` limit of the local three-point defect

This file removes the last asymptotic placeholder from the local energy
constant.  The finite-grid tail is bounded, with exact rational constants, by

`4*c^2/(81*L) + 113*c^2/(648*L^2)`.

Consequently the tail tends to zero at every fixed valid taper, and

`atDLocalDelta(T,P) -> explicitDeltaLower - 18*(1-P.lam)`.

The coefficient `18` is not an asymptotic convention: it is the product of
the stability loss `6` and the endpoint-kernel loss `3*(1-lam)`.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

open PrimeSide

/-- The normalized finite-grid tail for the concrete Montgomery--Taylor
window at height `T`. -/
def atDTailRatio (T : ℝ) (P : Params) : ℝ :=
  coreTailBudget (ThmD.cDT P.ϱ P.lam) (P.toSetting T) 3 /
    ((P.atD T).a T * P.L T ^ 2)

/-- A rational upper envelope for `atDTailRatio`. -/
def atDTailRatioUpper (T : ℝ) (P : Params) : ℝ :=
  (4 * (ThmD.cDT P.ϱ P.lam) ^ 2 / 81) / P.L T +
    (113 * (ThmD.cDT P.ϱ P.lam) ^ 2 / 648) / P.L T ^ 2

/-- The explicit three-point tail budget is nonnegative. -/
lemma coreTailBudget_three_nonneg
    {cϱ : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW cϱ p F) :
    0 ≤ coreTailBudget cϱ p 3 := by
  unfold coreTailBudget
  have hh : 0 ≤ p.h⁻¹ := inv_nonneg.mpr (PrimeSide.h_pos hF).le
  positivity

/-- Exact budget-over-mass estimate.  This is the only division estimate used
in the fixed-`lam` tail limit. -/
lemma coreTailBudget_three_div_mass_le
    {cϱ a : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW cϱ p F) (ha : 1 / 2 ≤ a) :
    coreTailBudget cϱ p 3 / (a * p.L ^ 2) ≤
      (4 * cϱ ^ 2 / 81) / p.L + (113 * cϱ ^ 2 / 648) / p.L ^ 2 := by
  have hL : 0 < p.L := hF.L_pos
  have ha0 : 0 < a := by linarith
  have hmass : 0 < a * p.L ^ 2 := mul_pos ha0 (sq_pos_of_pos hL)
  let U : ℝ := (4 * cϱ ^ 2 / 81) / p.L +
    (113 * cϱ ^ 2 / 648) / p.L ^ 2
  have hU0 : 0 ≤ U := by
    dsimp [U]
    positivity
  have hhalf : p.L ^ 2 / 2 ≤ a * p.L ^ 2 := by
    nlinarith [sq_nonneg p.L]
  have hid :
      cϱ ^ 2 * (2 * p.L / 81 + 113 / 1296) = U * (p.L ^ 2 / 2) := by
    dsimp [U]
    field_simp [hL.ne']
    ring
  rw [div_le_iff₀ hmass]
  calc
    coreTailBudget cϱ p 3
        ≤ cϱ ^ 2 * (2 * p.L / 81 + 113 / 1296) :=
          coreTailBudget_three_le hF
    _ = U * (p.L ^ 2 / 2) := hid
    _ ≤ U * (a * p.L ^ 2) := mul_le_mul_of_nonneg_left hhalf hU0

/-- Pointwise nonnegativity of the concrete tail ratio, under the same local
hypotheses that are already supplied by the frozen D-window bridge. -/
lemma atDTailRatio_nonneg_of
    {T : ℝ} {P : Params} (hP : P.Valid)
    (hF : PrimeSide.LocalHypsCore (ThmD.cDT P.ϱ P.lam)
      (P.toSetting T) (P.localFunD T)) :
    0 ≤ atDTailRatio T P := by
  have ha : 0 < (P.atD T).a T := by
    rw [Params.atD_a T hP]
    exact hF.toCoreW.a_pos
  have hL : 0 < P.L T := hF.toCoreW.L_pos
  unfold atDTailRatio
  exact div_nonneg (coreTailBudget_three_nonneg hF.toCoreW)
    (mul_nonneg ha.le (sq_nonneg _))

/-- Pointwise rational upper bound for the concrete tail ratio. -/
lemma atDTailRatio_le_upper_of
    {T : ℝ} {P : Params} (hP : P.Valid)
    (hF : PrimeSide.LocalHypsCore (ThmD.cDT P.ϱ P.lam)
      (P.toSetting T) (P.localFunD T)) :
    atDTailRatio T P ≤ atDTailRatioUpper T P := by
  have ha : 1 / 2 ≤ (P.atD T).a T := by
    rw [Params.atD_a T hP]
    exact hF.b_ge_half.trans hF.b_le_a
  simpa [atDTailRatio, atDTailRatioUpper, Params.toSetting_L] using
    (coreTailBudget_three_div_mass_le hF.toCoreW ha)

/-- Both sides of the squeeze estimate hold eventually. -/
theorem eventually_atDTailRatio_bounds
    {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop,
      0 ≤ atDTailRatio T P ∧ atDTailRatio T P ≤ atDTailRatioUpper T P := by
  obtain ⟨T₀, hlocal⟩ := ThmD.localHypsCoreD_eventually hP
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have hF := hlocal T hT
  exact ⟨atDTailRatio_nonneg_of hP hF, atDTailRatio_le_upper_of hP hF⟩

/-- The explicit rational upper envelope tends to zero. -/
theorem tendsto_atDTailRatioUpper_zero
    {P : Params} (hP : P.Valid) :
    Tendsto (fun T => atDTailRatioUpper T P) atTop (𝓝 0) := by
  have hL : Tendsto P.L atTop atTop := ThmD.tendsto_L hP
  have hL2 : Tendsto (fun T => P.L T ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hL
  have h1 : Tendsto
      (fun T => (4 * (ThmD.cDT P.ϱ P.lam) ^ 2 / 81) / P.L T)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hL
  have h2 : Tendsto
      (fun T => (113 * (ThmD.cDT P.ϱ P.lam) ^ 2 / 648) / P.L T ^ 2)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hL2
  simpa [atDTailRatioUpper] using h1.add h2

/-- The finite-grid normalization tail vanishes at fixed `lam`. -/
theorem tendsto_atDTailRatio_zero
    {P : Params} (hP : P.Valid) :
    Tendsto (fun T => atDTailRatio T P) atTop (𝓝 0) := by
  have hb := eventually_atDTailRatio_bounds hP
  exact squeeze_zero' (hb.mono fun T h => h.1)
    (hb.mono fun T h => h.2) (tendsto_atDTailRatioUpper_zero hP)

/-- The full-kernel comparison error has exactly the fixed-`lam` limit
`3*(1-lam)`. -/
theorem tendsto_atDEpsFull
    {P : Params} (hP : P.Valid) :
    Tendsto (fun T => 12 * P.w / P.L T + 3 * (1 - P.lam))
      atTop (𝓝 (3 * (1 - P.lam))) := by
  have hzero : Tendsto (fun T => 12 * P.w / P.L T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (ThmD.tendsto_L hP)
  simpa using hzero.add_const (3 * (1 - P.lam))

/-- The complete local correlation error tends to `3*(1-lam)`: the finite
full-kernel error contributes this term, while the finite-grid tail vanishes. -/
theorem tendsto_atDLocalCorrelationError
    {P : Params} (hP : P.Valid) :
    Tendsto (fun T => localCorrelationError T (P.atD T)
      (ThmD.cDT P.ϱ P.lam) (12 * P.w / P.L T + 3 * (1 - P.lam)))
      atTop (𝓝 (3 * (1 - P.lam))) := by
  have heps := tendsto_atDEpsFull hP
  have htail := (tendsto_atDTailRatio_zero hP).const_mul 2
  have hsum := heps.add htail
  simpa [localCorrelationError, atDTailRatio, Params.atD_toSetting,
    Params.atD_L] using hsum

/-- Fixed-`lam` limit of the actual local energy constant. -/
theorem tendsto_atDLocalDelta
    {P : Params} (hP : P.Valid) :
    Tendsto (fun T => atDLocalDelta T P) atTop
      (𝓝 (explicitDeltaLower - 18 * (1 - P.lam))) := by
  have herr := (tendsto_atDLocalCorrelationError hP).const_mul 6
  have hconst : Tendsto (fun _ : ℝ => explicitDeltaLower) atTop
      (𝓝 explicitDeltaLower) := tendsto_const_nhds
  have hlim := hconst.sub herr
  convert hlim using 1 <;> ring

/-- Any constant strictly below the limiting local defect is eventually a
valid uniform lower bound. -/
theorem eventually_atDLocalDelta_gt
    {P : Params} (hP : P.Valid) {delta0 : ℝ}
    (hdelta : delta0 < explicitDeltaLower - 18 * (1 - P.lam)) :
    ∀ᶠ T in atTop, delta0 < atDLocalDelta T P :=
  (tendsto_atDLocalDelta hP).eventually (eventually_gt_nhds hdelta)

/-- In particular, the local defect is eventually positive whenever the
fixed endpoint loss is strictly smaller than `explicitDeltaLower`. -/
theorem eventually_atDLocalDelta_pos
    {P : Params} (hP : P.Valid)
    (hlam : 18 * (1 - P.lam) < explicitDeltaLower) :
    ∀ᶠ T in atTop, 0 < atDLocalDelta T P := by
  exact eventually_atDLocalDelta_gt hP (by linarith)

end StrictImprovement
end Zeta23

end
