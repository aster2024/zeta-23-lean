/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaEndpointPassage
import Zeta23.StrictImprovement.ZetaWiderStrictConcrete
import Zeta23.StrictImprovement.WiderFourPointConstant

/-!
# Endpoint passage for the width-six four-point route

The auxiliary taper is fixed before the height tends to infinity.  This file
reuses the already formalized endpoint sequence but replaces the local defect
and quadratic coefficient by the exact width-six values.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

/-- The wider local defect at the `n`-th fixed window.  The coefficient `19`
leaves one endpoint-step of strict slack beyond the loss `18*(1-lam)`. -/
def widerEndpointDelta (n : ℕ) : ℝ :=
  widerDeltaLower - 19 * endpointStep n

/-- The exact wider coefficient supplied at the `n`-th fixed window. -/
def widerEndpointRate (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) +
    widerEndpointDelta n * endpointQ n ^ 2 /
      (8 * (1 + endpointEps n))

/-- The limiting coefficient before replacing the gain by its public
rational lower bound. -/
def widerEndpointRateLimit : ℝ :=
  ThmD.HD 1 + widerDeltaLower / 8 * (ThmD.HD 1 - 1 / 2) ^ 2

theorem tendsto_widerEndpointDelta :
    Tendsto widerEndpointDelta atTop (nhds widerDeltaLower) := by
  have h : Tendsto
      (fun n : ℕ => widerDeltaLower - 19 * endpointStep n)
      atTop (nhds (widerDeltaLower - 19 * 0)) :=
    tendsto_const_nhds.sub
      (tendsto_endpointStep_zero.const_mul 19)
  simpa [widerEndpointDelta] using h

/-- The fixed-window wider coefficient converges to the exact endpoint
coefficient without allowing the taper to depend on `T`. -/
theorem tendsto_widerEndpointRate :
    Tendsto widerEndpointRate atTop (nhds widerEndpointRateLimit) := by
  have hnum := tendsto_widerEndpointDelta.mul (tendsto_endpointQ.pow 2)
  have hden : Tendsto
      (fun n : ℕ => (8 : ℝ) * (1 + endpointStep n)) atTop
      (nhds ((8 : ℝ) * (1 + 0))) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.add tendsto_endpointStep_zero)
  have hgain := hnum.div hden (by norm_num : (8 : ℝ) * (1 + 0) ≠ 0)
  have h := tendsto_endpointHD.add hgain
  convert h using 1 <;>
    simp [widerEndpointRate, widerEndpointRateLimit, endpointEps] <;> ring

/-- Complete fixed-window feasibility conditions for the wider route. -/
def WiderEndpointFeasible (n : ℕ) : Prop :=
  0 < endpointLam n ∧ endpointLam n < 1 ∧
  0 < endpointEps n ∧
  0 < ThmD.HD (endpointLam n) - endpointEps n ∧
  0 ≤ widerEndpointDelta n ∧
  widerEndpointDelta n <
    widerDeltaLower - 18 * (1 - endpointLam n) ∧
  0 ≤ endpointQ n

/-- Every sufficiently late auxiliary index is feasible for the wider route. -/
theorem eventually_widerEndpointFeasible :
    ∀ᶠ n in atTop, WiderEndpointFeasible n := by
  have hlamPos : ∀ᶠ n in atTop, 0 < endpointLam n :=
    tendsto_endpointLam_one.eventually (Ioi_mem_nhds one_pos)
  have hdeltaPos : ∀ᶠ n in atTop, 0 < widerEndpointDelta n := by
    have h0 : 0 < widerDeltaLower := by
      norm_num [widerDeltaLower]
    exact tendsto_widerEndpointDelta.eventually (Ioi_mem_nhds h0)
  have hHlim :
      Tendsto (fun n => ThmD.HD (endpointLam n) - endpointEps n)
        atTop (nhds (ThmD.HD 1)) := by
    simpa [endpointEps] using
      tendsto_endpointHD.sub tendsto_endpointStep_zero
  have hHone : 0 < ThmD.HD 1 := by
    linarith [one_sixth_lt_HD_one_sub_half]
  have hHpos :
      ∀ᶠ n in atTop, 0 < ThmD.HD (endpointLam n) - endpointEps n :=
    hHlim.eventually (Ioi_mem_nhds hHone)
  have hqPos : ∀ᶠ n in atTop, 0 < endpointQ n :=
    tendsto_endpointQ.eventually
      (Ioi_mem_nhds one_sixth_lt_HD_one_sub_half)
  filter_upwards [hlamPos, hdeltaPos, hHpos, hqPos]
    with n hlam hdelta hH hq
  refine ⟨hlam, endpointLam_lt_one n, ?_, hH, hdelta.le, ?_, hq.le⟩
  · simpa [endpointEps] using endpointStep_pos n
  · unfold widerEndpointDelta endpointLam
    nlinarith [endpointStep_pos n]

/-- Generic endpoint passage for any certified lower bound on the wider
quadratic gain. -/
theorem zeta_wider_strict_simple_endpoint_of_le_gain
    {eta : ℝ}
    (heta : eta ≤
      widerDeltaLower / 8 * (ThmD.HD 1 - 1 / 2) ^ 2) :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + eta - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  intro outer houter
  have hclose : ∀ᶠ n in atTop,
      widerEndpointRateLimit - outer / 2 < widerEndpointRate n :=
    tendsto_widerEndpointRate.eventually
      (Ioi_mem_nhds (by linarith :
        widerEndpointRateLimit - outer / 2 < widerEndpointRateLimit))
  obtain ⟨n, hn, hrate⟩ :=
    (eventually_widerEndpointFeasible.and hclose).exists
  rcases hn with ⟨hlam0, hlam1, heps, hH, hdelta, hdeltaLim, hq⟩
  obtain ⟨T₀, hT₀⟩ := zeta_wider_strict_simple_fixed_lam
    hlam0 hlam1 heps hH hdelta hdeltaLim hq
    (outer / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have hfixed := hT₀ T hT
  have hcoef :
      ThmD.HD 1 + eta - outer ≤
        widerEndpointRate n - outer / 2 := by
    unfold widerEndpointRateLimit at hrate
    linarith
  exact le_trans
    (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) hfixed

/-- **Width-six four-point unconditional strict endpoint improvement.** -/
theorem zeta_wider_strict_simple_endpoint :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + widerEtaLower - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  zeta_wider_strict_simple_endpoint_of_le_gain
    widerEtaLower_le_endpoint_gain

/-- Public exact rational form of the wider endpoint theorem. -/
theorem zeta_wider_strict_simple_endpoint_rational :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + (1 : ℝ) / 79828975 - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  simpa [widerEtaLower] using zeta_wider_strict_simple_endpoint

end StrictImprovement
end Zeta23

end
