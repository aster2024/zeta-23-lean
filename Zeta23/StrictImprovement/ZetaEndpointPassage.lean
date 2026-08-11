/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaStrictConcrete
import Zeta23.StrictImprovement.ZetaEndpointConstant

/-!
# The fixed-parameter passage to the endpoint

The fixed-`lam` theorem must be applied with parameters that remain fixed as
`T -> infinity`.  This file therefore uses the auxiliary sequence

`eps n = 1/(n+1)`, `lam n = 1-eps n`,
`delta n = explicitDeltaLower - 19*eps n`.

For one sufficiently large, but then fixed, `n`, all hypotheses of the
fixed-`lam` theorem hold.  Only after invoking that theorem do we let `T`
tend to infinity.  The coefficient sequence converges to the exact endpoint
gain, which is at least `explicitEtaLower`.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

/-- The positive endpoint step `1/(n+1)`. -/
def endpointStep (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- A sequence of fixed window parameters approaching one from the left. -/
def endpointLam (n : ℕ) : ℝ := 1 - endpointStep n

/-- The internal epsilon used at the `n`-th fixed window. -/
def endpointEps (n : ℕ) : ℝ := endpointStep n

/-- The factor `19` leaves a strict unit of endpoint-step slack beyond the
`18 * (1-lam)` loss in the local-delta theorem. -/
def endpointDelta (n : ℕ) : ℝ :=
  explicitDeltaLower - 19 * endpointStep n

/-- The quadratic core-margin at the `n`-th fixed window. -/
def endpointQ (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) - endpointEps n -
    (endpointLam n + endpointEps n) / 2 - endpointEps n

/-- The exact coefficient supplied by the fixed-parameter strict theorem. -/
def endpointRate (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) +
    endpointDelta n * endpointQ n ^ 2 / (9 * (1 + endpointEps n))

/-- The limiting coefficient before replacing the endpoint gain by its
certified rational lower bound. -/
def endpointRateLimit : ℝ :=
  ThmD.HD 1 + explicitDeltaLower / 9 * (ThmD.HD 1 - 1 / 2) ^ 2

lemma endpointStep_pos (n : ℕ) : 0 < endpointStep n := by
  unfold endpointStep
  positivity

lemma endpointStep_le_one (n : ℕ) : endpointStep n ≤ 1 := by
  unfold endpointStep
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  exact (div_le_one (by positivity)).2 hden

lemma endpointLam_mem_Icc (n : ℕ) : endpointLam n ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold endpointLam
    linarith [endpointStep_le_one n]
  · unfold endpointLam
    linarith [endpointStep_pos n]

lemma endpointLam_lt_one (n : ℕ) : endpointLam n < 1 := by
  unfold endpointLam
  linarith [endpointStep_pos n]

theorem tendsto_endpointStep_zero :
    Tendsto endpointStep atTop (nhds 0) := by
  simpa [endpointStep] using tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_endpointLam_one :
    Tendsto endpointLam atTop (nhds 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - endpointStep n)
      atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_endpointStep_zero
  simpa [endpointLam] using h

/-- `HD` is continuous at the endpoint from inside the admissible interval. -/
theorem continuousWithinAt_HD_one :
    ContinuousWithinAt ThmD.HD (Set.Icc (0 : ℝ) 1) 1 := by
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hc : ContinuousWithinAt ThmD.cStar (Set.Icc (0 : ℝ) 1) 1 :=
    ThmD.cStar_continuousOn 1 hone
  have hc0 : ThmD.cStar 1 ≠ 0 :=
    (ThmD.cStar_pos one_pos le_rfl).ne'
  show ContinuousWithinAt (fun lam => 2 - 1 / ThmD.cStar lam)
    (Set.Icc (0 : ℝ) 1) 1
  exact continuousWithinAt_const.sub
    (continuousWithinAt_const.div hc hc0)

theorem tendsto_endpointHD :
    Tendsto (fun n => ThmD.HD (endpointLam n)) atTop
      (nhds (ThmD.HD 1)) := by
  have hwithin :
      Tendsto endpointLam atTop (nhdsWithin 1 (Set.Icc (0 : ℝ) 1)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_endpointLam_one,
        Eventually.of_forall endpointLam_mem_Icc⟩
  exact continuousWithinAt_HD_one.tendsto.comp hwithin

theorem tendsto_endpointDelta :
    Tendsto endpointDelta atTop (nhds explicitDeltaLower) := by
  have h : Tendsto
      (fun n : ℕ => explicitDeltaLower - 19 * endpointStep n)
      atTop (nhds (explicitDeltaLower - 19 * 0)) :=
    tendsto_const_nhds.sub
      (tendsto_endpointStep_zero.const_mul 19)
  simpa [endpointDelta] using h

theorem tendsto_endpointQ :
    Tendsto endpointQ atTop (nhds (ThmD.HD 1 - 1 / 2)) := by
  have hsum := tendsto_endpointLam_one.add tendsto_endpointStep_zero
  have h := ((tendsto_endpointHD.sub tendsto_endpointStep_zero).sub
      (hsum.div_const 2)).sub tendsto_endpointStep_zero
  simpa [endpointQ, endpointEps] using h

/-- The strict fixed-window coefficient converges to the endpoint coefficient;
no window parameter depends on `T` in the theorem invocation. -/
theorem tendsto_endpointRate :
    Tendsto endpointRate atTop (nhds endpointRateLimit) := by
  have hnum := tendsto_endpointDelta.mul (tendsto_endpointQ.pow 2)
  have hden : Tendsto
      (fun n : ℕ => (9 : ℝ) * (1 + endpointStep n)) atTop
      (nhds ((9 : ℝ) * (1 + 0))) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.add tendsto_endpointStep_zero)
  have hgain := hnum.div hden (by norm_num : (9 : ℝ) * (1 + 0) ≠ 0)
  have h := tendsto_endpointHD.add hgain
  convert h using 1 <;>
    simp [endpointRate, endpointRateLimit, endpointEps] <;> ring

/-- The complete collection of hypotheses needed by the fixed-window strict
theorem at one auxiliary index. -/
def EndpointFeasible (n : ℕ) : Prop :=
  0 < endpointLam n ∧ endpointLam n < 1 ∧
  0 < endpointEps n ∧
  0 < ThmD.HD (endpointLam n) - endpointEps n ∧
  0 ≤ endpointDelta n ∧
  endpointDelta n < explicitDeltaLower - 18 * (1 - endpointLam n) ∧
  0 ≤ endpointQ n

/-- Every sufficiently late auxiliary index is feasible. -/
theorem eventually_endpointFeasible :
    ∀ᶠ n in atTop, EndpointFeasible n := by
  have hlamPos : ∀ᶠ n in atTop, 0 < endpointLam n :=
    tendsto_endpointLam_one.eventually (Ioi_mem_nhds one_pos)
  have hdeltaPos : ∀ᶠ n in atTop, 0 < endpointDelta n := by
    have h0 : 0 < explicitDeltaLower := by
      norm_num [explicitDeltaLower]
    exact tendsto_endpointDelta.eventually (Ioi_mem_nhds h0)
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
  · unfold endpointDelta endpointLam
    nlinarith [endpointStep_pos n]

/-- Generic endpoint passage for any certified lower bound on the limiting
quadratic gain. -/
theorem zeta_strict_simple_endpoint_of_le_gain
    {eta : ℝ}
    (heta : eta ≤
      explicitDeltaLower / 9 * (ThmD.HD 1 - 1 / 2) ^ 2) :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + eta - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  intro outer houter
  have hclose : ∀ᶠ n in atTop,
      endpointRateLimit - outer / 2 < endpointRate n :=
    tendsto_endpointRate.eventually
      (Ioi_mem_nhds (by linarith : endpointRateLimit - outer / 2 < endpointRateLimit))
  obtain ⟨n, hn, hrate⟩ := (eventually_endpointFeasible.and hclose).exists
  rcases hn with ⟨hlam0, hlam1, heps, hH, hdelta, hdeltaLim, hq⟩
  obtain ⟨T₀, hT₀⟩ := zeta_strict_simple_fixed_lam
    hlam0 hlam1 heps hH hdelta hdeltaLim hq
    (outer / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have hfixed := hT₀ T hT
  have hcoef :
      ThmD.HD 1 + eta - outer ≤
        endpointRate n - outer / 2 := by
    unfold endpointRateLimit at hrate
    linarith
  exact le_trans
    (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) hfixed

/-- Baseline explicit strict endpoint improvement, dyadic epsilon form. -/
theorem zeta_strict_simple_endpoint :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + explicitEtaLower - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  zeta_strict_simple_endpoint_of_le_gain explicitEtaLower_le_endpoint_gain

/-- The baseline theorem with its original rational constant exposed. -/
theorem zeta_strict_simple_endpoint_baseline_rational :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + (1 : ℝ) / 250050969 - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  simpa [explicitEtaLower] using zeta_strict_simple_endpoint

/-- Intermediate optimization using the unrounded cubic/quartic root bound. -/
theorem zeta_strict_simple_endpoint_unrounded_cubic :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + explicitEtaImproved - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  zeta_strict_simple_endpoint_of_le_gain explicitEtaImproved_le_endpoint_gain

/-- Optimized endpoint theorem using the seventh/eighth-order Taylor pair. -/
theorem zeta_strict_simple_endpoint_optimized :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + explicitEtaTaylor - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  zeta_strict_simple_endpoint_of_le_gain explicitEtaTaylor_le_endpoint_gain

/-- **Taylor-optimized unconditional strict endpoint improvement.**  This
public statement exposes the exact certified rational constant. -/
theorem zeta_strict_simple_endpoint_rational :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + (1 : ℝ) / 233423794 - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  simpa [explicitEtaTaylor] using zeta_strict_simple_endpoint_optimized

end StrictImprovement
end Zeta23

end
