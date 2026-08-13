/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaEndpointPassage
import Zeta23.StrictImprovement.DirectZetaWiderStrictConcrete
import Zeta23.StrictImprovement.DirectFourPointInterface

/-!
# Endpoint passage for the direct four-point certificate

The theorem in this file is conditional only on the explicit proposition
`DirectFourEndpointCertificate`; the auxiliary taper is fixed before the
height tends to infinity.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

/-- Direct local defect at the `n`-th fixed window, with one endpoint step of
strict slack beyond the loss `18*(1-lam)`. -/
def directEndpointDelta (n : ℕ) : ℝ :=
  directFourEnergyLower / 2 - 19 * endpointStep n

/-- Direct fixed-window coefficient. -/
def directEndpointRate (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) +
    directEndpointDelta n * endpointQ n ^ 2 /
      (8 * (1 + endpointEps n))

/-- Direct endpoint coefficient before its public rational weakening. -/
def directEndpointRateLimit : ℝ :=
  ThmD.HD 1 + directFourEnergyLower / 16 *
    (ThmD.HD 1 - 1 / 2) ^ 2

theorem tendsto_directEndpointDelta :
    Tendsto directEndpointDelta atTop
      (nhds (directFourEnergyLower / 2)) := by
  have h : Tendsto
      (fun n : ℕ => directFourEnergyLower / 2 - 19 * endpointStep n)
      atTop (nhds (directFourEnergyLower / 2 - 19 * 0)) :=
    tendsto_const_nhds.sub (tendsto_endpointStep_zero.const_mul 19)
  change Tendsto
    (fun n : ℕ => directFourEnergyLower / 2 - 19 * endpointStep n)
    atTop (nhds (directFourEnergyLower / 2))
  simpa using h

theorem tendsto_directEndpointRate :
    Tendsto directEndpointRate atTop (nhds directEndpointRateLimit) := by
  have hnum := tendsto_directEndpointDelta.mul (tendsto_endpointQ.pow 2)
  have hden : Tendsto
      (fun n : ℕ => (8 : ℝ) * (1 + endpointStep n)) atTop
      (nhds ((8 : ℝ) * (1 + 0))) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.add tendsto_endpointStep_zero)
  have hgain := hnum.div hden (by norm_num : (8 : ℝ) * (1 + 0) ≠ 0)
  have h := tendsto_endpointHD.add hgain
  have hend :
      ThmD.HD 1 + (directFourEnergyLower / 2) *
          (ThmD.HD 1 - 1 / 2) ^ 2 / (8 * (1 + 0)) =
        directEndpointRateLimit := by
    unfold directEndpointRateLimit
    ring
  rw [← hend]
  change Tendsto (fun n : ℕ => ThmD.HD (endpointLam n) +
    directEndpointDelta n * endpointQ n ^ 2 /
      (8 * (1 + endpointStep n))) atTop _
  exact h

def DirectEndpointFeasible (n : ℕ) : Prop :=
  0 < endpointLam n ∧ endpointLam n < 1 ∧
  0 < endpointEps n ∧
  0 < ThmD.HD (endpointLam n) - endpointEps n ∧
  0 ≤ directEndpointDelta n ∧
  directEndpointDelta n <
    directFourEnergyLower / 2 - 18 * (1 - endpointLam n) ∧
  0 ≤ endpointQ n

theorem eventually_directEndpointFeasible :
    ∀ᶠ n in atTop, DirectEndpointFeasible n := by
  have hlamPos : ∀ᶠ n in atTop, 0 < endpointLam n :=
    tendsto_endpointLam_one.eventually (Ioi_mem_nhds one_pos)
  have hdeltaPos : ∀ᶠ n in atTop, 0 < directEndpointDelta n := by
    have h0 : 0 < directFourEnergyLower / 2 := by
      norm_num [directFourEnergyLower]
    exact tendsto_directEndpointDelta.eventually (Ioi_mem_nhds h0)
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
      (Ioi_mem_nhds (by linarith [one_sixth_lt_HD_one_sub_half]))
  filter_upwards [hlamPos, hdeltaPos, hHpos, hqPos]
    with n hlam hdelta hH hq
  refine ⟨hlam, endpointLam_lt_one n, ?_, hH, hdelta.le, ?_, hq.le⟩
  · simpa [endpointEps] using endpointStep_pos n
  · unfold directEndpointDelta endpointLam
    nlinarith [endpointStep_pos n]

/-- Conditional endpoint passage for any certified lower bound on the direct
quadratic gain. -/
theorem zeta_direct_strict_simple_endpoint_of_le_gain
    (hcertificate : DirectFourEndpointCertificate)
    {eta : ℝ}
    (heta : eta ≤ directFourEnergyLower / 16 *
      (ThmD.HD 1 - 1 / 2) ^ 2) :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + eta - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  intro outer houter
  have hclose : ∀ᶠ n in atTop,
      directEndpointRateLimit - outer / 2 < directEndpointRate n :=
    tendsto_directEndpointRate.eventually
      (Ioi_mem_nhds (by linarith :
        directEndpointRateLimit - outer / 2 < directEndpointRateLimit))
  obtain ⟨n, hn, hrate⟩ :=
    (eventually_directEndpointFeasible.and hclose).exists
  rcases hn with
    ⟨hlam0, hlam1, heps, hH, hdelta, hdeltaLim, hq⟩
  obtain ⟨T₀, hT₀⟩ := zeta_direct_strict_simple_fixed_lam
    hcertificate hlam0 hlam1 heps hH hdelta hdeltaLim hq
    (outer / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have hfixed := hT₀ T hT
  have hcoef :
      ThmD.HD 1 + eta - outer ≤
        directEndpointRate n - outer / 2 := by
    unfold directEndpointRateLimit at hrate
    linarith
  exact le_trans
    (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) hfixed

/-- **Conditional direct four-point strict endpoint improvement.** -/
theorem zeta_direct_strict_simple_endpoint
    (hcertificate : DirectFourEndpointCertificate) :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + directFourEtaLower - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  zeta_direct_strict_simple_endpoint_of_le_gain
    hcertificate directFourEtaLower_le_endpoint_gain

/-- Public rational form, still explicitly conditional on the external
coordinate-free endpoint certificate. -/
theorem zeta_direct_strict_simple_endpoint_rational
    (hcertificate : DirectFourEndpointCertificate) :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + (1 : ℝ) / 2150796 - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  simpa [directFourEtaLower] using
    zeta_direct_strict_simple_endpoint hcertificate

end StrictImprovement
end Zeta23

end
