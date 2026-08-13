/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.SpectralZetaWiderEndpointPassage
import Zeta23.StrictImprovement.CertificateSlackZetaStrictConcrete
import Zeta23.StrictImprovement.CertificateSlackArithmetic

/-!
# Endpoint passage consuming the full certificate diameter

The taper is fixed before height tends to infinity.  The endpoint spectral
mass and stability reserve are unchanged; the packing loss improves from
`1/2` to `7*pi/44`.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

/-- Fixed-taper positive part before truncation for the widened bins. -/
def certificateSlackEndpointQ (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) -
    (7 * Real.pi / 44) * (endpointLam n + endpointEps n) -
    endpointEps n

/-- Widened-bin spectral fixed-window coefficient. -/
def certificateSlackEndpointRate (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) +
    spectralEndpointMass n * certificateSlackEndpointQ n ^ 2 /
      (16 * (1 + endpointEps n))

/-- Widened-bin endpoint coefficient before its public rational weakening. -/
def certificateSlackEndpointRateLimit : ℝ :=
  ThmD.HD 1 + spectralFourMassLower / 16 *
    (ThmD.HD 1 - 7 * Real.pi / 44) ^ 2

theorem tendsto_certificateSlackEndpointQ :
    Tendsto certificateSlackEndpointQ atTop
      (nhds (ThmD.HD 1 - 7 * Real.pi / 44)) := by
  have hsum := tendsto_endpointLam_one.add tendsto_endpointStep_zero
  have hscaled := hsum.const_mul (7 * Real.pi / 44)
  have h := (tendsto_endpointHD.sub hscaled).sub tendsto_endpointStep_zero
  change Tendsto
    (fun n : ℕ => ThmD.HD (endpointLam n) -
      (7 * Real.pi / 44) * (endpointLam n + endpointEps n) -
      endpointEps n) atTop _
  simpa only [endpointEps, add_zero, mul_one, sub_zero] using h

theorem tendsto_certificateSlackEndpointRate :
    Tendsto certificateSlackEndpointRate atTop
      (nhds certificateSlackEndpointRateLimit) := by
  have hnum := tendsto_spectralEndpointMass.mul
    (tendsto_certificateSlackEndpointQ.pow 2)
  have hden : Tendsto
      (fun n : ℕ => (16 : ℝ) * (1 + endpointStep n)) atTop
      (nhds ((16 : ℝ) * (1 + 0))) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.add tendsto_endpointStep_zero)
  have hgain := hnum.div hden (by norm_num : (16 : ℝ) * (1 + 0) ≠ 0)
  have h := tendsto_endpointHD.add hgain
  have hend :
      ThmD.HD 1 + spectralFourMassLower *
          (ThmD.HD 1 - 7 * Real.pi / 44) ^ 2 / (16 * (1 + 0)) =
        certificateSlackEndpointRateLimit := by
    unfold certificateSlackEndpointRateLimit
    ring
  rw [← hend]
  change Tendsto (fun n : ℕ => ThmD.HD (endpointLam n) +
    spectralEndpointMass n * certificateSlackEndpointQ n ^ 2 /
      (16 * (1 + endpointStep n))) atTop _
  exact h

/-- Complete fixed-window feasibility conditions for the widened-bin route. -/
def CertificateSlackEndpointFeasible (n : ℕ) : Prop :=
  0 < endpointLam n ∧ endpointLam n < 1 ∧
  0 < endpointEps n ∧
  0 < ThmD.HD (endpointLam n) - endpointEps n ∧
  0 ≤ spectralEndpointMass n ∧
  Real.sqrt (spectralEndpointMass n) +
      6 * Real.sqrt 3 * (1 - endpointLam n) <
    Real.sqrt spectralFourMassLower ∧
  0 ≤ certificateSlackEndpointQ n

theorem eventually_certificateSlackEndpointFeasible :
    ∀ᶠ n in atTop, CertificateSlackEndpointFeasible n := by
  have hlamPos : ∀ᶠ n in atTop, 0 < endpointLam n :=
    tendsto_endpointLam_one.eventually (Ioi_mem_nhds one_pos)
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
  have hqLimit : 0 < ThmD.HD 1 - 7 * Real.pi / 44 := by
    have hlower : 0 < certificateSlackMarginLower := by
      norm_num [certificateSlackMarginLower]
    exact hlower.trans certificateSlackMarginLower_lt_endpointMargin
  have hqPos : ∀ᶠ n in atTop, 0 < certificateSlackEndpointQ n :=
    tendsto_certificateSlackEndpointQ.eventually (Ioi_mem_nhds hqLimit)
  filter_upwards [hlamPos, eventually_spectralEndpointRoot_pos, hHpos, hqPos]
    with n hlam hroot hH hq
  refine ⟨hlam, endpointLam_lt_one n, ?_, hH,
    sq_nonneg (spectralEndpointRoot n), ?_, hq.le⟩
  · simpa [endpointEps] using endpointStep_pos n
  · have hsqrt : Real.sqrt (spectralEndpointMass n) =
        spectralEndpointRoot n := by
      rw [spectralEndpointMass, Real.sqrt_sq hroot.le]
    rw [hsqrt]
    calc
      spectralEndpointRoot n +
          6 * Real.sqrt 3 * (1 - endpointLam n) =
        Real.sqrt spectralFourMassLower - endpointStep n := by
          unfold spectralEndpointRoot endpointLam
          ring
      _ < Real.sqrt spectralFourMassLower := by
        linarith [endpointStep_pos n]

/-- Conditional endpoint passage for any lower bound on the widened-bin
limiting spectral gain. -/
theorem zeta_certificate_slack_spectral_endpoint_of_le_gain
    (hcertificate : SpectralFourEndpointSlackCertificate)
    {eta : ℝ}
    (heta : eta ≤ spectralFourMassLower / 16 *
      (ThmD.HD 1 - 7 * Real.pi / 44) ^ 2) :
    ∀ outer > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (ThmD.HD 1 + eta - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  intro outer houter
  have hclose : ∀ᶠ n in atTop,
      certificateSlackEndpointRateLimit - outer / 2 <
        certificateSlackEndpointRate n :=
    tendsto_certificateSlackEndpointRate.eventually
      (Ioi_mem_nhds (by linarith :
        certificateSlackEndpointRateLimit - outer / 2 <
          certificateSlackEndpointRateLimit))
  obtain ⟨n, hn, hrate⟩ :=
    (eventually_certificateSlackEndpointFeasible.and hclose).exists
  rcases hn with
    ⟨hlam0, hlam1, heps, hH, hm, hmargin, hq⟩
  obtain ⟨T0, hT0⟩ :=
    zeta_certificate_slack_spectral_strict_simple_fixed_lam
      hcertificate hlam0 hlam1 heps hH hm hmargin hq
      (outer / 2) (by linarith)
  refine ⟨T0, fun T hT => ?_⟩
  have hfixed := hT0 T hT
  have hcoef :
      ThmD.HD 1 + eta - outer ≤
        certificateSlackEndpointRate n - outer / 2 := by
    unfold certificateSlackEndpointRateLimit at hrate
    linarith
  exact le_trans
    (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) hfixed

theorem certificateSlack_public_le_endpoint_gain :
    (1 : ℝ) / 911960 ≤ spectralFourMassLower / 16 *
      (ThmD.HD 1 - 7 * Real.pi / 44) ^ 2 := by
  have hlower : 0 < certificateSlackMarginLower := by
    norm_num [certificateSlackMarginLower]
  have hmargin := certificateSlackMarginLower_lt_endpointMargin
  have hsquare : certificateSlackMarginLower ^ 2 <
      (ThmD.HD 1 - 7 * Real.pi / 44) ^ 2 := by
    nlinarith [sq_nonneg
      ((ThmD.HD 1 - 7 * Real.pi / 44) - certificateSlackMarginLower)]
  have hmul : spectralFourMassLower / 16 *
      certificateSlackMarginLower ^ 2 <
      spectralFourMassLower / 16 *
        (ThmD.HD 1 - 7 * Real.pi / 44) ^ 2 := by
    exact mul_lt_mul_of_pos_left hsquare (by
      positivity)
  exact (certificateSlack_public_lt_exact_gain.le.trans hmul.le)

/-- Public rational form, explicitly conditional on the retained full-domain
endpoint interval certificate. -/
theorem zeta_certificate_slack_spectral_endpoint_rational
    (hcertificate : SpectralFourEndpointSlackCertificate) :
    ∀ outer > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (ThmD.HD 1 + (1 : ℝ) / 911960 - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  zeta_certificate_slack_spectral_endpoint_of_le_gain
    hcertificate certificateSlack_public_le_endpoint_gain

end StrictImprovement
end Zeta23

end
