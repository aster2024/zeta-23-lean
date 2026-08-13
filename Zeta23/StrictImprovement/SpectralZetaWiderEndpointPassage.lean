/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaEndpointPassage
import Zeta23.StrictImprovement.SpectralZetaWiderStrictConcrete
import Zeta23.StrictImprovement.SpectralFourPointInterface

/-!
# Endpoint passage for the spectral four-point certificate

The auxiliary taper is fixed before height tends to infinity.  The explicit
mass sequence reserves one endpoint step beyond the limiting stability loss.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

/-- Positive square-root margin used at the `n`-th fixed taper. -/
def spectralEndpointRoot (n : ℕ) : ℝ :=
  Real.sqrt spectralFourMassLower -
    (6 * Real.sqrt 3 + 1) * endpointStep n

/-- Fixed local spectral mass at the `n`-th taper. -/
def spectralEndpointMass (n : ℕ) : ℝ :=
  spectralEndpointRoot n ^ 2

/-- Spectral fixed-window coefficient. -/
def spectralEndpointRate (n : ℕ) : ℝ :=
  ThmD.HD (endpointLam n) +
    spectralEndpointMass n * endpointQ n ^ 2 /
      (16 * (1 + endpointEps n))

/-- Spectral endpoint coefficient before its public rational weakening. -/
def spectralEndpointRateLimit : ℝ :=
  ThmD.HD 1 + spectralFourMassLower / 16 *
    (ThmD.HD 1 - 1 / 2) ^ 2

lemma spectralFourMassLower_pos : 0 < spectralFourMassLower := by
  norm_num [spectralFourMassLower]

theorem tendsto_spectralEndpointRoot :
    Tendsto spectralEndpointRoot atTop
      (nhds (Real.sqrt spectralFourMassLower)) := by
  have hconst : Tendsto (fun _ : ℕ => Real.sqrt spectralFourMassLower)
      atTop (nhds (Real.sqrt spectralFourMassLower)) := tendsto_const_nhds
  have h := hconst.sub
    (tendsto_endpointStep_zero.const_mul (6 * Real.sqrt 3 + 1))
  simpa [spectralEndpointRoot] using h

theorem eventually_spectralEndpointRoot_pos :
    ∀ᶠ n in atTop, 0 < spectralEndpointRoot n :=
  tendsto_spectralEndpointRoot.eventually
    (Ioi_mem_nhds (Real.sqrt_pos.2 spectralFourMassLower_pos))

theorem tendsto_spectralEndpointMass :
    Tendsto spectralEndpointMass atTop (nhds spectralFourMassLower) := by
  have h := tendsto_spectralEndpointRoot.pow 2
  have hsqrt : (Real.sqrt spectralFourMassLower) ^ 2 =
      spectralFourMassLower :=
    Real.sq_sqrt spectralFourMassLower_nonneg
  rw [hsqrt] at h
  change Tendsto (fun n : ℕ => spectralEndpointRoot n ^ 2) atTop
    (nhds spectralFourMassLower)
  exact h

theorem tendsto_spectralEndpointRate :
    Tendsto spectralEndpointRate atTop
      (nhds spectralEndpointRateLimit) := by
  have hnum := tendsto_spectralEndpointMass.mul (tendsto_endpointQ.pow 2)
  have hden : Tendsto
      (fun n : ℕ => (16 : ℝ) * (1 + endpointStep n)) atTop
      (nhds ((16 : ℝ) * (1 + 0))) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.add tendsto_endpointStep_zero)
  have hgain := hnum.div hden (by norm_num : (16 : ℝ) * (1 + 0) ≠ 0)
  have h := tendsto_endpointHD.add hgain
  have hend :
      ThmD.HD 1 + spectralFourMassLower *
          (ThmD.HD 1 - 1 / 2) ^ 2 / (16 * (1 + 0)) =
        spectralEndpointRateLimit := by
    unfold spectralEndpointRateLimit
    ring
  rw [← hend]
  change Tendsto (fun n : ℕ => ThmD.HD (endpointLam n) +
    spectralEndpointMass n * endpointQ n ^ 2 /
      (16 * (1 + endpointStep n))) atTop _
  exact h

/-- Complete fixed-window feasibility conditions for the spectral route. -/
def SpectralEndpointFeasible (n : ℕ) : Prop :=
  0 < endpointLam n ∧ endpointLam n < 1 ∧
  0 < endpointEps n ∧
  0 < ThmD.HD (endpointLam n) - endpointEps n ∧
  0 ≤ spectralEndpointMass n ∧
  Real.sqrt (spectralEndpointMass n) +
      6 * Real.sqrt 3 * (1 - endpointLam n) <
    Real.sqrt spectralFourMassLower ∧
  0 ≤ endpointQ n

theorem eventually_spectralEndpointFeasible :
    ∀ᶠ n in atTop, SpectralEndpointFeasible n := by
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
  have hqPos : ∀ᶠ n in atTop, 0 < endpointQ n :=
    tendsto_endpointQ.eventually
      (Ioi_mem_nhds (by linarith [one_sixth_lt_HD_one_sub_half]))
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

/-- Conditional endpoint passage for any lower bound on the limiting spectral
gain. -/
theorem zeta_spectral_strict_simple_endpoint_of_le_gain
    (hcertificate : SpectralFourEndpointCertificate)
    {eta : ℝ}
    (heta : eta ≤ spectralFourMassLower / 16 *
      (ThmD.HD 1 - 1 / 2) ^ 2) :
    ∀ outer > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (ThmD.HD 1 + eta - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  intro outer houter
  have hclose : ∀ᶠ n in atTop,
      spectralEndpointRateLimit - outer / 2 < spectralEndpointRate n :=
    tendsto_spectralEndpointRate.eventually
      (Ioi_mem_nhds (by linarith :
        spectralEndpointRateLimit - outer / 2 < spectralEndpointRateLimit))
  obtain ⟨n, hn, hrate⟩ :=
    (eventually_spectralEndpointFeasible.and hclose).exists
  rcases hn with
    ⟨hlam0, hlam1, heps, hH, hm, hmargin, hq⟩
  obtain ⟨T0, hT0⟩ := zeta_spectral_strict_simple_fixed_lam
    hcertificate hlam0 hlam1 heps hH hm hmargin hq
    (outer / 2) (by linarith)
  refine ⟨T0, fun T hT => ?_⟩
  have hfixed := hT0 T hT
  have hcoef :
      ThmD.HD 1 + eta - outer ≤
        spectralEndpointRate n - outer / 2 := by
    unfold spectralEndpointRateLimit at hrate
    linarith
  exact le_trans
    (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) hfixed

/-- Conditional spectral four-point strict endpoint improvement. -/
theorem zeta_spectral_strict_simple_endpoint
    (hcertificate : SpectralFourEndpointCertificate) :
    ∀ outer > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (ThmD.HD 1 + spectralFourEtaLower - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  zeta_spectral_strict_simple_endpoint_of_le_gain
    hcertificate spectralFourEtaLower_le_endpoint_gain

/-- Public rational form, explicitly conditional on the external endpoint
interval certificate. -/
theorem zeta_spectral_strict_simple_endpoint_rational
    (hcertificate : SpectralFourEndpointCertificate) :
    ∀ outer > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (ThmD.HD 1 + (1 : ℝ) / 914088 - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  simpa [spectralFourEtaLower] using
    zeta_spectral_strict_simple_endpoint hcertificate

end StrictImprovement
end Zeta23

end
