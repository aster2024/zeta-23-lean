/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q6SuperbinEndpointInterface

/-!
# Explicit endpoint interfaces for the full-spectral q7 superbin repair

The stronger q6 and q7 interval certificates remain proposition-valued
inputs.  This file checks only their conversion to trace-norm rewards and the
generic finite/full entrywise stability estimates.
-/

noncomputable section

open Matrix Real
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

/-- Raised six-point endpoint certificate supported by the frozen q6 Taylor
inventory.  It is kept explicit rather than silently strengthening the public
q6 certificate. -/
def Q7FullSpectralSixEndpointCertificate : Prop :=
  ∀ x : Fin 6 → ℝ,
    (∀ i : Fin 6, i.val < 3 → 0 ≤ x i ∧ x i ≤ 16 * Real.pi) →
    (∀ i : Fin 6, 3 ≤ i.val → 16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) →
      (1849 : ℝ) / 25000000 <
        (Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2) ^ 2

/-- The seven-point certificate records both orientations of the adjacent
`3+4` split.  The external finite certificate verifies one orientation and
the other follows by reflection; both remain visible in the trusted input. -/
structure Q7FullSpectralSevenEndpointCertificate : Prop where
  threeFour :
    ∀ x : Fin 7 → ℝ,
      (∀ i : Fin 7, i.val < 3 → 0 ≤ x i ∧ x i ≤ 16 * Real.pi) →
      (∀ i : Fin 7, 3 ≤ i.val → 16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) →
        (556854735529 : ℝ) / 2500000000000000 <
          (Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2) ^ 2
  fourThree :
    ∀ x : Fin 7 → ℝ,
      (∀ i : Fin 7, i.val < 4 → 0 ≤ x i ∧ x i ≤ 16 * Real.pi) →
      (∀ i : Fin 7, 4 ≤ i.val → 16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) →
        (556854735529 : ℝ) / 2500000000000000 <
          (Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2) ^ 2

/-- Existing q3/q4/q5 inputs together with raised q6 and oriented q7 inputs. -/
structure Q7FullSpectralEndpointCertificates : Prop where
  base : WideRepairEndpointCertificates
  six : Q7FullSpectralSixEndpointCertificate
  seven : Q7FullSpectralSevenEndpointCertificate

def q7FullSpectralSixReward : ℝ := 43 / 5000
def q7FullSpectralSevenReward : ℝ := 746227 / 50000000

lemma q7FullSpectralSixReward_nonneg : 0 ≤ q7FullSpectralSixReward := by
  norm_num [q7FullSpectralSixReward]

lemma q7FullSpectralSevenReward_nonneg : 0 ≤ q7FullSpectralSevenReward := by
  norm_num [q7FullSpectralSevenReward]

lemma q7FullSpectralSixReward_sq : q7FullSpectralSixReward ^ 2 =
    (1849 : ℝ) / 25000000 := by
  norm_num [q7FullSpectralSixReward]

lemma q7FullSpectralSevenReward_sq : q7FullSpectralSevenReward ^ 2 =
    (556854735529 : ℝ) / 2500000000000000 := by
  norm_num [q7FullSpectralSevenReward]

theorem q7FullSpectral_six_endpoint_traceNorm_lower
    (hcertificate : Q7FullSpectralSixEndpointCertificate)
    (x : Fin 6 → ℝ)
    (hleft : ∀ i : Fin 6, i.val < 3 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 6, 3 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) :
    2 * q7FullSpectralSixReward ≤
      Tail.traceNorm (wideEndpointDeviation_isHermitian x) := by
  have hcert := hcertificate x hleft hright
  have htrace0 :
      0 ≤ Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  rw [← q7FullSpectralSixReward_sq] at hcert
  have hreward0 := q7FullSpectralSixReward_nonneg
  nlinarith

theorem q7FullSpectral_seven_threeFour_endpoint_traceNorm_lower
    (hcertificate : Q7FullSpectralSevenEndpointCertificate)
    (x : Fin 7 → ℝ)
    (hleft : ∀ i : Fin 7, i.val < 3 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 7, 3 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) :
    2 * q7FullSpectralSevenReward ≤
      Tail.traceNorm (wideEndpointDeviation_isHermitian x) := by
  have hcert := hcertificate.threeFour x hleft hright
  have htrace0 :
      0 ≤ Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  rw [← q7FullSpectralSevenReward_sq] at hcert
  have hreward0 := q7FullSpectralSevenReward_nonneg
  nlinarith

theorem q7FullSpectral_seven_fourThree_endpoint_traceNorm_lower
    (hcertificate : Q7FullSpectralSevenEndpointCertificate)
    (x : Fin 7 → ℝ)
    (hleft : ∀ i : Fin 7, i.val < 4 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 7, 4 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) :
    2 * q7FullSpectralSevenReward ≤
      Tail.traceNorm (wideEndpointDeviation_isHermitian x) := by
  have hcert := hcertificate.fourThree x hleft hright
  have htrace0 :
      0 ≤ Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  rw [← q7FullSpectralSevenReward_sq] at hcert
  have hreward0 := q7FullSpectralSevenReward_nonneg
  nlinarith

theorem q7FullSpectral_six_nearby_traceNorm_lower
    (hcertificate : Q7FullSpectralSixEndpointCertificate)
    (x : Fin 6 → ℝ)
    (hleft : ∀ i : Fin 6, i.val < 3 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 6, 3 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi)
    {B : Matrix (Fin 6) (Fin 6) ℂ} (hB : B.IsHermitian)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ i j, ‖B i j - wideEndpointDeviation x i j‖ ≤ eps)
    (hmargin : scale * q7FullSpectralSixReward +
      3 * Real.sqrt 6 * eps ≤ q7FullSpectralSixReward) :
    2 * (scale * q7FullSpectralSixReward) ≤ Tail.traceNorm hB := by
  have hstable := half_traceNorm_sub_le_card_sqrt_card_eps hB
    (wideEndpointDeviation_isHermitian x) heps hclose
  have hend := q7FullSpectral_six_endpoint_traceNorm_lower
    hcertificate x hleft hright
  norm_num at hstable
  have hlower := (abs_le.mp hstable).1
  linarith

theorem q7FullSpectral_seven_threeFour_nearby_traceNorm_lower
    (hcertificate : Q7FullSpectralSevenEndpointCertificate)
    (x : Fin 7 → ℝ)
    (hleft : ∀ i : Fin 7, i.val < 3 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 7, 3 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi)
    {B : Matrix (Fin 7) (Fin 7) ℂ} (hB : B.IsHermitian)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ i j, ‖B i j - wideEndpointDeviation x i j‖ ≤ eps)
    (hmargin : scale * q7FullSpectralSevenReward +
      (7 * Real.sqrt 7 / 2) * eps ≤ q7FullSpectralSevenReward) :
    2 * (scale * q7FullSpectralSevenReward) ≤ Tail.traceNorm hB := by
  have hstable := half_traceNorm_sub_le_card_sqrt_card_eps hB
    (wideEndpointDeviation_isHermitian x) heps hclose
  have hend := q7FullSpectral_seven_threeFour_endpoint_traceNorm_lower
    hcertificate x hleft hright
  norm_num at hstable
  have hlower := (abs_le.mp hstable).1
  linarith

theorem q7FullSpectral_seven_fourThree_nearby_traceNorm_lower
    (hcertificate : Q7FullSpectralSevenEndpointCertificate)
    (x : Fin 7 → ℝ)
    (hleft : ∀ i : Fin 7, i.val < 4 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 7, 4 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi)
    {B : Matrix (Fin 7) (Fin 7) ℂ} (hB : B.IsHermitian)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ i j, ‖B i j - wideEndpointDeviation x i j‖ ≤ eps)
    (hmargin : scale * q7FullSpectralSevenReward +
      (7 * Real.sqrt 7 / 2) * eps ≤ q7FullSpectralSevenReward) :
    2 * (scale * q7FullSpectralSevenReward) ≤ Tail.traceNorm hB := by
  have hstable := half_traceNorm_sub_le_card_sqrt_card_eps hB
    (wideEndpointDeviation_isHermitian x) heps hclose
  have hend := q7FullSpectral_seven_fourThree_endpoint_traceNorm_lower
    hcertificate x hleft hright
  norm_num at hstable
  have hlower := (abs_le.mp hstable).1
  linarith

end StrictImprovement
end Zeta23

end
