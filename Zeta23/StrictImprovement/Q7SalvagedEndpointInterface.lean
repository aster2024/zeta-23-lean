/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q6SuperbinEndpointInterface

/-!
# Explicit endpoint interfaces for the salvaged q7 superbin repair

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
def Q7SalvagedSixEndpointCertificate : Prop :=
  ∀ x : Fin 6 → ℝ,
    (∀ i : Fin 6, i.val < 3 → 0 ≤ x i ∧ x i ≤ 16 * Real.pi) →
    (∀ i : Fin 6, 3 ≤ i.val → 16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) →
      (161702907129 : ℝ) / 2500000000000000 <
        (Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2) ^ 2

/-- The seven-point certificate records both orientations of the adjacent
`3+4` split.  The external finite certificate verifies one orientation and
the other follows by reflection; both remain visible in the trusted input. -/
structure Q7SalvagedSevenEndpointCertificate : Prop where
  threeFour :
    ∀ x : Fin 7 → ℝ,
      (∀ i : Fin 7, i.val < 3 → 0 ≤ x i ∧ x i ≤ 16 * Real.pi) →
      (∀ i : Fin 7, 3 ≤ i.val → 16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) →
        (206410689 : ℝ) / 1000000000000 <
          (Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2) ^ 2
  fourThree :
    ∀ x : Fin 7 → ℝ,
      (∀ i : Fin 7, i.val < 4 → 0 ≤ x i ∧ x i ≤ 16 * Real.pi) →
      (∀ i : Fin 7, 4 ≤ i.val → 16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) →
        (206410689 : ℝ) / 1000000000000 <
          (Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2) ^ 2

/-- Existing q3/q4/q5 inputs together with raised q6 and oriented q7 inputs. -/
structure Q7SalvagedEndpointCertificates : Prop where
  base : WideRepairEndpointCertificates
  six : Q7SalvagedSixEndpointCertificate
  seven : Q7SalvagedSevenEndpointCertificate

def q7SalvagedSixReward : ℝ := 402123 / 50000000
def q7SalvagedSevenReward : ℝ := 14367 / 1000000

lemma q7SalvagedSixReward_nonneg : 0 ≤ q7SalvagedSixReward := by
  norm_num [q7SalvagedSixReward]

lemma q7SalvagedSevenReward_nonneg : 0 ≤ q7SalvagedSevenReward := by
  norm_num [q7SalvagedSevenReward]

lemma q7SalvagedSixReward_sq : q7SalvagedSixReward ^ 2 =
    (161702907129 : ℝ) / 2500000000000000 := by
  norm_num [q7SalvagedSixReward]

lemma q7SalvagedSevenReward_sq : q7SalvagedSevenReward ^ 2 =
    (206410689 : ℝ) / 1000000000000 := by
  norm_num [q7SalvagedSevenReward]

theorem q7Salvaged_six_endpoint_traceNorm_lower
    (hcertificate : Q7SalvagedSixEndpointCertificate)
    (x : Fin 6 → ℝ)
    (hleft : ∀ i : Fin 6, i.val < 3 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 6, 3 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) :
    2 * q7SalvagedSixReward ≤
      Tail.traceNorm (wideEndpointDeviation_isHermitian x) := by
  have hcert := hcertificate x hleft hright
  have htrace0 :
      0 ≤ Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  rw [← q7SalvagedSixReward_sq] at hcert
  have hreward0 := q7SalvagedSixReward_nonneg
  nlinarith

theorem q7Salvaged_seven_threeFour_endpoint_traceNorm_lower
    (hcertificate : Q7SalvagedSevenEndpointCertificate)
    (x : Fin 7 → ℝ)
    (hleft : ∀ i : Fin 7, i.val < 3 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 7, 3 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) :
    2 * q7SalvagedSevenReward ≤
      Tail.traceNorm (wideEndpointDeviation_isHermitian x) := by
  have hcert := hcertificate.threeFour x hleft hright
  have htrace0 :
      0 ≤ Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  rw [← q7SalvagedSevenReward_sq] at hcert
  have hreward0 := q7SalvagedSevenReward_nonneg
  nlinarith

theorem q7Salvaged_seven_fourThree_endpoint_traceNorm_lower
    (hcertificate : Q7SalvagedSevenEndpointCertificate)
    (x : Fin 7 → ℝ)
    (hleft : ∀ i : Fin 7, i.val < 4 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 7, 4 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) :
    2 * q7SalvagedSevenReward ≤
      Tail.traceNorm (wideEndpointDeviation_isHermitian x) := by
  have hcert := hcertificate.fourThree x hleft hright
  have htrace0 :
      0 ≤ Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  rw [← q7SalvagedSevenReward_sq] at hcert
  have hreward0 := q7SalvagedSevenReward_nonneg
  nlinarith

theorem q7Salvaged_six_nearby_traceNorm_lower
    (hcertificate : Q7SalvagedSixEndpointCertificate)
    (x : Fin 6 → ℝ)
    (hleft : ∀ i : Fin 6, i.val < 3 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 6, 3 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi)
    {B : Matrix (Fin 6) (Fin 6) ℂ} (hB : B.IsHermitian)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ i j, ‖B i j - wideEndpointDeviation x i j‖ ≤ eps)
    (hmargin : scale * q7SalvagedSixReward +
      3 * Real.sqrt 6 * eps ≤ q7SalvagedSixReward) :
    2 * (scale * q7SalvagedSixReward) ≤ Tail.traceNorm hB := by
  have hstable := half_traceNorm_sub_le_card_sqrt_card_eps hB
    (wideEndpointDeviation_isHermitian x) heps hclose
  have hend := q7Salvaged_six_endpoint_traceNorm_lower
    hcertificate x hleft hright
  norm_num at hstable
  have hlower := (abs_le.mp hstable).1
  linarith

theorem q7Salvaged_seven_threeFour_nearby_traceNorm_lower
    (hcertificate : Q7SalvagedSevenEndpointCertificate)
    (x : Fin 7 → ℝ)
    (hleft : ∀ i : Fin 7, i.val < 3 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 7, 3 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi)
    {B : Matrix (Fin 7) (Fin 7) ℂ} (hB : B.IsHermitian)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ i j, ‖B i j - wideEndpointDeviation x i j‖ ≤ eps)
    (hmargin : scale * q7SalvagedSevenReward +
      (7 * Real.sqrt 7 / 2) * eps ≤ q7SalvagedSevenReward) :
    2 * (scale * q7SalvagedSevenReward) ≤ Tail.traceNorm hB := by
  have hstable := half_traceNorm_sub_le_card_sqrt_card_eps hB
    (wideEndpointDeviation_isHermitian x) heps hclose
  have hend := q7Salvaged_seven_threeFour_endpoint_traceNorm_lower
    hcertificate x hleft hright
  norm_num at hstable
  have hlower := (abs_le.mp hstable).1
  linarith

theorem q7Salvaged_seven_fourThree_nearby_traceNorm_lower
    (hcertificate : Q7SalvagedSevenEndpointCertificate)
    (x : Fin 7 → ℝ)
    (hleft : ∀ i : Fin 7, i.val < 4 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 7, 4 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi)
    {B : Matrix (Fin 7) (Fin 7) ℂ} (hB : B.IsHermitian)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ i j, ‖B i j - wideEndpointDeviation x i j‖ ≤ eps)
    (hmargin : scale * q7SalvagedSevenReward +
      (7 * Real.sqrt 7 / 2) * eps ≤ q7SalvagedSevenReward) :
    2 * (scale * q7SalvagedSevenReward) ≤ Tail.traceNorm hB := by
  have hstable := half_traceNorm_sub_le_card_sqrt_card_eps hB
    (wideEndpointDeviation_isHermitian x) heps hclose
  have hend := q7Salvaged_seven_fourThree_endpoint_traceNorm_lower
    hcertificate x hleft hright
  norm_num at hstable
  have hlower := (abs_le.mp hstable).1
  linarith

end StrictImprovement
end Zeta23

end
