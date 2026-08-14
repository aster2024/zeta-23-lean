/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WideRepairEndpointInterface

/-!
# Explicit six-point superbin endpoint interface

The interval certificate remains an explicit proposition-valued input.  This
module kernel-checks only its conversion to a trace-norm reward and the
finite/full perturbation estimate used downstream.
-/

noncomputable section

open Matrix Real
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

/-- External six-point certificate for three coordinates in each half of a
width-`32*pi` superbin. -/
def Q6SuperbinEndpointCertificate : Prop :=
  ∀ x : Fin 6 → ℝ,
    (∀ i : Fin 6, i.val < 3 → 0 ≤ x i ∧ x i ≤ 16 * Real.pi) →
    (∀ i : Fin 6, 3 ≤ i.val → 16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) →
      (46416969 : ℝ) / 722500000000 <
        (Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2) ^ 2

/-- Existing q3/q4/q5 inputs together with the new explicit q6 input. -/
structure Q6SuperbinEndpointCertificates : Prop where
  base : WideRepairEndpointCertificates
  six : Q6SuperbinEndpointCertificate

/-- Saturated six-point reward used only for the `(3,3)` residue pair. -/
def q6SuperbinReward : ℝ := 6813 / 850000

lemma q6SuperbinReward_nonneg : 0 ≤ q6SuperbinReward := by
  norm_num [q6SuperbinReward]

lemma q6SuperbinReward_sq : q6SuperbinReward ^ 2 =
    (46416969 : ℝ) / 722500000000 := by
  norm_num [q6SuperbinReward]

theorem q6Superbin_endpoint_traceNorm_lower
    (hcertificate : Q6SuperbinEndpointCertificate)
    (x : Fin 6 → ℝ)
    (hleft : ∀ i : Fin 6, i.val < 3 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 6, 3 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi) :
    2 * q6SuperbinReward ≤
      Tail.traceNorm (wideEndpointDeviation_isHermitian x) := by
  have hcert := hcertificate x hleft hright
  have htrace0 :
      0 ≤ Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  rw [← q6SuperbinReward_sq] at hcert
  have hreward0 := q6SuperbinReward_nonneg
  nlinarith

/-- A finite six-block retains its scaled endpoint reward under the generic
entrywise trace-norm perturbation bound. -/
theorem q6Superbin_nearby_traceNorm_lower
    (hcertificate : Q6SuperbinEndpointCertificate)
    (x : Fin 6 → ℝ)
    (hleft : ∀ i : Fin 6, i.val < 3 →
      0 ≤ x i ∧ x i ≤ 16 * Real.pi)
    (hright : ∀ i : Fin 6, 3 ≤ i.val →
      16 * Real.pi ≤ x i ∧ x i ≤ 32 * Real.pi)
    {B : Matrix (Fin 6) (Fin 6) ℂ} (hB : B.IsHermitian)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ i j, ‖B i j - wideEndpointDeviation x i j‖ ≤ eps)
    (hmargin : scale * q6SuperbinReward +
      3 * Real.sqrt 6 * eps ≤ q6SuperbinReward) :
    2 * (scale * q6SuperbinReward) ≤ Tail.traceNorm hB := by
  have hstable := half_traceNorm_sub_le_card_sqrt_card_eps hB
    (wideEndpointDeviation_isHermitian x) heps hclose
  have hend := q6Superbin_endpoint_traceNorm_lower hcertificate x hleft hright
  norm_num at hstable
  have hlower := (abs_le.mp hstable).1
  linarith

end StrictImprovement
end Zeta23

end
