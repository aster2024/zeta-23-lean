/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7SalvagedEndpointArithmetic
import Zeta23.StrictImprovement.Q7SalvagedZetaStrictConcrete

/-!
# Endpoint passage for salvaged q7 superbin packing

The taper is fixed before height tends to infinity.  The external q3--q7
interval certificates remain explicit hypotheses of the public theorem.
-/

noncomputable section

open Filter Topology Real

namespace Zeta23
namespace StrictImprovement

theorem zeta_q7Salvaged_strict_simple_endpoint_of_le_gain
    (hcertificates : Q7SalvagedEndpointCertificates)
    {eta : ℝ}
    (heta : eta ≤ wideRepairAlpha ^ 2 *
      (ThmD.HD 1 - q7SalvagedPackingLoss) ^ 2) :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + eta - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  intro outer houter
  have hclose : ∀ᶠ n in atTop,
      q7SalvagedEndpointRateLimit - outer / 2 < q7SalvagedEndpointRate n :=
    tendsto_q7SalvagedEndpointRate.eventually
      (Ioi_mem_nhds (by linarith :
        q7SalvagedEndpointRateLimit - outer / 2 <
          q7SalvagedEndpointRateLimit))
  obtain ⟨n, hn, hrate⟩ :=
    (eventually_q7SalvagedEndpointFeasible.and hclose).exists
  rcases hn with
    ⟨hlam0, hlam1, heps, hH, hscale, hm3, hm4, hm5, hm6, hm7, hq⟩
  obtain ⟨T₀, hT₀⟩ := zeta_q7Salvaged_strict_simple_fixed_lam
    hcertificates hlam0 hlam1 heps hH hscale hm3 hm4 hm5 hm6 hm7
      (by simpa [q7SalvagedEndpointQ] using hq)
      (outer / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have hfixed :
      (q7SalvagedEndpointRate n - outer / 2) *
          (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
    simpa [q7SalvagedEndpointRate, q7SalvagedEndpointQ] using hT₀ T hT
  have hcoef :
      ThmD.HD 1 + eta - outer ≤
        q7SalvagedEndpointRate n - outer / 2 := by
    unfold q7SalvagedEndpointRateLimit at hrate
    linarith
  exact le_trans
    (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) hfixed

/-- Public rational form, explicitly conditional on q3--q7 endpoint
certificates and on the named analytic input package. -/
theorem zeta_q7Salvaged_strict_simple_endpoint_rational
    (hcertificates : Q7SalvagedEndpointCertificates) :
    ∀ outer > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThmD.HD 1 + (1 : ℝ) / 175919 - outer) *
        (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  zeta_q7Salvaged_strict_simple_endpoint_of_le_gain
    hcertificates q7Salvaged_public_le_endpoint_gain

end StrictImprovement
end Zeta23

end
