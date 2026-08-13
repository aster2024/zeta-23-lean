/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.SpectralFourPointInterface

/-!
# Explicit endpoint interface on the full `264/7` certificate domain

The interval proof remains an external proposition.  This file only widens the
coordinate-free diameter recorded by Lean from `12*pi` to the rational domain
actually covered by the retained certificate.
-/

noncomputable section

open Matrix Finset Real
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

/-- Explicit trusted boundary supplied by the retained interval tree on its
full rational simplex.  No theorem in this repository constructs a proof of
this proposition. -/
def SpectralFourEndpointSlackCertificate : Prop :=
  ∀ x : Fin 4 → ℝ,
    (∀ i j : Fin 4, |x i - x j| ≤ (264 : ℝ) / 7) →
      spectralFourMassLower <
        (Tail.traceNorm (endpointFourDeviation_isHermitian x) / 2) ^ 2

lemma spectralFourMassLower_sqrt_lt_of_slack_certificate
    (hcertificate : SpectralFourEndpointSlackCertificate)
    (x : Fin 4 → ℝ)
    (hdist : ∀ i j : Fin 4, |x i - x j| ≤ (264 : ℝ) / 7) :
    Real.sqrt spectralFourMassLower <
      Tail.traceNorm (endpointFourDeviation_isHermitian x) / 2 := by
  have hcert := hcertificate x hdist
  have hsqrt0 := Real.sqrt_nonneg spectralFourMassLower
  have hsqrtSq := Real.sq_sqrt spectralFourMassLower_nonneg
  have htrace0 :
      0 ≤ Tail.traceNorm (endpointFourDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  nlinarith

/-- The same sharp finite/full stability transfer, now consuming the full
`264/7` endpoint certificate. -/
theorem spectral_slack_endpoint_to_nearby_traceNorm_lower
    (hcertificate : SpectralFourEndpointSlackCertificate)
    (x : Fin 4 → ℝ)
    (hdist : ∀ i j : Fin 4, |x i - x j| ≤ (264 : ℝ) / 7)
    {B : Matrix (Fin 4) (Fin 4) ℂ} (hB : B.IsHermitian)
    (hdiagB : ∀ i, B i i = 0)
    {eps m : ℝ} (heps : 0 ≤ eps) (hm : 0 ≤ m)
    (hmargin : Real.sqrt m + 2 * Real.sqrt 3 * eps ≤
      Real.sqrt spectralFourMassLower)
    (h01 : ‖B 0 1 - endpointFourDeviation x 0 1‖ ≤ eps)
    (h02 : ‖B 0 2 - endpointFourDeviation x 0 2‖ ≤ eps)
    (h03 : ‖B 0 3 - endpointFourDeviation x 0 3‖ ≤ eps)
    (h12 : ‖B 1 2 - endpointFourDeviation x 1 2‖ ≤ eps)
    (h13 : ‖B 1 3 - endpointFourDeviation x 1 3‖ ≤ eps)
    (h23 : ‖B 2 3 - endpointFourDeviation x 2 3‖ ≤ eps) :
    2 * Real.sqrt m ≤ Tail.traceNorm hB := by
  let hA := endpointFourDeviation_isHermitian x
  have hstable := half_traceNorm_sub_le_two_sqrt_three_eps_fin4
    hB hA hdiagB (endpointFourDeviation_diag x) heps
    h01 h02 h03 h12 h13 h23
  have hend := spectralFourMassLower_sqrt_lt_of_slack_certificate
    hcertificate x hdist
  have hlower :
      Tail.traceNorm hA / 2 - 2 * Real.sqrt 3 * eps ≤
        Tail.traceNorm hB / 2 := by
    have hneg := neg_abs_le
      (Tail.traceNorm hB / 2 - Tail.traceNorm hA / 2)
    linarith
  have hsqrt : Real.sqrt m ≤ Tail.traceNorm hB / 2 := by
    linarith
  nlinarith

end StrictImprovement
end Zeta23

end
