/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.SpectralFourStability
import Zeta23.StrictImprovement.ZetaEndpointConstant

/-!
# Explicit interface for the four-point spectral endpoint certificate

The interval computation remains an explicit proposition.  This module only
kernel-checks the coordinate-free matrix formulation and the perturbation
transfer from the endpoint matrix to a nearby finite Gram block.
-/

noncomputable section

open Matrix Finset Real
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

/-- Conservative square of the endpoint half-trace-norm lower bound. -/
def spectralFourMassLower : ℝ := 1 / 1700

/-- Public rational increment selected below the exact endpoint product. -/
def spectralFourEtaLower : ℝ := 1 / 914088

/-- The trace-zero Hermitian endpoint matrix associated with four real
coordinates. -/
def endpointFourDeviation (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => if i = j then 0 else (endpointR (x i - x j) : ℂ)

lemma endpointFourDeviation_diag (x : Fin 4 → ℝ) (i : Fin 4) :
    endpointFourDeviation x i i = 0 := by
  simp [endpointFourDeviation]

lemma endpointFourDeviation_offdiag
    (x : Fin 4 → ℝ) {i j : Fin 4} (hij : i ≠ j) :
    endpointFourDeviation x i j = (endpointR (x i - x j) : ℂ) := by
  simp [endpointFourDeviation, hij]

lemma endpointFourDeviation_isHermitian (x : Fin 4 → ℝ) :
    (endpointFourDeviation x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [endpointFourDeviation]
  · have hji : j ≠ i := Ne.symm hij
    rw [endpointFourDeviation_offdiag x hji,
      endpointFourDeviation_offdiag x hij]
    simp only [Complex.star_def, Complex.conj_ofReal]
    congr 1
    rw [show x j - x i = -(x i - x j) by ring, endpointR_neg]

/-- The explicit trusted boundary supplied by the external interval tree.
No theorem in this repository constructs a proof of this proposition. -/
def SpectralFourEndpointCertificate : Prop :=
  ∀ x : Fin 4 → ℝ,
    (∀ i j : Fin 4, |x i - x j| ≤ 12 * Real.pi) →
      spectralFourMassLower <
        (Tail.traceNorm (endpointFourDeviation_isHermitian x) / 2) ^ 2

lemma spectralFourMassLower_nonneg : 0 ≤ spectralFourMassLower := by
  norm_num [spectralFourMassLower]

lemma spectralFourMassLower_sqrt_lt
    (hcertificate : SpectralFourEndpointCertificate)
    (x : Fin 4 → ℝ)
    (hdist : ∀ i j : Fin 4, |x i - x j| ≤ 12 * Real.pi) :
    Real.sqrt spectralFourMassLower <
      Tail.traceNorm (endpointFourDeviation_isHermitian x) / 2 := by
  have hcert := hcertificate x hdist
  have hsqrt0 := Real.sqrt_nonneg spectralFourMassLower
  have hsqrtSq := Real.sq_sqrt spectralFourMassLower_nonneg
  have htrace0 : 0 ≤ Tail.traceNorm (endpointFourDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  nlinarith

/-- Coordinate-free perturbation transfer.  The endpoint certificate is
kept explicit, and a nearby Hermitian zero-diagonal matrix inherits any local
mass whose square-root margin absorbs the sharp `2*sqrt 3*eps` loss. -/
theorem spectral_endpoint_to_nearby_traceNorm_lower
    (hcertificate : SpectralFourEndpointCertificate)
    (x : Fin 4 → ℝ)
    (hdist : ∀ i j : Fin 4, |x i - x j| ≤ 12 * Real.pi)
    {B : Matrix (Fin 4) (Fin 4) ℂ} (hB : B.IsHermitian)
    (hdiagB : ∀ i, B i i = 0)
    {eps m : ℝ} (heps : 0 ≤ eps)
    -- `hm` records that `m` is a genuine mass parameter.  The inequality below
    -- happens to remain true without it because `Real.sqrt` truncates at zero.
    (hm : 0 ≤ m)
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
  have hend := spectralFourMassLower_sqrt_lt hcertificate x hdist
  have hlower :
      Tail.traceNorm hA / 2 - 2 * Real.sqrt 3 * eps ≤
        Tail.traceNorm hB / 2 := by
    have hneg := neg_abs_le
      (Tail.traceNorm hB / 2 - Tail.traceNorm hA / 2)
    linarith
  have hsqrt : Real.sqrt m ≤ Tail.traceNorm hB / 2 := by
    linarith
  nlinarith

/-- Frozen exact arithmetic for the public rational weakening. -/
theorem spectralFourEtaLower_le_endpoint_gain :
    spectralFourEtaLower ≤
      spectralFourMassLower / 16 * (ThmD.HD 1 - 1 / 2) ^ 2 := by
  have hgap0 : 0 ≤ (102239 : ℝ) / 592688 := by norm_num
  have hsq := pow_le_pow_left₀ hgap0 refined_endpoint_gap 2
  have hcoef : 0 ≤ spectralFourMassLower / 16 := by
    norm_num [spectralFourMassLower]
  calc
    spectralFourEtaLower
        ≤ spectralFourMassLower / 16 * ((102239 : ℝ) / 592688) ^ 2 := by
          norm_num [spectralFourEtaLower, spectralFourMassLower]
    _ ≤ spectralFourMassLower / 16 * (ThmD.HD 1 - 1 / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef

end StrictImprovement
end Zeta23

end
