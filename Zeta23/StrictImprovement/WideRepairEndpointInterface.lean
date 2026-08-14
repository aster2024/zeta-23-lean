/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.SpectralFourPointInterface
import Zeta23.StrictImprovement.ThreeCoordinateEnergy
import Zeta23.StrictImprovement.TraceZero

/-!
# Explicit endpoint interfaces for the width-sixteen residue repair

The interval computations stay visible as three proposition-valued inputs.
Everything after those inputs--spectral conversion, perturbation stability,
and rational reward weakening--is kernel checked here.
-/

noncomputable section

open Matrix Finset Real
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

/-- Hollow endpoint matrix in arbitrary finite order. -/
def wideEndpointDeviation {n : Type*} [DecidableEq n]
    (x : n → ℝ) : Matrix n n ℂ :=
  fun i j => if i = j then 0 else (endpointR (x i - x j) : ℂ)

lemma wideEndpointDeviation_diag {n : Type*} [DecidableEq n]
    (x : n → ℝ) (i : n) : wideEndpointDeviation x i i = 0 := by
  simp [wideEndpointDeviation]

lemma wideEndpointDeviation_offdiag {n : Type*} [DecidableEq n]
    (x : n → ℝ) {i j : n} (hij : i ≠ j) :
    wideEndpointDeviation x i j = (endpointR (x i - x j) : ℂ) := by
  simp [wideEndpointDeviation, hij]

lemma wideEndpointDeviation_isHermitian {n : Type*} [DecidableEq n]
    (x : n → ℝ) : (wideEndpointDeviation x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [wideEndpointDeviation]
  · have hji : j ≠ i := Ne.symm hij
    rw [wideEndpointDeviation_offdiag x hji,
      wideEndpointDeviation_offdiag x hij]
    simp only [Complex.star_def, Complex.conj_ofReal]
    congr 1
    rw [show x j - x i = -(x i - x j) by ring, endpointR_neg]

/-- External three-point energy tree on the rational simplex containing the
physical diameter-sixteen domain. -/
def WideRepairThreeEndpointCertificate : Prop :=
  ∀ x : Fin 3 → ℝ,
    (∀ i j : Fin 3, |x i - x j| ≤ (352 : ℝ) / 7) →
      (1 : ℝ) / 160000 < threeCoordinateEnergy endpointR (x 0) (x 1) (x 2)

/-- External four-point spectral tree on the same rational simplex. -/
def WideRepairFourEndpointCertificate : Prop :=
  ∀ x : Fin 4 → ℝ,
    (∀ i j : Fin 4, |x i - x j| ≤ (352 : ℝ) / 7) →
      (1 : ℝ) / 7225 <
        (Tail.traceNorm (endpointFourDeviation_isHermitian x) / 2) ^ 2

/-- External five-point spectral certificate on physical diameter at most
`16*pi`. -/
def WideRepairFiveEndpointCertificate : Prop :=
  ∀ x : Fin 5 → ℝ,
    (∀ i j : Fin 5, |x i - x j| ≤ 16 * Real.pi) →
      (1 : ℝ) / 1000 <
        (Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2) ^ 2

/-- All non-kernel endpoint evidence required by the repaired packing. -/
structure WideRepairEndpointCertificates : Prop where
  three : WideRepairThreeEndpointCertificate
  four : WideRepairFourEndpointCertificate
  five : WideRepairFiveEndpointCertificate

def wideRepairRewardThree : ℝ := 1 / 400
def wideRepairRewardFour : ℝ := 1 / 85
def wideRepairRewardFive : ℝ := 316227 / 10000000

/-- Reward per atom of the dominant five-point block. -/
def wideRepairAlpha : ℝ := wideRepairRewardFive / 5

/-- Worst one-bin residue deficit; residue three is proved maximal in
`WideRepairMixedPacking`. -/
def wideRepairDeficit : ℝ := 3 * wideRepairAlpha - wideRepairRewardThree

/-- Coefficient of the diameter term after `card(B) <= D/8+1`. -/
def wideRepairPackingLoss : ℝ := wideRepairDeficit / (8 * wideRepairAlpha)

/-- Constant boundary loss after summing over bins. -/
def wideRepairPackingIntercept : ℝ := wideRepairDeficit / wideRepairAlpha

lemma wideRepairRewardThree_nonneg : 0 ≤ wideRepairRewardThree := by
  norm_num [wideRepairRewardThree]

lemma wideRepairRewardFour_nonneg : 0 ≤ wideRepairRewardFour := by
  norm_num [wideRepairRewardFour]

lemma wideRepairRewardFive_nonneg : 0 ≤ wideRepairRewardFive := by
  norm_num [wideRepairRewardFive]

lemma wideRepairAlpha_pos : 0 < wideRepairAlpha := by
  norm_num [wideRepairAlpha, wideRepairRewardFive]

lemma wideRepairDeficit_nonneg : 0 ≤ wideRepairDeficit := by
  norm_num [wideRepairDeficit, wideRepairAlpha, wideRepairRewardFive,
    wideRepairRewardThree]

lemma wideRepairPackingLoss_nonneg : 0 ≤ wideRepairPackingLoss := by
  exact div_nonneg wideRepairDeficit_nonneg (mul_nonneg (by norm_num)
    wideRepairAlpha_pos.le)

lemma wideRepairPackingIntercept_nonneg : 0 ≤ wideRepairPackingIntercept := by
  exact div_nonneg wideRepairDeficit_nonneg wideRepairAlpha_pos.le

private lemma frobSq_eq_sum_norm_sq_wide
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold frobSq
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum, RCLike.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Dimension-cardinality Cauchy--Schwarz bound for the Hermitian trace norm. -/
theorem traceNorm_sq_le_card_mul_frobSq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Tail.traceNorm hA) ^ 2 ≤ (Fintype.card n : ℝ) * frobSq A := by
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues hA, Tail.traceNorm]
  have h := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i => |hA.eigenvalues i|)
  simpa [sq_abs] using h

/-- Entrywise perturbations give a deliberately simple all-entry Frobenius
bound.  Diagonal zeroes may be included among the bounded entries. -/
theorem frobSq_le_card_sq_mul_eps_sq_of_entrywise
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} {eps : ℝ} (heps : 0 ≤ eps)
    (hentry : ∀ i j, ‖A i j‖ ≤ eps) :
    frobSq A ≤ (Fintype.card n : ℝ) ^ 2 * eps ^ 2 := by
  rw [frobSq_eq_sum_norm_sq_wide]
  calc
    (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ ∑ i, ∑ _j : n, eps ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [norm_nonneg (A i j), hentry i j]
    _ = (Fintype.card n : ℝ) ^ 2 * eps ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      push_cast
      ring

/-- Generic half-trace-norm stability.  The coefficient is
`card(n)*sqrt(card(n))/2`; this intentionally favors a uniform proof over the
sharper hand-enumerated four-dimensional constant. -/
theorem half_traceNorm_sub_le_card_sqrt_card_eps
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hentry : ∀ i j, ‖A i j - B i j‖ ≤ eps) :
    |Tail.traceNorm hA / 2 - Tail.traceNorm hB / 2| ≤
      ((Fintype.card n : ℝ) * Real.sqrt (Fintype.card n : ℝ) / 2) * eps := by
  let C : Matrix n n ℂ := A - B
  have hC : C.IsHermitian := hA.sub hB
  have hentryC : ∀ i j, ‖C i j‖ ≤ eps := by
    intro i j
    simpa [C, Matrix.sub_apply] using hentry i j
  have hfrob := frobSq_le_card_sq_mul_eps_sq_of_entrywise heps hentryC
  have htraceSq := traceNorm_sq_le_card_mul_frobSq hC
  have hcard0 : 0 ≤ (Fintype.card n : ℝ) := by positivity
  have hcardPos : 0 < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsqrt0 : 0 ≤ Real.sqrt (Fintype.card n : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (Fintype.card n : ℝ)) ^ 2 =
      (Fintype.card n : ℝ) := Real.sq_sqrt hcard0
  have htrace0 := Tail.traceNorm_nonneg hC
  have htraceBound : Tail.traceNorm hC ≤
      (Fintype.card n : ℝ) * Real.sqrt (Fintype.card n : ℝ) * eps := by
    have hrhs0 : 0 ≤ (Fintype.card n : ℝ) *
        Real.sqrt (Fintype.card n : ℝ) * eps := by positivity
    have htargetSq :
        ((Fintype.card n : ℝ) * Real.sqrt (Fintype.card n : ℝ) * eps) ^ 2 =
          (Fintype.card n : ℝ) *
            ((Fintype.card n : ℝ) ^ 2 * eps ^ 2) := by
      calc
        ((Fintype.card n : ℝ) * Real.sqrt (Fintype.card n : ℝ) * eps) ^ 2 =
            (Fintype.card n : ℝ) ^ 2 *
              (Real.sqrt (Fintype.card n : ℝ)) ^ 2 * eps ^ 2 := by ring
        _ = (Fintype.card n : ℝ) *
            ((Fintype.card n : ℝ) ^ 2 * eps ^ 2) := by
          rw [hsqrtSq]
          ring
    have hsq : (Tail.traceNorm hC) ^ 2 ≤
        (Fintype.card n : ℝ) *
          ((Fintype.card n : ℝ) ^ 2 * eps ^ 2) :=
      htraceSq.trans (mul_le_mul_of_nonneg_left hfrob hcard0)
    rw [← htargetSq] at hsq
    nlinarith
  have hreverse := Tail.abs_traceNorm_sub_traceNorm_le hA hB
  rw [← sub_div, abs_div]
  norm_num
  calc
    |Tail.traceNorm hA - Tail.traceNorm hB| / 2
        ≤ Tail.traceNorm hC / 2 :=
      div_le_div_of_nonneg_right hreverse (by norm_num)
    _ ≤ ((Fintype.card n : ℝ) * Real.sqrt (Fintype.card n : ℝ) * eps) / 2 :=
      div_le_div_of_nonneg_right htraceBound (by norm_num)
    _ = ((Fintype.card n : ℝ) * Real.sqrt (Fintype.card n : ℝ) / 2) * eps := by
      ring

lemma frobSq_wideEndpointDeviation_fin3 (x : Fin 3 → ℝ) :
    frobSq (wideEndpointDeviation x) =
      2 * threeCoordinateEnergy endpointR (x 0) (x 1) (x 2) := by
  rw [frobSq_fin3_of_diag_zero (wideEndpointDeviation_isHermitian x)
    (wideEndpointDeviation_diag x)]
  rw [wideEndpointDeviation_offdiag x (by decide : (0 : Fin 3) ≠ 1),
    wideEndpointDeviation_offdiag x (by decide : (0 : Fin 3) ≠ 2),
    wideEndpointDeviation_offdiag x (by decide : (1 : Fin 3) ≠ 2)]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

theorem wideRepairThree_endpoint_traceNorm_lower
    (hcertificate : WideRepairThreeEndpointCertificate)
    (x : Fin 3 → ℝ)
    (hdist : ∀ i j : Fin 3, |x i - x j| ≤ (352 : ℝ) / 7) :
    2 * wideRepairRewardThree ≤
      Tail.traceNorm (wideEndpointDeviation_isHermitian x) := by
  have hcert := (hcertificate x hdist).le
  have htrace := two_mul_sqrt_le_traceNorm_fin3
    (show 0 ≤ (1 : ℝ) / 160000 by norm_num)
    (wideEndpointDeviation_isHermitian x)
    (by
      unfold rtrace Matrix.trace
      simp [wideEndpointDeviation_diag])
    (by
      rw [frobSq_wideEndpointDeviation_fin3]
      nlinarith)
  have hsqrt0 : 0 ≤ Real.sqrt ((1 : ℝ) / 160000) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt ((1 : ℝ) / 160000)) ^ 2 =
      (1 : ℝ) / 160000 := Real.sq_sqrt (by norm_num)
  have hreward0 := wideRepairRewardThree_nonneg
  have hrewardSq : wideRepairRewardThree ^ 2 = (1 : ℝ) / 160000 := by
    norm_num [wideRepairRewardThree]
  have heq : Real.sqrt ((1 : ℝ) / 160000) = wideRepairRewardThree := by
    nlinarith
  rwa [heq] at htrace

theorem wideRepairFour_endpoint_traceNorm_lower
    (hcertificate : WideRepairFourEndpointCertificate)
    (x : Fin 4 → ℝ)
    (hdist : ∀ i j : Fin 4, |x i - x j| ≤ (352 : ℝ) / 7) :
    2 * wideRepairRewardFour ≤
      Tail.traceNorm (endpointFourDeviation_isHermitian x) := by
  have hcert := hcertificate x hdist
  have htrace0 : 0 ≤ Tail.traceNorm (endpointFourDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  norm_num [wideRepairRewardFour] at ⊢
  nlinarith

theorem wideRepairFive_endpoint_traceNorm_lower
    (hcertificate : WideRepairFiveEndpointCertificate)
    (x : Fin 5 → ℝ)
    (hdist : ∀ i j : Fin 5, |x i - x j| ≤ 16 * Real.pi) :
    2 * wideRepairRewardFive ≤
      Tail.traceNorm (wideEndpointDeviation_isHermitian x) := by
  have hcert := hcertificate x hdist
  have htrace0 : 0 ≤ Tail.traceNorm (wideEndpointDeviation_isHermitian x) / 2 :=
    div_nonneg (Tail.traceNorm_nonneg _) (by norm_num)
  norm_num [wideRepairRewardFive] at ⊢
  nlinarith

/-- A nearby three-block retains its conservative reward after the generic
three-dimensional trace-norm loss. -/
theorem wideRepairThree_nearby_traceNorm_lower
    (hcertificate : WideRepairThreeEndpointCertificate)
    (x : Fin 3 → ℝ)
    (hdist : ∀ i j : Fin 3, |x i - x j| ≤ (352 : ℝ) / 7)
    {B : Matrix (Fin 3) (Fin 3) ℂ} (hB : B.IsHermitian)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ i j, ‖B i j - wideEndpointDeviation x i j‖ ≤ eps)
    (hmargin : scale * wideRepairRewardThree +
      (3 * Real.sqrt 3 / 2) * eps ≤ wideRepairRewardThree) :
    2 * (scale * wideRepairRewardThree) ≤ Tail.traceNorm hB := by
  have hstable := half_traceNorm_sub_le_card_sqrt_card_eps hB
    (wideEndpointDeviation_isHermitian x) heps hclose
  have hend := wideRepairThree_endpoint_traceNorm_lower hcertificate x hdist
  norm_num at hstable
  have hlower := (abs_le.mp hstable).1
  linarith

/-- The four-block uses the sharper six-edge stability constant already
proved for `Fin 4`. -/
theorem wideRepairFour_nearby_traceNorm_lower
    (hcertificate : WideRepairFourEndpointCertificate)
    (x : Fin 4 → ℝ)
    (hdist : ∀ i j : Fin 4, |x i - x j| ≤ (352 : ℝ) / 7)
    {B : Matrix (Fin 4) (Fin 4) ℂ} (hB : B.IsHermitian)
    (hdiagB : ∀ i, B i i = 0)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hmargin : scale * wideRepairRewardFour +
      2 * Real.sqrt 3 * eps ≤ wideRepairRewardFour)
    (h01 : ‖B 0 1 - endpointFourDeviation x 0 1‖ ≤ eps)
    (h02 : ‖B 0 2 - endpointFourDeviation x 0 2‖ ≤ eps)
    (h03 : ‖B 0 3 - endpointFourDeviation x 0 3‖ ≤ eps)
    (h12 : ‖B 1 2 - endpointFourDeviation x 1 2‖ ≤ eps)
    (h13 : ‖B 1 3 - endpointFourDeviation x 1 3‖ ≤ eps)
    (h23 : ‖B 2 3 - endpointFourDeviation x 2 3‖ ≤ eps) :
    2 * (scale * wideRepairRewardFour) ≤ Tail.traceNorm hB := by
  have hstable := half_traceNorm_sub_le_two_sqrt_three_eps_fin4
    hB (endpointFourDeviation_isHermitian x) hdiagB
    (endpointFourDeviation_diag x) heps h01 h02 h03 h12 h13 h23
  have hend := wideRepairFour_endpoint_traceNorm_lower hcertificate x hdist
  have hlower := (abs_le.mp hstable).1
  linarith

theorem wideRepairFive_nearby_traceNorm_lower
    (hcertificate : WideRepairFiveEndpointCertificate)
    (x : Fin 5 → ℝ)
    (hdist : ∀ i j : Fin 5, |x i - x j| ≤ 16 * Real.pi)
    {B : Matrix (Fin 5) (Fin 5) ℂ} (hB : B.IsHermitian)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ i j, ‖B i j - wideEndpointDeviation x i j‖ ≤ eps)
    (hmargin : scale * wideRepairRewardFive +
      (5 * Real.sqrt 5 / 2) * eps ≤ wideRepairRewardFive) :
    2 * (scale * wideRepairRewardFive) ≤ Tail.traceNorm hB := by
  have hstable := half_traceNorm_sub_le_card_sqrt_card_eps hB
    (wideEndpointDeviation_isHermitian x) heps hclose
  have hend := wideRepairFive_endpoint_traceNorm_lower hcertificate x hdist
  norm_num at hstable
  have hlower := (abs_le.mp hstable).1
  linarith

end StrictImprovement
end Zeta23

end
