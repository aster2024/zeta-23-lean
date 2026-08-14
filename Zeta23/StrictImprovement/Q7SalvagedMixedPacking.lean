/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7SalvagedResiduePacking
import Zeta23.StrictImprovement.WideRepairMixedPacking

/-!
# Abstract dependent-block pinching for the salvaged q7 superbin repair

The concrete selector is kept separate from the spectral argument.  Once a
finite dependent family of disjoint blocks realizes the exact pair-reward
sum, the pinching and rank--trace consequences below are generic.
-/

noncomputable section

open Matrix Finset Real
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

theorem q7Salvaged_selected_blocks_traceNorm_lower
    {S C d : Type*} [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C] [Fintype d] [DecidableEq d]
    (gamma : C → ℕ) (idx : ∀ c, Fin (gamma c) → S)
    (hinj : Function.Injective
      (fun ck : Σ c, Fin (gamma c) => idx ck.1 ck.2))
    (reward : C → ℝ) (x : S → d → ℂ) {scale : ℝ}
    (hlocal : ∀ c : C,
      2 * (scale * reward c) ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix (idx c))) :
    2 * (scale * ∑ c, reward c) ≤
      Tail.traceNorm (gramDeviation_isHermitian x) := by
  calc
    2 * (scale * ∑ c, reward c) =
        ∑ c, 2 * (scale * reward c) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ∑ c, Tail.traceNorm
        ((gramDeviation_isHermitian x).submatrix (idx c)) :=
      Finset.sum_le_sum fun c _ => hlocal c
    _ ≤ Tail.traceNorm (gramDeviation_isHermitian x) :=
      sum_traceNorm_dependent_principal_le idx hinj
        (gramDeviation_isHermitian x)

theorem q7Salvaged_selected_blocks_traceNorm_target_lower
    {S B C d : Type*} [Fintype S] [DecidableEq S]
    [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype d] [DecidableEq d]
    (left right : B → ℕ)
    (hcover : ∑ b, (left b + right b) = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 16 + 1)
    (gamma : C → ℕ) (idx : ∀ c, Fin (gamma c) → S)
    (hinj : Function.Injective
      (fun ck : Σ c, Fin (gamma c) => idx ck.1 ck.2))
    (reward : C → ℝ)
    (hrewardSum : ∑ c, reward c =
      ∑ b, q7SalvagedPairReward (left b) (right b))
    (x : S → d → ℂ) {scale : ℝ} (hscale : 0 ≤ scale)
    (hlocal : ∀ c : C,
      2 * (scale * reward c) ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix (idx c))) :
    2 * (scale * wideRepairAlpha * max 0
        ((Fintype.card S : ℝ) - q7SalvagedPackingLoss * D -
          q7SalvagedPackingIntercept)) ≤
      Tail.traceNorm (gramDeviation_isHermitian x) := by
  have hrewards := sum_q7SalvagedPairReward_target_lower
    left right hcover D hbins
  rw [← hrewardSum] at hrewards
  have hscaled := mul_le_mul_of_nonneg_left hrewards hscale
  have htrace := q7Salvaged_selected_blocks_traceNorm_lower
    gamma idx hinj reward x hlocal
  calc
    2 * (scale * wideRepairAlpha * max 0
        ((Fintype.card S : ℝ) - q7SalvagedPackingLoss * D -
          q7SalvagedPackingIntercept)) ≤
        2 * (scale * ∑ c, reward c) := by nlinarith
    _ ≤ Tail.traceNorm (gramDeviation_isHermitian x) := htrace

/-- Rank--trace consequence of any concrete q7 superbin selector. -/
theorem rank_trace_two_with_q7Salvaged_selected_blocks
    {S B C d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype d] [DecidableEq d]
    (left right : B → ℕ)
    (hcover : ∑ b, (left b + right b) = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 16 + 1)
    (gamma : C → ℕ) (idx : ∀ c, Fin (gamma c) → S)
    (hinj : Function.Injective
      (fun ck : Σ c, Fin (gamma c) => idx ck.1 ck.2))
    (reward : C → ℝ)
    (hrewardSum : ∑ c, reward c =
      ∑ b, q7SalvagedPairReward (left b) (right b))
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hlocal : ∀ c : C,
      2 * (scale * reward c) ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix (idx c)))
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (columnMatrix x * (columnMatrix x)ᴴ) -
        (Fintype.card S : ℝ) + 4 * rtrace Q - 4 * (b : ℝ) +
        scale ^ 2 * wideRepairAlpha ^ 2 / (Fintype.card S : ℝ) *
          max 0 ((Fintype.card S : ℝ) -
            q7SalvagedPackingLoss * D -
            q7SalvagedPackingIntercept) ^ 2 ≤
      frobSq (columnMatrix x * (columnMatrix x)ᴴ + Q) := by
  let target : ℝ := max 0 ((Fintype.card S : ℝ) -
    q7SalvagedPackingLoss * D - q7SalvagedPackingIntercept)
  let R : ℝ := scale * wideRepairAlpha * target
  have hR0 : 0 ≤ R := by
    dsimp [R, target]
    exact mul_nonneg (mul_nonneg hscale wideRepairAlpha_pos.le)
      (le_max_left 0 ((Fintype.card S : ℝ) -
        q7SalvagedPackingLoss * D - q7SalvagedPackingIntercept))
  have htrace : 2 * R ≤ Tail.traceNorm (gramDeviation_isHermitian x) := by
    dsimp [R, target]
    exact q7Salvaged_selected_blocks_traceNorm_target_lower
      left right hcover D hbins gamma idx hinj reward hrewardSum
        x hscale hlocal
  have hlower := reward_sq_le_card_mul_belowOneDefect_of_traceNorm
    x hunit hR0 htrace
  rw [← belowOneDefect_columnMatrix_gram x] at hlower
  have hspos : 0 < (Fintype.card S : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hdiv : R ^ 2 / (Fintype.card S : ℝ) ≤
      belowOneDefect
        (Matrix.posSemidef_conjTranspose_mul_self (columnMatrix x)).1 := by
    apply (div_le_iff₀ hspos).2
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hlower
  have hrefined := rank_trace_ineq_two_refined_gram (columnMatrix x) hQ hb
  have hRform : R ^ 2 / (Fintype.card S : ℝ) =
      scale ^ 2 * wideRepairAlpha ^ 2 / (Fintype.card S : ℝ) *
        target ^ 2 := by
    dsimp [R]
    field_simp [ne_of_gt hspos]
  rw [hRform] at hdiv
  dsimp [target] at hdiv
  linarith

/-- Weighted normalized wrapper consumed by the zero-side seam once the
concrete q7 selector supplies its local block inequalities. -/
theorem rank_trace_two_with_normalized_q7Salvaged_selected_blocks
    {S B C d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype d] [DecidableEq d]
    (left right : B → ℕ)
    (hcover : ∑ b, (left b + right b) = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 16 + 1)
    (gamma : C → ℕ) (idx : ∀ c, Fin (gamma c) → S)
    (hinj : Function.Injective
      (fun ck : Σ c, Fin (gamma c) => idx ck.1 ck.2))
    (reward : C → ℝ)
    (hrewardSum : ∑ c, reward c =
      ∑ b, q7SalvagedPairReward (left b) (right b))
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hlocal : ∀ c : C,
      2 * (scale * reward c) ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix (idx c)))
    (w : S → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    {A : Matrix d d ℂ} (hA : A.IsHermitian)
    {b : ℕ}
    (hb : posIndex
      (hA.sub (weightedProjectorSum_posSemidef x w hw0).isHermitian) ≤ b) :
    2 * rtrace (projectorSum x) - (Fintype.card S : ℝ) +
        4 * rtrace (A - projectorSum x) - 4 * (b : ℝ) +
        scale ^ 2 * wideRepairAlpha ^ 2 / (Fintype.card S : ℝ) *
          max 0 ((Fintype.card S : ℝ) -
            q7SalvagedPackingLoss * D -
            q7SalvagedPackingIntercept) ^ 2 ≤
      frobSq A := by
  have hb' : posIndex (hA.sub (projectorSum_posSemidef x).isHermitian) ≤ b :=
    (posIndex_unit_complement_le_weighted_complement x w hw0 hw1 hA).trans hb
  have hmain := rank_trace_two_with_q7Salvaged_selected_blocks
    left right hcover D hbins gamma idx hinj reward hrewardSum x hunit
      hscale hlocal (hA.sub (projectorSum_posSemidef x).isHermitian) hb'
  rw [← projectorSum_eq_columnMatrix_mul_conjTranspose x] at hmain
  have hsum : projectorSum x + (A - projectorSum x) = A := by abel
  rw [hsum] at hmain
  exact hmain

end StrictImprovement
end Zeta23

end
