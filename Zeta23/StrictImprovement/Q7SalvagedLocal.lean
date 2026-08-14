/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7SalvagedBlocks

/-!
# Local trace-norm inequality for every salvaged q7 inventory block

The three-, four-, and five-block cases require only a width-`16*pi`
diameter bound.  The six- and seven-block cases record the left/right half
geometry of a single width-`32*pi` superbin.
-/

noncomputable section

open Matrix Real
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

def Q7SalvagedBlockGeometry
    {S B : Type*} [Fintype B]
    {E : BinnedEnumeration S (B × Fin 2)}
    (q : Q7SalvagedBlock E)
    (coord : Fin (q7SalvagedBlockSize q) → ℝ) : Prop :=
  match q.1.2 with
  | .six =>
      (∀ i, i.val < 3 → 0 ≤ coord i ∧ coord i ≤ 16 * Real.pi) ∧
      (∀ i, 3 ≤ i.val → 16 * Real.pi ≤ coord i ∧
        coord i ≤ 32 * Real.pi)
  | .sevenThreeFour =>
      (∀ i, i.val < 3 → 0 ≤ coord i ∧ coord i ≤ 16 * Real.pi) ∧
      (∀ i, 3 ≤ i.val → 16 * Real.pi ≤ coord i ∧
        coord i ≤ 32 * Real.pi)
  | .sevenFourThree =>
      (∀ i, i.val < 4 → 0 ≤ coord i ∧ coord i ≤ 16 * Real.pi) ∧
      (∀ i, 4 ≤ i.val → 16 * Real.pi ≤ coord i ∧
        coord i ≤ 32 * Real.pi)
  | _ => ∀ i j, |coord i - coord j| ≤ 16 * Real.pi

theorem q7SalvagedBlock_nearby_traceNorm_lower
    {S K : Type*} [Fintype K]
    {E : BinnedEnumeration S (K × Fin 2)}
    (hcertificates : Q7SalvagedEndpointCertificates)
    (q : Q7SalvagedBlock E)
    (coord : Fin (q7SalvagedBlockSize q) → ℝ)
    (hgeometry : Q7SalvagedBlockGeometry q coord)
    {B : Matrix (Fin (q7SalvagedBlockSize q))
      (Fin (q7SalvagedBlockSize q)) ℂ}
    (hB : B.IsHermitian) (hdiagB : ∀ i, B i i = 0)
    {eps scale : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ i j, ‖B i j - wideEndpointDeviation coord i j‖ ≤ eps)
    (hmargin3 : scale * wideRepairRewardThree +
      (3 * Real.sqrt 3 / 2) * eps ≤ wideRepairRewardThree)
    (hmargin4 : scale * wideRepairRewardFour +
      2 * Real.sqrt 3 * eps ≤ wideRepairRewardFour)
    (hmargin5 : scale * wideRepairRewardFive +
      (5 * Real.sqrt 5 / 2) * eps ≤ wideRepairRewardFive)
    (hmargin6 : scale * q7SalvagedSixReward +
      3 * Real.sqrt 6 * eps ≤ q7SalvagedSixReward)
    (hmargin7 : scale * q7SalvagedSevenReward +
      (7 * Real.sqrt 7 / 2) * eps ≤ q7SalvagedSevenReward) :
    2 * (scale * q7SalvagedBlockReward q) ≤ Tail.traceNorm hB := by
  rcases q with ⟨k, u⟩
  rcases k with ⟨b, kind⟩
  cases kind with
  | fiveLeft =>
      exact wideRepairFive_nearby_traceNorm_lower hcertificates.base.five
        coord hgeometry hB heps hclose hmargin5
  | fiveRight =>
      exact wideRepairFive_nearby_traceNorm_lower hcertificates.base.five
        coord hgeometry hB heps hclose hmargin5
  | threeLeft =>
      have hdist : ∀ i j : Fin 3,
          |coord i - coord j| ≤ (352 : ℝ) / 7 := by
        intro i j
        have hp := Real.pi_lt_d4
        exact (hgeometry i j).trans (by nlinarith)
      exact wideRepairThree_nearby_traceNorm_lower
        hcertificates.base.three coord hdist hB heps hclose hmargin3
  | threeRight =>
      have hdist : ∀ i j : Fin 3,
          |coord i - coord j| ≤ (352 : ℝ) / 7 := by
        intro i j
        have hp := Real.pi_lt_d4
        exact (hgeometry i j).trans (by nlinarith)
      exact wideRepairThree_nearby_traceNorm_lower
        hcertificates.base.three coord hdist hB heps hclose hmargin3
  | fourLeft =>
      have hdist : ∀ i j : Fin 4,
          |coord i - coord j| ≤ (352 : ℝ) / 7 := by
        intro i j
        have hp := Real.pi_lt_d4
        exact (hgeometry i j).trans (by nlinarith)
      have hedge : ∀ {i j : Fin 4}, i ≠ j →
          ‖B i j - endpointFourDeviation coord i j‖ ≤ eps := by
        intro i j hij
        rw [endpointFourDeviation_offdiag coord hij]
        have h := hclose i j
        rw [wideEndpointDeviation_offdiag coord hij] at h
        exact h
      exact wideRepairFour_nearby_traceNorm_lower
        hcertificates.base.four coord hdist hB hdiagB heps hmargin4
          (hedge (by decide)) (hedge (by decide)) (hedge (by decide))
          (hedge (by decide)) (hedge (by decide)) (hedge (by decide))
  | fourRight =>
      have hdist : ∀ i j : Fin 4,
          |coord i - coord j| ≤ (352 : ℝ) / 7 := by
        intro i j
        have hp := Real.pi_lt_d4
        exact (hgeometry i j).trans (by nlinarith)
      have hedge : ∀ {i j : Fin 4}, i ≠ j →
          ‖B i j - endpointFourDeviation coord i j‖ ≤ eps := by
        intro i j hij
        rw [endpointFourDeviation_offdiag coord hij]
        have h := hclose i j
        rw [wideEndpointDeviation_offdiag coord hij] at h
        exact h
      exact wideRepairFour_nearby_traceNorm_lower
        hcertificates.base.four coord hdist hB hdiagB heps hmargin4
          (hedge (by decide)) (hedge (by decide)) (hedge (by decide))
          (hedge (by decide)) (hedge (by decide)) (hedge (by decide))
  | six =>
      exact q7Salvaged_six_nearby_traceNorm_lower hcertificates.six coord
        hgeometry.1 hgeometry.2 hB heps hclose hmargin6
  | sevenThreeFour =>
      exact q7Salvaged_seven_threeFour_nearby_traceNorm_lower
        hcertificates.seven coord hgeometry.1 hgeometry.2 hB heps hclose hmargin7
  | sevenFourThree =>
      exact q7Salvaged_seven_fourThree_nearby_traceNorm_lower
        hcertificates.seven coord hgeometry.1 hgeometry.2 hB heps hclose hmargin7

end StrictImprovement
end Zeta23

end
