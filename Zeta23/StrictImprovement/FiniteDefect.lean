/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.GramDefectLower

/-!
# Finite refined rank--trace theorem with local Gram triples

This module identifies the abstract unit-vector Gram matrix with `Wᴴ * W`
and inserts the disjoint-triple defect lower bound into the refined
rank--trace inequality.

This is a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

variable {d s β : Type*} [Fintype d] [DecidableEq d]
variable [Fintype s] [DecidableEq s]
variable [Fintype β] [DecidableEq β]

/-- Matrix whose columns are the vectors `x j`. -/
def columnMatrix (x : s → d → ℂ) : Matrix d s ℂ :=
  fun i j => x j i

lemma columnMatrix_gram (x : s → d → ℂ) :
    (columnMatrix x)ᴴ * columnMatrix x = gramMatrix x := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, columnMatrix,
    gramMatrix, dotProduct, Pi.star_apply]

lemma belowOneDefect_columnMatrix_gram
    (x : s → d → ℂ) :
    belowOneDefect (Matrix.posSemidef_conjTranspose_mul_self (columnMatrix x)).1
      = belowOneDefect (gramMatrix_isHermitian x) := by
  have h := columnMatrix_gram x
  cases h
  rfl

/-- Finite-dimensional refined rank--trace bound with the explicit local
triple gain. -/
theorem rank_trace_two_with_local_gram_triples
    [Nonempty s]
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    (idx : β → Fin 3 → s)
    (hinj : Function.Injective (fun br : β × Fin 3 => idx br.1 br.2))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ b, delta ≤ tripleCorrelationEnergy x idx b)
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (columnMatrix x * (columnMatrix x)ᴴ)
        - (Fintype.card s : ℝ)
        + 4 * rtrace Q - 4 * (b : ℝ)
        + (Fintype.card β : ℝ) ^ 2 * delta / (Fintype.card s : ℝ)
      ≤ frobSq (columnMatrix x * (columnMatrix x)ᴴ + Q) := by
  have hlower := card_sq_mul_delta_le_card_mul_belowOneDefect
    x hunit idx hinj hdelta hlocal
  rw [← belowOneDefect_columnMatrix_gram x] at hlower
  have hspos : 0 < (Fintype.card s : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hdiv :
      (Fintype.card β : ℝ) ^ 2 * delta / (Fintype.card s : ℝ)
        ≤ belowOneDefect
          (Matrix.posSemidef_conjTranspose_mul_self (columnMatrix x)).1 := by
    apply (div_le_iff₀ hspos).2
    simpa only [mul_comm] using hlower
  have hrefined := rank_trace_ineq_two_refined_gram
    (columnMatrix x) hQ hb
  linarith

end StrictImprovement
end Zeta23
