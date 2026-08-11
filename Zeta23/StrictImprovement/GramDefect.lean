/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.RefinedDefect
import Zeta23.ZeroSide.RankTraceMult

/-!
# Transfer of the below-one defect to the Gram matrix

The ambient matrix `W * Wᴴ` and the Gram matrix `Wᴴ * W` have the same
nonzero spectrum.  The centered function `unitDefect x - 1` vanishes at
zero, so its spectral sum transfers exactly.  This is the clean way to
remove the forced ambient zero eigenvalues from the refined rank--trace
inequality.

This is a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

variable {K : Type*} [RCLike K]

/-- Subtracting the ambient dimension from `belowOneDefect` is exactly the
spectral sum of the centered defect over the unsorted eigenvalue list. -/
lemma belowOneDefect_sub_card_eq_sum_centered
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n K} (hA : A.IsHermitian) :
    belowOneDefect hA - (Fintype.card n : ℝ)
      = ∑ i, centeredUnitDefect (hA.eigenvalues i) := by
  unfold belowOneDefect
  rw [← sum_eigenvalues_reindex hA unitDefect]
  simp only [centeredUnitDefect, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Exact padding identity for the below-one spectral defect of `W * Wᴴ`
and `Wᴴ * W`. -/
theorem belowOneDefect_gram_balance
    {n ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι] (W : Matrix n ι K) :
    belowOneDefect (Matrix.posSemidef_self_mul_conjTranspose W).1
          - (Fintype.card n : ℝ)
      = belowOneDefect (Matrix.posSemidef_conjTranspose_mul_self W).1
          - (Fintype.card ι : ℝ) := by
  rw [belowOneDefect_sub_card_eq_sum_centered,
    belowOneDefect_sub_card_eq_sum_centered]
  exact Zeta23.ZeroSide.RankTraceMult.sum_eigenvalues_comm
    W centeredUnitDefect centeredUnitDefect_zero

/-- Gram-dimension form of the refined `c = 2` rank--trace inequality.

Compared with the ambient theorem, the dimension term and the below-one
defect have both moved to the generally smaller Gram matrix `Wᴴ * W`.
No rank estimate or manual zero padding is needed. -/
theorem rank_trace_ineq_two_refined_gram
    {n ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι]
    (W : Matrix n ι K) {Q : Matrix n n K}
    (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (W * Wᴴ) - (Fintype.card ι : ℝ)
        + 4 * rtrace Q - 4 * (b : ℝ)
        + belowOneDefect (Matrix.posSemidef_conjTranspose_mul_self W).1
      ≤ frobSq (W * Wᴴ + Q) := by
  have hambient := rank_trace_ineq_two_refined_dimension
    (Matrix.posSemidef_self_mul_conjTranspose W) hQ hb
  have hbalance := belowOneDefect_gram_balance W
  linarith

end StrictImprovement
end Zeta23
