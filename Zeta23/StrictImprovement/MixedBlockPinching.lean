/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.LocalPinching

/-!
# Trace-norm pinching for variable-size principal blocks

The fixed-size theorem in `LocalPinching` is enough for uniform triple or
four-block packing.  Mixed residue repair uses blocks of orders three, four,
and five simultaneously.  This module proves the corresponding dependent
version: the coordinate type of block `b` may be `gamma b`.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

variable {n beta : Type*} [Fintype n] [DecidableEq n]
variable [Fintype beta] [DecidableEq beta]
variable {gamma : beta -> Type*}
variable [forall b, Fintype (gamma b)] [forall b, DecidableEq (gamma b)]

/-- The trace norms of pairwise disjoint principal submatrices remain
additive at the lower-bound level when their orders depend on the block. -/
theorem sum_traceNorm_dependent_principal_le
    (idx : (b : beta) -> gamma b -> n)
    (hinj : Function.Injective
      (fun br : Sigma gamma => idx br.1 br.2))
    {A : Matrix n n Complex} (hA : A.IsHermitian) :
    ∑ b, Tail.traceNorm (hA.submatrix (idx b)) <= Tail.traceNorm hA := by
  let U : Matrix n n Complex := hA.eigenvectorUnitary
  have hdecomp : forall b,
      (∑ k, (((abs (hA.eigenvalues k) : Real) : Complex)) •
        vecMulVec (fun r => U (idx b r) k)
          (if 0 <= hA.eigenvalues k then
            (fun r => star (U (idx b r) k))
          else -(fun r => star (U (idx b r) k))))
        = A.submatrix (idx b) (idx b) := by
    intro b
    calc
      (∑ k, (((abs (hA.eigenvalues k) : Real) : Complex)) •
        vecMulVec (fun r => U (idx b r) k)
          (if 0 <= hA.eigenvalues k then
            (fun r => star (U (idx b r) k))
          else -(fun r => star (U (idx b r) k))))
          = ∑ k, (((hA.eigenvalues k : Real) : Complex)) •
              vecMulVec (fun r => U (idx b r) k)
                (fun r => star (U (idx b r) k)) := by
            apply Finset.sum_congr rfl
            intro k _
            exact abs_smul_signed_vecMulVec (n := gamma b)
              (hA.eigenvalues k)
              (fun r => U (idx b r) k)
              (fun r => star (U (idx b r) k))
      _ = (∑ k, (((hA.eigenvalues k : Real) : Complex)) •
              vecMulVec (fun i => U i k) (fun i => star (U i k))).submatrix
              (idx b) (idx b) := by
            ext r s
            simp [Matrix.submatrix, Matrix.sum_apply, Matrix.smul_apply,
              vecMulVec_apply]
      _ = A.submatrix (idx b) (idx b) := by
            rw [show U = (hA.eigenvectorUnitary : Matrix n n Complex) from rfl,
              sum_eigen_vecMulVec_eq hA]
  have hblock : forall b,
      Tail.traceNorm (hA.submatrix (idx b)) <=
        ∑ k, abs (hA.eigenvalues k) *
          ∑ r, norm (U (idx b r) k) ^ 2 := by
    intro b
    have hraw := traceNorm_le_sum_vecMulVec_two
      (hA.submatrix (idx b))
      (fun k => abs (hA.eigenvalues k)) (fun k => abs_nonneg _)
      (fun k r => U (idx b r) k)
      (fun k => if 0 <= hA.eigenvalues k then
        (fun r => star (U (idx b r) k))
      else -(fun r => star (U (idx b r) k)))
      (hdecomp b)
    refine hraw.trans_eq ?_
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : 0 <= hA.eigenvalues k
    · simp only [hk, if_true, Pi.neg_apply, norm_neg, norm_star]
      ring_nf
    · simp only [hk, if_false, Pi.neg_apply, norm_neg, norm_star]
      ring_nf
  have hinjective_energy : forall k,
      ∑ b, ∑ r, norm (U (idx b r) k) ^ 2 <=
        ∑ i, norm (U i k) ^ 2 := by
    intro k
    let e : n -> Real := fun i => norm (U i k) ^ 2
    change (∑ b, ∑ r, e (idx b r)) <= ∑ i, e i
    have hSigma : (∑ b, ∑ r, e (idx b r)) =
        ∑ br : Sigma gamma, e (idx br.1 br.2) := by
      exact (Fintype.sum_sigma'
        (fun b r => e (idx b r))).symm
    rw [hSigma]
    calc
      (∑ br : Sigma gamma, e (idx br.1 br.2)) =
          (Finset.univ.image
            (fun br : Sigma gamma => idx br.1 br.2)).sum e := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact hinj hab
      _ <= (Finset.univ : Finset n).sum e :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
      _ = ∑ i, e i := rfl
  have hcol : forall k, ∑ i, norm (U i k) ^ 2 = 1 := by
    have hDS := normSqMatrix_mem_doublyStochastic_of_unitary
      (hA.eigenvectorUnitary).2
    rw [mem_doublyStochastic_iff_sum] at hDS
    obtain ⟨_, _, hcols⟩ := hDS
    intro k
    simpa [U, normSqMatrix] using hcols k
  calc
    (∑ b, Tail.traceNorm (hA.submatrix (idx b)))
        <= ∑ b, ∑ k, abs (hA.eigenvalues k) *
            ∑ r, norm (U (idx b r) k) ^ 2 :=
      Finset.sum_le_sum fun b _ => hblock b
    _ = ∑ k, abs (hA.eigenvalues k) *
          (∑ b, ∑ r, norm (U (idx b r) k) ^ 2) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
    _ <= ∑ k, abs (hA.eigenvalues k) * 1 := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left
          ((hinjective_energy k).trans_eq (hcol k)) (abs_nonneg _)
    _ = Tail.traceNorm hA := by simp [Tail.traceNorm]

end StrictImprovement
end Zeta23

end
