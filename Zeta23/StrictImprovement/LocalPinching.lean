/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.TraceNormRankOne
import Zeta23.StrictImprovement.TraceZero

/-!
# Trace-norm contractivity for a disjoint family of principal blocks

An assignment `owner : n → Option β` encodes disjoint coordinate blocks:
`some b` selects block `b`, while `none` discards the coordinate.  This file
proves that the corresponding (possibly incomplete) block pinching is
trace-norm contractive on complex Hermitian matrices.  The proof expands the
matrix in its Hermitian eigenbasis and applies the two-vector rank-one
majorant from `TraceNormRankOne`.

The combinatorial construction of the zeta triples and the final defect
arithmetic are downstream.  This is a source draft until checked by the
pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

variable {n β : Type*} [Fintype n] [DecidableEq n]
variable [Fintype β] [DecidableEq β]

/-- Restrict a vector to the coordinates owned by one block. -/
def cutVector (owner : n → Option β) (b : β) (u : n → ℂ) : n → ℂ :=
  fun i => if owner i = some b then u i else 0

/-- Keep the principal blocks selected by `owner`, and set every other entry
to zero.  Because a coordinate has only one `Option` value, the blocks are
disjoint by construction. -/
def blockPinch (owner : n → Option β) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => ∑ b, if owner i = some b ∧ owner j = some b then A i j else 0

lemma sum_cutVector_normSq_le (owner : n → Option β) (u : n → ℂ) :
    ∑ b, ∑ i, ‖cutVector owner b u i‖ ^ 2 ≤ ∑ i, ‖u i‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  cases hi : owner i with
  | none => simp [cutVector, hi]
  | some b =>
      rw [Finset.sum_eq_single b]
      · simp [cutVector, hi]
      · intro b' _ hb'
        simp [cutVector, hi, Ne.symm hb']
      · simp

lemma blockPinch_vecMulVec (owner : n → Option β) (u v : n → ℂ) :
    blockPinch owner (vecMulVec u v)
      = ∑ b, vecMulVec (cutVector owner b u) (cutVector owner b v) := by
  ext i j
  simp only [blockPinch, Matrix.sum_apply, vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hi : owner i = some b <;>
    by_cases hj : owner j = some b <;>
    simp [cutVector, hi, hj]

lemma blockPinch_smul (owner : n → Option β) (z : ℂ)
    (A : Matrix n n ℂ) :
    blockPinch owner (z • A) = z • blockPinch owner A := by
  ext i j
  simp only [blockPinch, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : owner i = some b ∧ owner j = some b <;> simp [h]

lemma blockPinch_sum (owner : n → Option β)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Matrix n n ℂ) :
    blockPinch owner (∑ k, A k) = ∑ k, blockPinch owner (A k) := by
  ext i j
  simp only [blockPinch, Matrix.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : owner i = some b ∧ owner j = some b <;> simp [h]

lemma blockPinch_isHermitian (owner : n → Option β)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (blockPinch owner A).IsHermitian := by
  change (blockPinch owner A)ᴴ = blockPinch owner A
  ext i j
  have hstar : star (A j i) = A i j := by
    have h := congrFun (congrFun hA.eq i) j
    simpa [Matrix.conjTranspose_apply] using h
  simp only [Matrix.conjTranspose_apply, blockPinch, star_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hi : owner i = some b <;>
    by_cases hj : owner j = some b <;>
    simp [hi, hj, hstar]

/-- Spectral decomposition of a Hermitian matrix as a finite sum of
two-vector rank-one matrices. -/
lemma sum_eigen_vecMulVec_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (∑ k, ((hA.eigenvalues k : ℝ) : ℂ) •
      vecMulVec (fun i => (hA.eigenvectorUnitary : Matrix n n ℂ) i k)
        (fun j => star ((hA.eigenvectorUnitary : Matrix n n ℂ) j k))) = A := by
  ext i j
  conv_rhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_diagonal, Matrix.star_apply]
  simp only [Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul, Function.comp_apply]
  ac_rfl

lemma abs_smul_signed_vecMulVec (x : ℝ) (u v : n → ℂ) :
    ((|x| : ℝ) : ℂ) •
        vecMulVec u (if 0 ≤ x then v else -v)
      = ((x : ℝ) : ℂ) • vecMulVec u v := by
  by_cases hx : 0 ≤ x
  · simp [hx, abs_of_nonneg]
  · have hneg : x < 0 := lt_of_not_ge hx
    ext i j
    simp [hx, abs_of_neg hneg, Matrix.smul_apply, vecMulVec_apply]

/-- Contractivity of an incomplete disjoint block pinching for the Hermitian
trace norm defined in `Tail.RankOne`. -/
theorem traceNorm_blockPinch_le (owner : n → Option β)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Tail.traceNorm (blockPinch_isHermitian owner hA) ≤ Tail.traceNorm hA := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let c : n × β → ℝ := fun kb => |hA.eigenvalues kb.1|
  let u : n × β → n → ℂ := fun kb =>
    cutVector owner kb.2 (fun i => U i kb.1)
  let v : n × β → n → ℂ := fun kb =>
    if 0 ≤ hA.eigenvalues kb.1 then
      cutVector owner kb.2 (fun i => star (U i kb.1))
    else -cutVector owner kb.2 (fun i => star (U i kb.1))
  have hc : ∀ kb, 0 ≤ c kb := fun kb => abs_nonneg _
  have hdecomp :
      ∑ kb, ((c kb : ℝ) : ℂ) • vecMulVec (u kb) (v kb)
        = blockPinch owner A := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ k, ∑ b, ((c (k, b) : ℝ) : ℂ) •
          vecMulVec (u (k, b)) (v (k, b)))
          = ∑ k, ∑ b, ((hA.eigenvalues k : ℝ) : ℂ) •
              vecMulVec (cutVector owner b (fun i => U i k))
                (cutVector owner b (fun i => star (U i k))) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro b _
            simpa only [c, u, v] using abs_smul_signed_vecMulVec
              (n := n) (hA.eigenvalues k)
              (cutVector owner b (fun i => U i k))
              (cutVector owner b (fun i => star (U i k)))
      _ = ∑ k, ((hA.eigenvalues k : ℝ) : ℂ) •
            blockPinch owner
              (vecMulVec (fun i => U i k) (fun i => star (U i k))) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [blockPinch_vecMulVec, Finset.smul_sum]
      _ = ∑ k, blockPinch owner
            (((hA.eigenvalues k : ℝ) : ℂ) •
              vecMulVec (fun i => U i k) (fun i => star (U i k))) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [blockPinch_smul]
      _ = blockPinch owner
            (∑ k, ((hA.eigenvalues k : ℝ) : ℂ) •
              vecMulVec (fun i => U i k) (fun i => star (U i k))) := by
            rw [blockPinch_sum]
      _ = blockPinch owner A := by
            rw [show U = (hA.eigenvectorUnitary : Matrix n n ℂ) from rfl,
              sum_eigen_vecMulVec_eq hA]
  have hmajor := traceNorm_le_sum_vecMulVec_two
    (blockPinch_isHermitian owner hA) c hc u v hdecomp
  have hcol : ∀ k, ∑ i, ‖U i k‖ ^ 2 = 1 := by
    have hDS := normSqMatrix_mem_doublyStochastic_of_unitary
      (hA.eigenvectorUnitary).2
    rw [mem_doublyStochastic_iff_sum] at hDS
    obtain ⟨_, _, hcols⟩ := hDS
    intro k
    simpa [U, normSqMatrix] using hcols k
  have hcut : ∀ k, ∑ b, ∑ i,
      ‖cutVector owner b (fun j => U j k) i‖ ^ 2 ≤ 1 := by
    intro k
    exact (sum_cutVector_normSq_le owner (fun j => U j k)).trans_eq (hcol k)
  calc
    Tail.traceNorm (blockPinch_isHermitian owner hA)
        ≤ ∑ kb, c kb *
          ((∑ i, ‖u kb i‖ ^ 2) + ∑ i, ‖v kb i‖ ^ 2) / 2 := hmajor
    _ = ∑ k, |hA.eigenvalues k| *
          (∑ b, ∑ i, ‖cutVector owner b (fun j => U j k) i‖ ^ 2) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        have hstar :
            (∑ i, ‖cutVector owner b (fun j => star (U j k)) i‖ ^ 2) =
              ∑ i, ‖cutVector owner b (fun j => U j k) i‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          simp [cutVector]
        by_cases hk : 0 ≤ hA.eigenvalues k
        · simp only [c, u, v, hk, if_true, Pi.neg_apply, norm_neg]
          rw [hstar]
          ring
        · simp only [c, u, v, hk, if_false, Pi.neg_apply, norm_neg]
          rw [hstar]
          ring
    _ ≤ ∑ k, |hA.eigenvalues k| * 1 := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hcut k) (abs_nonneg _)
    _ = Tail.traceNorm hA := by simp [Tail.traceNorm]

/-- The sum of the trace norms of pairwise disjoint principal submatrices is
at most the trace norm of the ambient Hermitian matrix.  Disjointness is
expressed by injectivity of the combined block-coordinate embedding. -/
theorem sum_traceNorm_principal_le
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (idx : β → γ → n)
    (hinj : Function.Injective (fun bg : β × γ => idx bg.1 bg.2))
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∑ b, Tail.traceNorm (hA.submatrix (idx b)) ≤ Tail.traceNorm hA := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  have hdecomp : ∀ b,
      (∑ k, ((|hA.eigenvalues k| : ℝ) : ℂ) •
        vecMulVec (fun r => U (idx b r) k)
          (if 0 ≤ hA.eigenvalues k then
            (fun r => star (U (idx b r) k))
          else -(fun r => star (U (idx b r) k))))
        = A.submatrix (idx b) (idx b) := by
    intro b
    calc
      (∑ k, ((|hA.eigenvalues k| : ℝ) : ℂ) •
        vecMulVec (fun r => U (idx b r) k)
          (if 0 ≤ hA.eigenvalues k then
            (fun r => star (U (idx b r) k))
          else -(fun r => star (U (idx b r) k))))
          = ∑ k, ((hA.eigenvalues k : ℝ) : ℂ) •
              vecMulVec (fun r => U (idx b r) k)
                (fun r => star (U (idx b r) k)) := by
            apply Finset.sum_congr rfl
            intro k _
            exact abs_smul_signed_vecMulVec (n := γ) (hA.eigenvalues k)
              (fun r => U (idx b r) k)
              (fun r => star (U (idx b r) k))
      _ = (∑ k, ((hA.eigenvalues k : ℝ) : ℂ) •
              vecMulVec (fun i => U i k) (fun i => star (U i k))).submatrix
              (idx b) (idx b) := by
            ext r s
            simp [Matrix.submatrix, Matrix.sum_apply, Matrix.smul_apply,
              vecMulVec_apply]
      _ = A.submatrix (idx b) (idx b) := by
            rw [show U = (hA.eigenvectorUnitary : Matrix n n ℂ) from rfl,
              sum_eigen_vecMulVec_eq hA]
  have hblock : ∀ b,
      Tail.traceNorm (hA.submatrix (idx b)) ≤
        ∑ k, |hA.eigenvalues k| * ∑ r, ‖U (idx b r) k‖ ^ 2 := by
    intro b
    have hraw := traceNorm_le_sum_vecMulVec_two
      (hA.submatrix (idx b))
      (fun k => |hA.eigenvalues k|) (fun k => abs_nonneg _)
      (fun k r => U (idx b r) k)
      (fun k => if 0 ≤ hA.eigenvalues k then
        (fun r => star (U (idx b r) k))
      else -(fun r => star (U (idx b r) k)))
      (hdecomp b)
    refine hraw.trans_eq ?_
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : 0 ≤ hA.eigenvalues k
    · simp only [hk, if_true, Pi.neg_apply, norm_neg, norm_star]
      ring_nf
    · simp only [hk, if_false, Pi.neg_apply, norm_neg, norm_star]
      ring_nf
  have hinjective_energy : ∀ k,
      ∑ b, ∑ r, ‖U (idx b r) k‖ ^ 2 ≤ ∑ i, ‖U i k‖ ^ 2 := by
    intro k
    let e : n → ℝ := fun i => ‖U i k‖ ^ 2
    change (∑ b, ∑ r, e (idx b r)) ≤ ∑ i, e i
    have hprod : (∑ b, ∑ r, e (idx b r)) =
        ∑ bg : β × γ, e (idx bg.1 bg.2) := by
      rw [Fintype.sum_prod_type]
    rw [hprod]
    calc
      (∑ bg : β × γ, e (idx bg.1 bg.2))
          = (Finset.univ.image
              (fun bg : β × γ => idx bg.1 bg.2)).sum e := by
            rw [Finset.sum_image]
            intro a _ b _ hab
            exact hinj hab
      _ ≤ (Finset.univ : Finset n).sum e :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => by dsimp [e]; exact sq_nonneg ‖U i k‖)
      _ = ∑ i, e i := rfl
  have hcol : ∀ k, ∑ i, ‖U i k‖ ^ 2 = 1 := by
    have hDS := normSqMatrix_mem_doublyStochastic_of_unitary
      (hA.eigenvectorUnitary).2
    rw [mem_doublyStochastic_iff_sum] at hDS
    obtain ⟨_, _, hcols⟩ := hDS
    intro k
    simpa [U, normSqMatrix] using hcols k
  calc
    (∑ b, Tail.traceNorm (hA.submatrix (idx b)))
        ≤ ∑ b, ∑ k, |hA.eigenvalues k| *
            ∑ r, ‖U (idx b r) k‖ ^ 2 :=
      Finset.sum_le_sum fun b _ => hblock b
    _ = ∑ k, |hA.eigenvalues k| *
          (∑ b, ∑ r, ‖U (idx b r) k‖ ^ 2) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
    _ ≤ ∑ k, |hA.eigenvalues k| * 1 := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left
          ((hinjective_energy k).trans_eq (hcol k)) (abs_nonneg _)
    _ = Tail.traceNorm hA := by simp [Tail.traceNorm]

/-- Abstract local-energy consequence for disjoint Hermitian principal
triples.  This is the exact finite-dimensional interface consumed by the
zeta binning argument. -/
theorem two_card_mul_sqrt_le_traceNorm_of_principal_triples
    (idx : β → Fin 3 → n)
    (hinj : Function.Injective (fun br : β × Fin 3 => idx br.1 br.2))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (htr : ∀ b, rtrace (H.submatrix (idx b) (idx b)) = 0)
    (henergy : ∀ b, 2 * delta ≤ frobSq (H.submatrix (idx b) (idx b))) :
    2 * (Fintype.card β : ℝ) * Real.sqrt delta ≤ Tail.traceNorm hH := by
  have hlocal : ∀ b, 2 * Real.sqrt delta ≤
      Tail.traceNorm (hH.submatrix (idx b)) := fun b =>
    two_mul_sqrt_le_traceNorm_fin3 hdelta (hH.submatrix (idx b))
      (htr b) (henergy b)
  calc
    2 * (Fintype.card β : ℝ) * Real.sqrt delta
        = ∑ b : β, 2 * Real.sqrt delta := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
    _ ≤ ∑ b, Tail.traceNorm (hH.submatrix (idx b)) :=
      Finset.sum_le_sum fun b _ => hlocal b
    _ ≤ Tail.traceNorm hH := sum_traceNorm_principal_le idx hinj hH

end StrictImprovement
end Zeta23
