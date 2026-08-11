/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.GramTriples
import Zeta23.StrictImprovement.GramDefect

/-!
# From disjoint Gram triples to the below-one spectral defect

For a unit-vector Gram matrix `G`, this file proves the finite-dimensional
chain

`local triple energy -> trace norm of G-I -> linear below-one deficit
 -> squared below-one defect`.

The proof deliberately avoids identifying the ordered eigenvalue list of
`G-I`: an explicit decomposition in the eigenbasis of `G` gives the only
trace-norm inequality that is needed.

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

/-- Unsquared deficit below one. -/
def linearUnitDefect (p : ℝ) : ℝ :=
  if p < 1 then 1 - p else 0

lemma linearUnitDefect_nonneg (p : ℝ) : 0 ≤ linearUnitDefect p := by
  by_cases hp : p < 1
  · simp [linearUnitDefect, hp, hp.le]
  · simp [linearUnitDefect, hp]

lemma unitDefect_eq_linear_sq (p : ℝ) :
    unitDefect p = (linearUnitDefect p) ^ 2 := by
  by_cases hp : p < 1 <;> simp [unitDefect, linearUnitDefect, hp]

lemma abs_sub_one_eq_shift_add_linear (p : ℝ) :
    |p - 1| = (p - 1) + 2 * linearUnitDefect p := by
  by_cases hp : p < 1
  · rw [linearUnitDefect, if_pos hp, abs_of_nonpos (sub_nonpos.mpr hp.le)]
    ring
  · rw [linearUnitDefect, if_neg hp, abs_of_nonneg (sub_nonneg.mpr (not_lt.mp hp))]
    ring

/-- Spectral rank-one expansion of `specMap`. -/
lemma sum_spec_vecMulVec_eq
    {A : Matrix s s ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (∑ k, ((f (hA.eigenvalues k) : ℝ) : ℂ) •
      vecMulVec (fun i => (hA.eigenvectorUnitary : Matrix s s ℂ) i k)
        (fun j => star ((hA.eigenvectorUnitary : Matrix s s ℂ) j k)))
      = specMap hA f := by
  unfold specMap
  ext i j
  rw [Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_diagonal, Matrix.star_apply]
  simp only [Finset.sum_apply, Matrix.smul_apply, vecMulVec_apply,
    Complex.real_smul, smul_eq_mul, Function.comp_apply]
  ring

lemma specMap_sub_one
    {A : Matrix s s ℂ} (hA : A.IsHermitian) :
    specMap hA (fun p => p - 1) = A - 1 := by
  have hfun : (fun p : ℝ => p - 1) = id - (fun _ => 1) := by
    funext p
    rfl
  have hone : specMap hA (fun _ => 1) = 1 := by
    unfold specMap
    simp
  rw [hfun, specMap_sub, specMap_id, hone]

/-- The trace norm of `G-I`, estimated using the eigenbasis of `G`, is at
most the total absolute displacement of the eigenvalues of `G` from one. -/
lemma traceNorm_gramDeviation_le_sum_abs_shift
    (x : s → d → ℂ) :
    Tail.traceNorm (gramDeviation_isHermitian x)
      ≤ ∑ k, |(gramMatrix_isHermitian x).eigenvalues k - 1| := by
  let hG : (gramMatrix x).IsHermitian := gramMatrix_isHermitian x
  let U : Matrix s s ℂ := hG.eigenvectorUnitary
  let c : s → ℝ := fun k => |hG.eigenvalues k - 1|
  let u : s → s → ℂ := fun k i => U i k
  let v : s → s → ℂ := fun k =>
    if 0 ≤ hG.eigenvalues k - 1 then
      (fun i => star (U i k))
    else -(fun i => star (U i k))
  have hc : ∀ k, 0 ≤ c k := fun k => abs_nonneg _
  have hdecomp :
      ∑ k, ((c k : ℝ) : ℂ) • vecMulVec (u k) (v k)
        = gramDeviation x := by
    calc
      (∑ k, ((c k : ℝ) : ℂ) • vecMulVec (u k) (v k))
          = ∑ k, (((hG.eigenvalues k - 1 : ℝ)) : ℂ) •
              vecMulVec (fun i => U i k) (fun i => star (U i k)) := by
            apply Finset.sum_congr rfl
            intro k _
            simpa only [c, u, v] using abs_smul_signed_vecMulVec
              (n := s) (hG.eigenvalues k - 1)
              (fun i => U i k) (fun i => star (U i k))
      _ = specMap hG (fun p => p - 1) := by
            simpa only [U] using sum_spec_vecMulVec_eq hG (fun p => p - 1)
      _ = gramDeviation x := by
            rw [specMap_sub_one hG]
            rfl
  have hraw := traceNorm_le_sum_vecMulVec_two
    (gramDeviation_isHermitian x) c hc u v hdecomp
  have hcol : ∀ k, ∑ i, ‖U i k‖ ^ 2 = 1 := by
    have hDS := normSqMatrix_mem_doublyStochastic_of_unitary
      (hG.eigenvectorUnitary).2
    rw [mem_doublyStochastic_iff_sum] at hDS
    obtain ⟨_, _, hcols⟩ := hDS
    intro k
    simpa [U, normSqMatrix] using hcols k
  calc
    Tail.traceNorm (gramDeviation_isHermitian x)
        ≤ ∑ k, c k *
          ((∑ i, ‖u k i‖ ^ 2) + ∑ i, ‖v k i‖ ^ 2) / 2 := hraw
    _ = ∑ k, |hG.eigenvalues k - 1| := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : 0 ≤ hG.eigenvalues k - 1 <;>
          simp only [c, u, v, hk, if_true, if_false, Pi.neg_apply,
            norm_neg, norm_star, hcol]
        ring
    _ = ∑ k, |(gramMatrix_isHermitian x).eigenvalues k - 1| := rfl

/-- The unit diagonal forces the sum of the eigenvalue displacements from
one to vanish. -/
lemma sum_gram_eigen_sub_one_eq_zero
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1) :
    ∑ k, ((gramMatrix_isHermitian x).eigenvalues k - 1) = 0 := by
  have htrace : rtrace (gramMatrix x) = (Fintype.card s : ℝ) := by
    unfold rtrace Matrix.trace
    simp [gramMatrix_diag, hunit]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← rtrace_eq_sum_eigenvalues (gramMatrix_isHermitian x),
    htrace]
  ring

lemma sum_abs_gram_shift_eq_two_linearDefect
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1) :
    ∑ k, |(gramMatrix_isHermitian x).eigenvalues k - 1|
      = 2 * ∑ k, linearUnitDefect ((gramMatrix_isHermitian x).eigenvalues k) := by
  calc
    (∑ k, |(gramMatrix_isHermitian x).eigenvalues k - 1|)
        = ∑ k, ((gramMatrix_isHermitian x).eigenvalues k - 1
            + 2 * linearUnitDefect ((gramMatrix_isHermitian x).eigenvalues k)) := by
          apply Finset.sum_congr rfl
          intro k _
          exact abs_sub_one_eq_shift_add_linear _
    _ = (∑ k, ((gramMatrix_isHermitian x).eigenvalues k - 1))
          + 2 * ∑ k, linearUnitDefect
              ((gramMatrix_isHermitian x).eigenvalues k) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * ∑ k, linearUnitDefect
            ((gramMatrix_isHermitian x).eigenvalues k) := by
          rw [sum_gram_eigen_sub_one_eq_zero x hunit, zero_add]

/-- Complete finite-dimensional `/9` input: disjoint local Gram triples with
energy at least `delta` force a quantitative below-one squared spectral
defect.  The division-free form also covers an empty ambient type. -/
theorem card_sq_mul_delta_le_card_mul_belowOneDefect
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    (idx : β → Fin 3 → s)
    (hinj : Function.Injective (fun br : β × Fin 3 => idx br.1 br.2))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ b, delta ≤ tripleCorrelationEnergy x idx b) :
    (Fintype.card β : ℝ) ^ 2 * delta
      ≤ (Fintype.card s : ℝ) *
        belowOneDefect (gramMatrix_isHermitian x) := by
  let V : ℝ := ∑ k, linearUnitDefect
    ((gramMatrix_isHermitian x).eigenvalues k)
  have hV_nonneg : 0 ≤ V := Finset.sum_nonneg fun k _ =>
    linearUnitDefect_nonneg _
  have hlocal_trace := gram_triples_traceNorm_lower
    x hunit idx hinj hdelta hlocal
  have htrace_upper := traceNorm_gramDeviation_le_sum_abs_shift x
  have habs := sum_abs_gram_shift_eq_two_linearDefect x hunit
  have hTV : (Fintype.card β : ℝ) * Real.sqrt delta ≤ V := by
    dsimp [V]
    linarith
  have hsqV : V ^ 2 ≤ (Fintype.card s : ℝ) *
      belowOneDefect (gramMatrix_isHermitian x) := by
    have hCS : V ^ 2 ≤ (Fintype.card s : ℝ) *
        ∑ k, (linearUnitDefect
          ((gramMatrix_isHermitian x).eigenvalues k)) ^ 2 := by
      dsimp [V]
      simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset s))
          (f := fun k => linearUnitDefect
            ((gramMatrix_isHermitian x).eigenvalues k)))
    have hdefect : belowOneDefect (gramMatrix_isHermitian x) =
        ∑ k, (linearUnitDefect
          ((gramMatrix_isHermitian x).eigenvalues k)) ^ 2 := by
      unfold belowOneDefect
      rw [← sum_eigenvalues_reindex (gramMatrix_isHermitian x) unitDefect]
      apply Finset.sum_congr rfl
      intro k _
      exact unitDefect_eq_linear_sq _
    rwa [← hdefect] at hCS
  have hsqrt_sq : (Real.sqrt delta) ^ 2 = delta := Real.sq_sqrt hdelta
  have hsqrt_nonneg : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
  have hcard_nonneg : 0 ≤ (Fintype.card β : ℝ) := by positivity
  have hfactor_nonneg :
      0 ≤ (V - (Fintype.card β : ℝ) * Real.sqrt delta) *
        (V + (Fintype.card β : ℝ) * Real.sqrt delta) :=
    mul_nonneg (sub_nonneg.mpr hTV)
      (add_nonneg hV_nonneg (mul_nonneg hcard_nonneg hsqrt_nonneg))
  have hsqTV :
      ((Fintype.card β : ℝ) * Real.sqrt delta) ^ 2 ≤ V ^ 2 := by
    nlinarith
  calc
    (Fintype.card β : ℝ) ^ 2 * delta
        = ((Fintype.card β : ℝ) * Real.sqrt delta) ^ 2 := by
            rw [mul_pow, hsqrt_sq]
    _ ≤ V ^ 2 := hsqTV
    _ ≤ (Fintype.card s : ℝ) *
        belowOneDefect (gramMatrix_isHermitian x) := hsqV

end StrictImprovement
end Zeta23
