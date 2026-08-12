/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.LocalPinching

/-!
# Unit-vector Gram triples

This file connects the abstract disjoint-principal-triple theorem to the
concrete matrix `H = G - I`, where `G` is the Gram matrix of unit complex
vectors.  It proves Hermitianity, zero diagonal/trace, and the exact
three-point Frobenius-energy identity.

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

/-- Gram matrix of a finite family of complex vectors. -/
def gramMatrix (x : s → d → ℂ) : Matrix s s ℂ :=
  fun i j => star (x i) ⬝ᵥ x j

/-- Centered Gram matrix `G - I`. -/
def gramDeviation (x : s → d → ℂ) : Matrix s s ℂ :=
  gramMatrix x - 1

lemma gramMatrix_isHermitian (x : s → d → ℂ) :
    (gramMatrix x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [gramMatrix, dotProduct, Pi.star_apply, star_sum, star_mul',
    star_star]
  apply Finset.sum_congr rfl
  intro k _
  ac_rfl

lemma gramMatrix_diag (x : s → d → ℂ) (i : s) :
    gramMatrix x i i = ((∑ k, ‖x i k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [gramMatrix, dotProduct, Pi.star_apply, Complex.star_def,
    Complex.conj_mul']
  push_cast
  rfl

lemma gramDeviation_isHermitian (x : s → d → ℂ) :
    (gramDeviation x).IsHermitian :=
  (gramMatrix_isHermitian x).sub Matrix.isHermitian_one

lemma gramDeviation_diag_zero (x : s → d → ℂ)
    (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1) (i : s) :
    gramDeviation x i i = 0 := by
  rw [gramDeviation, Matrix.sub_apply, gramMatrix_diag, hunit i]
  simp

lemma gramDeviation_offdiag (x : s → d → ℂ)
    {i j : s} (hij : i ≠ j) :
    gramDeviation x i j = gramMatrix x i j := by
  simp [gramDeviation, hij]

private lemma frobSq_eq_sum_norm_sq_local
    {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) :
    frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold frobSq
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum, RCLike.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Exact Frobenius bookkeeping for a Hermitian `3 x 3` matrix with zero
diagonal. -/
lemma frobSq_fin3_of_diag_zero
    {B : Matrix (Fin 3) (Fin 3) ℂ} (hB : B.IsHermitian)
    (hdiag : ∀ i, B i i = 0) :
    frobSq B = 2 *
      (‖B 0 1‖ ^ 2 + ‖B 0 2‖ ^ 2 + ‖B 1 2‖ ^ 2) := by
  have hsymm : ∀ i j, ‖B j i‖ = ‖B i j‖ := by
    intro i j
    calc
      ‖B j i‖ = ‖star (B j i)‖ := (norm_star _).symm
      _ = ‖B i j‖ := by rw [hB.apply]
  have h10 : ‖B 1 0‖ = ‖B 0 1‖ := hsymm 0 1
  have h20 : ‖B 2 0‖ = ‖B 0 2‖ := hsymm 0 2
  have h21 : ‖B 2 1‖ = ‖B 1 2‖ := hsymm 1 2
  rw [frobSq_eq_sum_norm_sq_local]
  simp [Fin.sum_univ_succ, hdiag, h10, h20, h21]
  ring

/-- Sum of the three unordered squared correlations in one indexed triple. -/
def tripleCorrelationEnergy (x : s → d → ℂ)
    (idx : β → Fin 3 → s) (b : β) : ℝ :=
  ‖gramMatrix x (idx b 0) (idx b 1)‖ ^ 2
    + ‖gramMatrix x (idx b 0) (idx b 2)‖ ^ 2
    + ‖gramMatrix x (idx b 1) (idx b 2)‖ ^ 2

/-- Exact energy identity for a principal Gram triple. -/
lemma frobSq_gramDeviation_triple
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    (idx : β → Fin 3 → s)
    (hinj : Function.Injective (fun br : β × Fin 3 => idx br.1 br.2))
    (b : β) :
    frobSq ((gramDeviation x).submatrix (idx b) (idx b))
      = 2 * tripleCorrelationEnergy x idx b := by
  have hlocal_ne : ∀ {r t : Fin 3}, r ≠ t → idx b r ≠ idx b t := by
    intro r t hrt heq
    have hp : (b, r) = (b, t) := hinj heq
    exact hrt (congrArg Prod.snd hp)
  have hdiag : ∀ r,
      (gramDeviation x).submatrix (idx b) (idx b) r r = 0 := fun r =>
    gramDeviation_diag_zero x hunit (idx b r)
  have h01 : (gramDeviation x).submatrix (idx b) (idx b) 0 1 =
      gramMatrix x (idx b 0) (idx b 1) := by
    exact gramDeviation_offdiag x
      (hlocal_ne (by decide : (0 : Fin 3) ≠ 1))
  have h02 : (gramDeviation x).submatrix (idx b) (idx b) 0 2 =
      gramMatrix x (idx b 0) (idx b 2) := by
    exact gramDeviation_offdiag x
      (hlocal_ne (by decide : (0 : Fin 3) ≠ 2))
  have h12 : (gramDeviation x).submatrix (idx b) (idx b) 1 2 =
      gramMatrix x (idx b 1) (idx b 2) := by
    exact gramDeviation_offdiag x
      (hlocal_ne (by decide : (1 : Fin 3) ≠ 2))
  rw [frobSq_fin3_of_diag_zero
    ((gramDeviation_isHermitian x).submatrix (idx b)) hdiag]
  rw [h01, h02, h12]
  rfl

/-- Unit-vector Gram triples with local correlation energy at least `delta`
force the global centered Gram matrix to have trace norm at least
`2 * number_of_triples * sqrt delta`. -/
theorem gram_triples_traceNorm_lower
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    (idx : β → Fin 3 → s)
    (hinj : Function.Injective (fun br : β × Fin 3 => idx br.1 br.2))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ b, delta ≤ tripleCorrelationEnergy x idx b) :
    2 * (Fintype.card β : ℝ) * Real.sqrt delta
      ≤ Tail.traceNorm (gramDeviation_isHermitian x) := by
  apply two_card_mul_sqrt_le_traceNorm_of_principal_triples idx hinj hdelta
    (gramDeviation_isHermitian x)
  · intro b
    unfold rtrace Matrix.trace
    simp [gramDeviation_diag_zero x hunit]
  · intro b
    rw [frobSq_gramDeviation_triple x hunit idx hinj b]
    exact mul_le_mul_of_nonneg_left (hlocal b) (by norm_num)

end StrictImprovement
end Zeta23
