/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Tail.RankOne
import Zeta23.LinAlg.VonNeumann

/-!
# Triangle and reverse-triangle inequalities for the Hermitian trace norm

`Tail.traceNorm` was introduced directly as the sum of the absolute
eigenvalues of a Hermitian matrix.  This file proves the norm inequalities
needed for finite/full Gram-matrix perturbations without adding a Schatten
norm as a second representation.

The key auxiliary fact is elementary: in any orthonormal basis, the sum of
the absolute diagonal entries of a Hermitian matrix is at most the sum of the
absolute eigenvalues.  It follows by writing the change-of-basis squared
moduli as a doubly stochastic matrix.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The absolute diagonal sum in an arbitrary unitary basis is bounded by
the Hermitian trace norm. -/
theorem sum_abs_re_diag_unitary_conj_le_traceNorm
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) :
    ∑ i, |Complex.re
        ((star (U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)) i i)|
      ≤ traceNorm hA := by
  let U₀ : Matrix n n ℂ := U
  let Uₐ : Matrix n n ℂ := hA.eigenvectorUnitary
  let D : Matrix n n ℂ := diagonal (Complex.ofReal ∘ hA.eigenvalues)
  let W : Matrix n n ℂ := star U₀ * Uₐ
  have hW : W ∈ Matrix.unitaryGroup n ℂ := by
    dsimp [W, U₀, Uₐ]
    exact mul_mem (Unitary.star_mem U.2) hA.eigenvectorUnitary.2
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary hW
  rw [mem_doublyStochastic_iff_sum] at hDS
  rcases hDS with ⟨hSnonneg, _hrow, hcol⟩
  have hconj : star U₀ * A * U₀ = W * D * star W := by
    rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    dsimp [W, D, U₀, Uₐ]
    simp only [StarMul.star_mul, star_star]
    noncomm_ring
  have hentry : ∀ i,
      Complex.re ((star U₀ * A * U₀) i i) =
        ∑ j, normSqMatrix W i j * hA.eigenvalues j := by
    intro i
    rw [hconj, Matrix.mul_apply]
    dsimp [D]
    simp only [mul_diagonal, Function.comp_apply]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [show W i j * (hA.eigenvalues j : ℂ) * starRingEnd ℂ (W i j) =
        ((hA.eigenvalues j * ‖W i j‖ ^ 2 : ℝ) : ℂ) by
      rw [show W i j * (hA.eigenvalues j : ℂ) * starRingEnd ℂ (W i j) =
          (hA.eigenvalues j : ℂ) *
            (W i j * starRingEnd ℂ (W i j)) by ring,
        RCLike.mul_conj]
      push_cast
      rfl]
    simp only [Complex.ofReal_re, normSqMatrix, Matrix.of_apply]
    ring
  have hdiag : ∀ i,
      |Complex.re ((star U₀ * A * U₀) i i)| ≤
        ∑ j, normSqMatrix W i j * |hA.eigenvalues j| := by
    intro i
    rw [hentry]
    calc
      |∑ j, normSqMatrix W i j * hA.eigenvalues j|
          ≤ ∑ j, |normSqMatrix W i j * hA.eigenvalues j| :=
            abs_sum_le_sum_abs _ _
      _ = ∑ j, normSqMatrix W i j * |hA.eigenvalues j| := by
        refine sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hSnonneg i j)]
  calc
    ∑ i, |Complex.re
        ((star (U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)) i i)|
        ≤ ∑ i, ∑ j, normSqMatrix W i j * |hA.eigenvalues j| :=
          sum_le_sum fun i _ => by simpa [U₀] using hdiag i
    _ = ∑ j, |hA.eigenvalues j| * ∑ i, normSqMatrix W i j := by
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring
    _ = ∑ j, |hA.eigenvalues j| := by
      refine sum_congr rfl fun j _ => ?_
      rw [hcol j, mul_one]
    _ = traceNorm hA := rfl

/-- In its own eigenbasis, the absolute diagonal sum is exactly the trace
norm. -/
theorem traceNorm_eq_sum_abs_re_diag_eigenbasis
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm hA =
      ∑ i, |Complex.re
        ((star (hA.eigenvectorUnitary : Matrix n n ℂ) * A *
          (hA.eigenvectorUnitary : Matrix n n ℂ)) i i)| := by
  let U : Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary
  let D : Matrix n n ℂ :=
    diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hspectral : A =
      (U : Matrix n n ℂ) * D * star (U : Matrix n n ℂ) := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hdiag :
      star (U : Matrix n n ℂ) * A * (U : Matrix n n ℂ) = D := by
    calc
      star (U : Matrix n n ℂ) * A * (U : Matrix n n ℂ) =
          star (U : Matrix n n ℂ) *
            ((U : Matrix n n ℂ) * D * star (U : Matrix n n ℂ)) *
            (U : Matrix n n ℂ) :=
        congrArg (fun M : Matrix n n ℂ =>
          star (U : Matrix n n ℂ) * M * (U : Matrix n n ℂ)) hspectral
      _ = (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) * D *
          (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) := by
        noncomm_ring
      _ = D := by
        rw [Unitary.star_mul_self_of_mem U.2]
        simp
  change traceNorm hA =
    ∑ i, |Complex.re
      ((star (U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)) i i)|
  rw [hdiag]
  dsimp [D]
  simp [traceNorm]

/-- The custom trace norm depends on the matrix, not on the particular proof
of Hermitianity. -/
theorem traceNorm_congr
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A = B) : traceNorm hA = traceNorm hB := by
  subst B
  rfl

/-- Triangle inequality for the custom Hermitian trace norm. -/
theorem traceNorm_add_le
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (hA.add hB) ≤ traceNorm hA + traceNorm hB := by
  let U : Matrix.unitaryGroup n ℂ := (hA.add hB).eigenvectorUnitary
  have hsplit :
      star (U : Matrix n n ℂ) * (A + B) * (U : Matrix n n ℂ) =
        star (U : Matrix n n ℂ) * A * (U : Matrix n n ℂ) +
        star (U : Matrix n n ℂ) * B * (U : Matrix n n ℂ) := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  rw [traceNorm_eq_sum_abs_re_diag_eigenbasis (hA.add hB)]
  calc
    ∑ i, |Complex.re
        ((star (U : Matrix n n ℂ) * (A + B) * (U : Matrix n n ℂ)) i i)|
        ≤ ∑ i,
          (|Complex.re ((star (U : Matrix n n ℂ) * A *
              (U : Matrix n n ℂ)) i i)| +
           |Complex.re ((star (U : Matrix n n ℂ) * B *
              (U : Matrix n n ℂ)) i i)|) := by
          refine sum_le_sum fun i _ => ?_
          rw [hsplit, Matrix.add_apply]
          change |Complex.re ((star (U : Matrix n n ℂ) * A *
              (U : Matrix n n ℂ)) i i) +
                Complex.re ((star (U : Matrix n n ℂ) * B *
                  (U : Matrix n n ℂ)) i i)| ≤ _
          exact abs_add_le _ _
    _ = (∑ i, |Complex.re ((star (U : Matrix n n ℂ) * A *
          (U : Matrix n n ℂ)) i i)|) +
        ∑ i, |Complex.re ((star (U : Matrix n n ℂ) * B *
          (U : Matrix n n ℂ)) i i)| := sum_add_distrib
    _ ≤ traceNorm hA + traceNorm hB := add_le_add
      (sum_abs_re_diag_unitary_conj_le_traceNorm hA U)
      (sum_abs_re_diag_unitary_conj_le_traceNorm hB U)

/-- Negating a Hermitian matrix does not change its trace norm. -/
theorem traceNorm_neg
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm hA.neg = traceNorm hA := by
  have hconj_neg (U : Matrix.unitaryGroup n ℂ) :
      star (U : Matrix n n ℂ) * (-A) * (U : Matrix n n ℂ) =
        -(star (U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)) := by
    noncomm_ring
  have hsum_neg (U : Matrix.unitaryGroup n ℂ) :
      (∑ i, |Complex.re
        ((star (U : Matrix n n ℂ) * (-A) * (U : Matrix n n ℂ)) i i)|) =
      ∑ i, |Complex.re
        ((star (U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)) i i)| := by
    refine sum_congr rfl fun i _ => ?_
    have hentry := congrArg (fun M : Matrix n n ℂ => M i i) (hconj_neg U)
    rw [hentry]
    simp
  have hle : traceNorm hA.neg ≤ traceNorm hA := by
    rw [traceNorm_eq_sum_abs_re_diag_eigenbasis hA.neg]
    rw [hsum_neg]
    exact sum_abs_re_diag_unitary_conj_le_traceNorm hA
      hA.neg.eigenvectorUnitary
  have hle' : traceNorm hA ≤ traceNorm hA.neg := by
    have h := sum_abs_re_diag_unitary_conj_le_traceNorm hA.neg
      hA.eigenvectorUnitary
    rw [hsum_neg] at h
    rw [traceNorm_eq_sum_abs_re_diag_eigenbasis hA]
    exact h
  exact le_antisymm hle hle'

/-- Reverse triangle inequality, stated in the exact form used by the
finite/full perturbation bridge. -/
theorem abs_traceNorm_sub_traceNorm_le
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |traceNorm hA - traceNorm hB| ≤ traceNorm (hA.sub hB) := by
  have hAB : traceNorm hA ≤ traceNorm hB + traceNorm (hA.sub hB) := by
    have h := traceNorm_add_le hB (hA.sub hB)
    rw [traceNorm_congr (hB.add (hA.sub hB)) hA (by abel)] at h
    exact h
  have hBA : traceNorm hB ≤ traceNorm hA + traceNorm (hA.sub hB) := by
    have h := traceNorm_add_le hA (hA.sub hB).neg
    have hneg := traceNorm_neg (hA.sub hB)
    rw [hneg] at h
    rw [traceNorm_congr (hA.add (hA.sub hB).neg) hB (by abel)] at h
    exact h
  rw [abs_le]
  constructor <;> linarith

end Tail
end Zeta23

end
