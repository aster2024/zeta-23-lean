/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Tail.TraceNormTriangle
import Zeta23.StrictImprovement.FourBlockDefect

/-!
# Four-point spectral stability under entrywise perturbation

This is the finite-dimensional bridge from the endpoint spectral certificate
to a nearby finite normalized Gram block.  Six upper-triangular errors of
size at most `eps` give Frobenius error at most `sqrt 12 * eps`, hence half
trace norm changes by at most `2 * sqrt 3 * eps`.
-/

noncomputable section

open Matrix Finset Real
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

/-- In dimension four, the Hermitian trace norm is at most twice the
Frobenius norm. -/
theorem traceNorm_le_two_sqrt_frobSq_fin4
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.IsHermitian) :
    Tail.traceNorm hA ≤ 2 * Real.sqrt (frobSq A) := by
  have hsq : (Tail.traceNorm hA) ^ 2 ≤ 4 * frobSq A := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hA, Tail.traceNorm]
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun i => |hA.eigenvalues i|)
    simpa [sq_abs] using h
  have hfrob : 0 ≤ frobSq A := frobSq_nonneg A
  have hsqrt : 0 ≤ Real.sqrt (frobSq A) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (frobSq A)) ^ 2 = frobSq A :=
    Real.sq_sqrt hfrob
  have htrace := Tail.traceNorm_nonneg hA
  nlinarith

/-- A Hermitian zero-diagonal `Fin 4` matrix whose six upper-triangular
entries have norm at most `eps` has Frobenius square at most `12*eps^2`. -/
theorem frobSq_fin4_le_twelve_eps_sq
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.IsHermitian)
    (hdiag : ∀ i, A i i = 0) {eps : ℝ} (heps : 0 ≤ eps)
    (h01 : ‖A 0 1‖ ≤ eps) (h02 : ‖A 0 2‖ ≤ eps)
    (h03 : ‖A 0 3‖ ≤ eps) (h12 : ‖A 1 2‖ ≤ eps)
    (h13 : ‖A 1 3‖ ≤ eps) (h23 : ‖A 2 3‖ ≤ eps) :
    frobSq A ≤ 12 * eps ^ 2 := by
  rw [frobSq_fin4_of_diag_zero hA hdiag]
  have h01' := sq_le_sq' (by linarith [norm_nonneg (A 0 1)]) h01
  have h02' := sq_le_sq' (by linarith [norm_nonneg (A 0 2)]) h02
  have h03' := sq_le_sq' (by linarith [norm_nonneg (A 0 3)]) h03
  have h12' := sq_le_sq' (by linarith [norm_nonneg (A 1 2)]) h12
  have h13' := sq_le_sq' (by linarith [norm_nonneg (A 1 3)]) h13
  have h23' := sq_le_sq' (by linarith [norm_nonneg (A 2 3)]) h23
  nlinarith

/-- Half trace norm is `2*sqrt 3*eps`-Lipschitz for two Hermitian
zero-diagonal four-by-four matrices with six entrywise errors. -/
theorem half_traceNorm_sub_le_two_sqrt_three_eps_fin4
    {A B : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hdiagA : ∀ i, A i i = 0) (hdiagB : ∀ i, B i i = 0)
    {eps : ℝ} (heps : 0 ≤ eps)
    (h01 : ‖A 0 1 - B 0 1‖ ≤ eps)
    (h02 : ‖A 0 2 - B 0 2‖ ≤ eps)
    (h03 : ‖A 0 3 - B 0 3‖ ≤ eps)
    (h12 : ‖A 1 2 - B 1 2‖ ≤ eps)
    (h13 : ‖A 1 3 - B 1 3‖ ≤ eps)
    (h23 : ‖A 2 3 - B 2 3‖ ≤ eps) :
    |Tail.traceNorm hA / 2 - Tail.traceNorm hB / 2| ≤
      2 * Real.sqrt 3 * eps := by
  let C : Matrix (Fin 4) (Fin 4) ℂ := A - B
  have hC : C.IsHermitian := hA.sub hB
  have hdiagC : ∀ i, C i i = 0 := by
    intro i
    simp [C, hdiagA i, hdiagB i]
  have hfrob : frobSq C ≤ 12 * eps ^ 2 := by
    apply frobSq_fin4_le_twelve_eps_sq hC hdiagC heps <;>
      simpa [C, Matrix.sub_apply]
  have htraceC := traceNorm_le_two_sqrt_frobSq_fin4 hC
  have hsqrt3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt3Sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrtFrob : 0 ≤ Real.sqrt (frobSq C) := Real.sqrt_nonneg _
  have hsqrtFrobSq : (Real.sqrt (frobSq C)) ^ 2 = frobSq C :=
    Real.sq_sqrt (frobSq_nonneg C)
  have hsqrtBound : Real.sqrt (frobSq C) ≤ 2 * Real.sqrt 3 * eps := by
    nlinarith [sq_nonneg (Real.sqrt (frobSq C) - 2 * Real.sqrt 3 * eps)]
  have hreverse := Tail.abs_traceNorm_sub_traceNorm_le hA hB
  rw [← sub_div, abs_div]
  norm_num
  calc
    |Tail.traceNorm hA - Tail.traceNorm hB| / 2
        ≤ Tail.traceNorm hC / 2 := div_le_div_of_nonneg_right hreverse (by norm_num)
    _ ≤ (2 * Real.sqrt (frobSq C)) / 2 :=
      div_le_div_of_nonneg_right htraceC (by norm_num)
    _ ≤ 2 * Real.sqrt 3 * eps := by nlinarith

end StrictImprovement
end Zeta23

end
