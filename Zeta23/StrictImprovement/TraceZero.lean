/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Tail.RankOne
import Zeta23.LinAlg.RankTrace

/-!
# The trace-zero gain for three-dimensional Hermitian blocks

This is the finite-dimensional factor-two improvement used by the strict
simple-zero candidate.  The source is deliberately independent of every zeta
input.  It is a source draft until it has been checked by the pinned Lean
toolchain recorded in `LEAN_FORMALIZATION_PLAN.md`.
-/

noncomputable section

open Matrix Finset

namespace Zeta23
namespace StrictImprovement

open RHLinalg

/-- For three real numbers with zero sum, the square of the `l1` norm is at
least twice the square of the `l2` norm.  The constant two is sharp. -/
lemma three_trace_zero_l1_sq
    (a b c : ℝ) (hsum : a + b + c = 0) :
    2 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (|a| + |b| + |c|) ^ 2 := by
  rcases le_total 0 a with ha | ha <;>
    rcases le_total 0 b with hb | hb <;>
      rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg hc]
    nlinarith
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonpos hc]
    nlinarith [mul_nonneg ha hb]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb, abs_of_nonneg hc]
    nlinarith [mul_nonneg ha hc]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb, abs_of_nonpos hc]
    have hnb : 0 ≤ -b := neg_nonneg.mpr hb
    have hnc : 0 ≤ -c := neg_nonneg.mpr hc
    nlinarith [mul_nonneg hnb hnc]
  · rw [abs_of_nonpos ha, abs_of_nonneg hb, abs_of_nonneg hc]
    nlinarith [mul_nonneg hb hc]
  · rw [abs_of_nonpos ha, abs_of_nonneg hb, abs_of_nonpos hc]
    have hna : 0 ≤ -a := neg_nonneg.mpr ha
    have hnc : 0 ≤ -c := neg_nonneg.mpr hc
    nlinarith [mul_nonneg hna hnc]
  · rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonneg hc]
    have hna : 0 ≤ -a := neg_nonneg.mpr ha
    have hnb : 0 ≤ -b := neg_nonneg.mpr hb
    nlinarith [mul_nonneg hna hnb]
  · rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonpos hc]
    nlinarith

/-- Hermitian `3 x 3` trace-zero form of the sharp trace-norm/Frobenius
inequality. -/
theorem two_frobSq_le_traceNorm_sq_fin3
    {B : Matrix (Fin 3) (Fin 3) ℂ}
    (hB : B.IsHermitian) (htr : rtrace B = 0) :
    2 * frobSq B ≤ (Tail.traceNorm hB) ^ 2 := by
  have hsum :
      hB.eigenvalues 0 + hB.eigenvalues 1 + hB.eigenvalues 2 = 0 := by
    rw [rtrace_eq_sum_eigenvalues hB] at htr
    simpa [Fin.sum_univ_succ, add_assoc] using htr
  have h := three_trace_zero_l1_sq
    (hB.eigenvalues 0) (hB.eigenvalues 1) (hB.eigenvalues 2) hsum
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues hB, Tail.traceNorm]
  simpa [Fin.sum_univ_succ, add_assoc] using h

/-- A trace-zero Hermitian triple whose Frobenius energy is at least
`2 * delta` has trace norm at least `2 * sqrt delta`.  This is the exact local
factor consumed by the improved three-point pinching argument. -/
theorem two_mul_sqrt_le_traceNorm_fin3
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {B : Matrix (Fin 3) (Fin 3) ℂ}
    (hB : B.IsHermitian) (htr : rtrace B = 0)
    (henergy : 2 * delta ≤ frobSq B) :
    2 * Real.sqrt delta ≤ Tail.traceNorm hB := by
  have hmatrix := two_frobSq_le_traceNorm_sq_fin3 hB htr
  have hsqrt_sq : (Real.sqrt delta) ^ 2 = delta := Real.sq_sqrt hdelta
  have hsqrt_nonneg : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
  have htrace_nonneg : 0 ≤ Tail.traceNorm hB := Tail.traceNorm_nonneg hB
  nlinarith

/-- The scalar eigenvalue pattern `(1,-1,0)` attains equality, so the factor
two in `three_trace_zero_l1_sq` cannot be enlarged. -/
lemma three_trace_zero_l1_sq_sharp :
    2 * ((1 : ℝ) ^ 2 + (-1 : ℝ) ^ 2 + (0 : ℝ) ^ 2)
      = (|(1 : ℝ)| + |(-1 : ℝ)| + |(0 : ℝ)|) ^ 2 := by
  norm_num

end StrictImprovement
end Zeta23
