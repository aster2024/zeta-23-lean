/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.LinAlg.RankTrace

/-!
# The below-one refinement of the rank--trace inequality

This file isolates the finite-dimensional spectral statement used by the
strict simple-zero candidate.  It first works with the full ambient list of
eigenvalues.  Removing the forced zero eigenvalues supplied by a rank bound
is a separate downstream step.

This is a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

open RHLinalg

variable {K : Type*} [RCLike K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared distance to one below the threshold one, and zero above it. -/
def unitDefect (x : ℝ) : ℝ :=
  if x < 1 then (1 - x) ^ 2 else 0

/-- Centered defect.  Its value at zero is zero, so it transfers between
`W * Wᴴ` and `Wᴴ * W`. -/
def centeredUnitDefect (x : ℝ) : ℝ := unitDefect x - 1

@[simp] lemma centeredUnitDefect_zero : centeredUnitDefect 0 = 0 := by
  norm_num [centeredUnitDefect, unitDefect]

/-- Sum of the squared deficits below one over the full ambient eigenvalue
list. -/
def belowOneDefect {P : Matrix n n K} (hP : P.IsHermitian) : ℝ :=
  ∑ i, unitDefect (hP.eigenvalues₀ i)

/-- Scalar atom of the refined defect.  A nonnegative negative-part
eigenvalue cannot cancel a below-one deficit for free. -/
lemma refined_scalar_atom (p m : ℝ) (hm : 0 ≤ m) :
    2 * p - 1 - 4 * m + unitDefect p
      ≤ (p - m) ^ 2 := by
  by_cases hp : p < 1
  · rw [unitDefect, if_pos hp]
    have hgap : 0 ≤ 1 - p := sub_nonneg.mpr hp.le
    nlinarith [mul_nonneg hgap hm, sq_nonneg m]
  · rw [unitDefect, if_neg hp]
    nlinarith [sq_nonneg (p - m - 1)]

/-- Ambient-dimension form of the refined rank--trace inequality.

For `P` positive semidefinite and `Q` Hermitian with positive index at most
`b`, the usual `c = 2` rank--trace lower bound gains the complete squared
spectral deficit of the eigenvalues of `P` below one. -/
theorem rank_trace_ineq_two_refined_dimension
    {P Q : Matrix n n K}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace P - (Fintype.card n : ℝ)
        + 4 * rtrace Q - 4 * (b : ℝ)
        + belowOneDefect hP.isHermitian
      ≤ frobSq (P + Q) := by
  classical
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  set d := Fintype.card n
  change 2 * rtrace P - (d : ℝ)
        + 4 * rtrace Q - 4 * (b : ℝ)
        + belowOneDefect hP.isHermitian
      ≤ frobSq (P + Q)
  set p : Fin d → ℝ := hP.isHermitian.eigenvalues₀
  set m : Fin d → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hm_nonneg : ∀ k, 0 ≤ m k := fun k => by
    rw [show m k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _

  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, m k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (m k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  have hdefect : belowOneDefect hP.isHermitian =
      ∑ k, unitDefect (p k) := by
    simp [belowOneDefect, p, d]

  have hexpand : frobSq (P + Q)
      = frobSq P + 2 * RCLike.re (P * Qp).trace
        - 2 * RCLike.re (P * Qm).trace
        + frobSq Qp + frobSq Qm := by
    have hneg : frobSq (-Qm) = frobSq Qm := by
      unfold frobSq
      rw [conjTranspose_neg, neg_mul_neg]
    have hcross : RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]
      simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian
        (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      hneg, hcross, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring

  have hPQp : 0 ≤ RCLike.re (P * Qp).trace :=
    trace_mul_nonneg_of_posSemidef hP hQp_psd
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * m k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  have hminus : ∑ k, (p k - m k) ^ 2
      ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - m k) ^ 2
        = ∑ k, (p k) ^ 2 - 2 * ∑ k, p k * m k
          + ∑ k, (m k) ^ 2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]
    linarith

  have hrefined : 2 * rtrace P - (d : ℝ) - 4 * rtrace Qm
        + belowOneDefect hP.isHermitian
      ≤ ∑ k, (p k - m k) ^ 2 := by
    have hsum : ∑ k,
        (2 * p k - 1 - 4 * m k
          + unitDefect (p k))
        ≤ ∑ k, (p k - m k) ^ 2 :=
      sum_le_sum fun k _ => refined_scalar_atom (p k) (m k) (hm_nonneg k)
    rw [htraceP, htraceQm, hdefect]
    calc
      2 * (∑ k, p k) - (d : ℝ) - 4 * (∑ k, m k)
            + ∑ k, unitDefect (p k)
          = ∑ k,
              (2 * p k - 1 - 4 * m k
                + unitDefect (p k)) := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul]
              ring
      _ ≤ ∑ k, (p k - m k) ^ 2 := hsum

  have hpositive :
      2 * (2 : ℝ) * rtrace Qp - (2 : ℝ) ^ 2 * (b : ℝ) ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ (2 : ℝ)
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0}
        = #{i | 0 < hQ.eigenvalues i} := by
          congr 1
          ext i
          simp [posPart_eq_zero, not_le]
      _ ≤ b := hb

  have htraceQ : 4 * rtrace Q = 4 * rtrace Qp - 4 * rtrace Qm := by
    rw [hQdec, rtrace_sub]
    ring
  linarith [hexpand, hPQp, hminus, hrefined, hpositive, htraceQ]

end StrictImprovement
end Zeta23
