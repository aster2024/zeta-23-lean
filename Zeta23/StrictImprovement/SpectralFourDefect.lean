/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.FourBlockDefect

/-!
# Four-point spectral-mass defect coefficient

This file replaces the six-edge Frobenius premise by a direct lower bound for
the trace norm of every packed four-point principal Gram deviation.  It is
finite-dimensional and contains no zeta or interval input.

If every local block has half trace norm at least `sqrt m`, disjoint pinching
gives global half trace norm at least `t * sqrt m`.  Cauchy--Schwarz then gives
the below-one squared defect `t^2 * m / s`; width-six four-packing contributes
the exact coefficient `m / (16*s)`.
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

/-- Direct local trace-norm lower bounds add across pairwise disjoint
principal four-blocks. -/
theorem spectral_fours_traceNorm_lower
    (x : s → d → ℂ)
    (idx : β → Fin 4 → s)
    (hinj : Function.Injective (fun br : β × Fin 4 => idx br.1 br.2))
    {m : ℝ}
    (hlocal : ∀ b,
      2 * Real.sqrt m ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix (idx b))) :
    2 * (Fintype.card β : ℝ) * Real.sqrt m ≤
      Tail.traceNorm (gramDeviation_isHermitian x) := by
  calc
    2 * (Fintype.card β : ℝ) * Real.sqrt m =
        ∑ b : β, 2 * Real.sqrt m := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
    _ ≤ ∑ b, Tail.traceNorm
          ((gramDeviation_isHermitian x).submatrix (idx b)) :=
      Finset.sum_le_sum fun b _ => hlocal b
    _ ≤ Tail.traceNorm (gramDeviation_isHermitian x) :=
      sum_traceNorm_principal_le idx hinj (gramDeviation_isHermitian x)

/-- Direct local half-trace-norm mass `sqrt m` yields the global below-one
squared defect `card β ^ 2 * m / card s`. -/
theorem card_sq_mul_spectral_mass_le_card_mul_belowOneDefect
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    (idx : β → Fin 4 → s)
    (hinj : Function.Injective (fun br : β × Fin 4 => idx br.1 br.2))
    {m : ℝ} (hm : 0 ≤ m)
    (hlocal : ∀ b,
      2 * Real.sqrt m ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix (idx b))) :
    (Fintype.card β : ℝ) ^ 2 * m ≤
      (Fintype.card s : ℝ) * belowOneDefect (gramMatrix_isHermitian x) := by
  let V : ℝ := ∑ k, linearUnitDefect
    ((gramMatrix_isHermitian x).eigenvalues k)
  have hVNonneg : 0 ≤ V := Finset.sum_nonneg fun k _ =>
    linearUnitDefect_nonneg _
  have hlocalTrace := spectral_fours_traceNorm_lower
    x idx hinj hlocal
  have htraceUpper := traceNorm_gramDeviation_le_sum_abs_shift x
  have habs := sum_abs_gram_shift_eq_two_linearDefect x hunit
  have hTV : (Fintype.card β : ℝ) * Real.sqrt m ≤ V := by
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
  have hsqrtSq : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt hm
  have hfactor :
      0 ≤ (V - (Fintype.card β : ℝ) * Real.sqrt m) *
        (V + (Fintype.card β : ℝ) * Real.sqrt m) :=
    mul_nonneg (sub_nonneg.mpr hTV)
      (add_nonneg hVNonneg
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))
  have hsqTV :
      ((Fintype.card β : ℝ) * Real.sqrt m) ^ 2 ≤ V ^ 2 := by
    nlinarith
  calc
    (Fintype.card β : ℝ) ^ 2 * m =
        ((Fintype.card β : ℝ) * Real.sqrt m) ^ 2 := by
          rw [mul_pow, hsqrtSq]
    _ ≤ V ^ 2 := hsqTV
    _ ≤ (Fintype.card s : ℝ) *
        belowOneDefect (gramMatrix_isHermitian x) := hsqV

/-- Rank--trace inequality with a direct local spectral-mass premise. -/
theorem rank_trace_two_with_local_spectral_fours
    [Nonempty s]
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    (idx : β → Fin 4 → s)
    (hinj : Function.Injective (fun br : β × Fin 4 => idx br.1 br.2))
    {m : ℝ} (hm : 0 ≤ m)
    (hlocal : ∀ b,
      2 * Real.sqrt m ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix (idx b)))
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (columnMatrix x * (columnMatrix x)ᴴ) -
        (Fintype.card s : ℝ) + 4 * rtrace Q - 4 * (b : ℝ) +
        (Fintype.card β : ℝ) ^ 2 * m / (Fintype.card s : ℝ) ≤
      frobSq (columnMatrix x * (columnMatrix x)ᴴ + Q) := by
  have hlower := card_sq_mul_spectral_mass_le_card_mul_belowOneDefect
    x hunit idx hinj hm hlocal
  rw [← belowOneDefect_columnMatrix_gram x] at hlower
  have hspos : 0 < (Fintype.card s : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hdiv :
      (Fintype.card β : ℝ) ^ 2 * m / (Fintype.card s : ℝ) ≤
        belowOneDefect
          (Matrix.posSemidef_conjTranspose_mul_self (columnMatrix x)).1 := by
    apply (div_le_iff₀ hspos).2
    simpa only [mul_comm] using hlower
  have hrefined := rank_trace_ineq_two_refined_gram (columnMatrix x) hQ hb
  linarith

/-- Width-six four-packing converts a direct local spectral mass `m` into the
coefficient `m/(16*s)`. -/
theorem rank_trace_two_with_binned_spectral_fours
    {S B d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S B)
    (hcover : ∑ b, E.occupancy b = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 6 + 1)
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {m : ℝ} (hm : 0 ≤ m)
    (hlocal : ∀ q : PackedFour E,
      2 * Real.sqrt m ≤ Tail.traceNorm
        ((gramDeviation_isHermitian x).submatrix (packedFourIndex E q)))
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (columnMatrix x * (columnMatrix x)ᴴ) -
        (Fintype.card S : ℝ) + 4 * rtrace Q - 4 * (b : ℝ) +
        m / (16 * (Fintype.card S : ℝ)) *
          max 0 ((Fintype.card S : ℝ) - D / 2 - 3) ^ 2 ≤
      frobSq (columnMatrix x * (columnMatrix x)ᴴ + Q) := by
  have hbase := rank_trace_two_with_local_spectral_fours
    x hunit (packedFourIndex E) (packedFourIndex_injective E)
    hm hlocal hQ hb
  have hcount := fourCount_ge_width_six_target E.occupancy D hbins
  rw [hcover, ← card_packedFour E] at hcount
  let sR : ℝ := Fintype.card S
  let tR : ℝ := Fintype.card (PackedFour E)
  let target : ℝ := max 0 (sR - D / 2 - 3)
  have hspos : 0 < sR := by
    dsimp [sR]
    exact_mod_cast Fintype.card_pos
  have ht0 : 0 ≤ tR := by dsimp [tR]; positivity
  have htarget0 : 0 ≤ target := by
    dsimp [target]
    exact le_max_left _ _
  have hcount' : target / 4 ≤ tR := by
    dsimp [sR, tR, target] at hcount ⊢
    nlinarith
  have hsquare : (target / 4) ^ 2 ≤ tR ^ 2 := by nlinarith
  have hfactor : 0 ≤ m / sR := div_nonneg hm hspos.le
  have hgain : m / (16 * sR) * target ^ 2 ≤ tR ^ 2 * m / sR := by
    calc
      m / (16 * sR) * target ^ 2 =
          (target / 4) ^ 2 * (m / sR) := by
            field_simp [ne_of_gt hspos]
            ring
      _ ≤ tR ^ 2 * (m / sR) :=
        mul_le_mul_of_nonneg_right hsquare hfactor
      _ = tR ^ 2 * m / sR := by ring
  dsimp [sR, tR, target] at hgain
  linarith

/-- Weighted normalized version consumed by the zeta finite-window bridge. -/
theorem rank_trace_two_with_normalized_binned_spectral_fours
    {S B d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S B)
    (hcover : ∑ b, E.occupancy b = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 6 + 1)
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {m : ℝ} (hm : 0 ≤ m)
    (hlocal : ∀ q : PackedFour E,
      2 * Real.sqrt m ≤ Tail.traceNorm
        ((gramDeviation_isHermitian x).submatrix (packedFourIndex E q)))
    (w : S → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    {A : Matrix d d ℂ} (hA : A.IsHermitian)
    {b : ℕ}
    (hb : posIndex
      (hA.sub (weightedProjectorSum_posSemidef x w hw0).isHermitian) ≤ b) :
    2 * rtrace (projectorSum x) - (Fintype.card S : ℝ) +
        4 * rtrace (A - projectorSum x) - 4 * (b : ℝ) +
        m / (16 * (Fintype.card S : ℝ)) *
          max 0 ((Fintype.card S : ℝ) - D / 2 - 3) ^ 2 ≤
      frobSq A := by
  have hb' :
      posIndex (hA.sub (projectorSum_posSemidef x).isHermitian) ≤ b :=
    (posIndex_unit_complement_le_weighted_complement x w hw0 hw1 hA).trans hb
  have hmain := rank_trace_two_with_binned_spectral_fours
    E hcover D hbins x hunit hm hlocal
    (hA.sub (projectorSum_posSemidef x).isHermitian) hb'
  rw [← projectorSum_eq_columnMatrix_mul_conjTranspose x] at hmain
  have hsum : projectorSum x + (A - projectorSum x) = A := by abel
  rw [hsum] at hmain
  exact hmain

end StrictImprovement
end Zeta23

end
