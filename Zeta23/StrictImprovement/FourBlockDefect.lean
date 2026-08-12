/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.FiniteFullNormalization

/-!
# Four-point pinching and the width-six defect coefficient

This module specializes the reviewed larger-block calculation to `q = 4`.
Each packed block has six unordered Gram edges.  If each of its four triples
has energy at least `delta`, double counting gives total edge energy at least
`2 * delta`; the sharp trace-zero inequality then contributes the extra factor
two in the squared defect.  Four-at-a-time packing with at most three leftovers
per width-six bin yields the exact coefficient

`delta / (8*s) * max 0 (s - D/2 - 3)^2`.

The statements are finite-dimensional and contain no zeta or asymptotic input.
This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

/-! ## The sharp trace-zero inequality in dimension four -/

def scalarPositivePart (x : ℝ) : ℝ := max x 0
def scalarNegativePart (x : ℝ) : ℝ := max (-x) 0

lemma scalar_part_spec (x : ℝ) :
    0 ≤ scalarPositivePart x ∧ 0 ≤ scalarNegativePart x ∧
      scalarPositivePart x * scalarNegativePart x = 0 ∧
      x = scalarPositivePart x - scalarNegativePart x ∧
      |x| = scalarPositivePart x + scalarNegativePart x := by
  by_cases hx : 0 ≤ x
  · have hnx : -x ≤ 0 := neg_nonpos.mpr hx
    simp [scalarPositivePart, scalarNegativePart, max_eq_left hx,
      max_eq_right hnx, abs_of_nonneg hx]
    exact hx
  · have hx' : x < 0 := lt_of_not_ge hx
    have hxle : x ≤ 0 := hx'.le
    have hnx : 0 ≤ -x := neg_nonneg.mpr hxle
    simp [scalarPositivePart, scalarNegativePart, max_eq_right hxle,
      max_eq_left hnx, abs_of_neg hx']
    exact hxle

lemma four_trace_zero_l1_sq
    (a b c d : ℝ) (hsum : a + b + c + d = 0) :
    2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤
      (|a| + |b| + |c| + |d|) ^ 2 := by
  let pa := scalarPositivePart a
  let pb := scalarPositivePart b
  let pc := scalarPositivePart c
  let pd := scalarPositivePart d
  let na := scalarNegativePart a
  let nb := scalarNegativePart b
  let nc := scalarNegativePart c
  let nd := scalarNegativePart d
  have ha := scalar_part_spec a
  have hb := scalar_part_spec b
  have hc := scalar_part_spec c
  have hd := scalar_part_spec d
  have hP : pa + pb + pc + pd = na + nb + nc + nd := by
    dsimp [pa, pb, pc, pd, na, nb, nc, nd]
    nlinarith [ha.2.2.2.1, hb.2.2.2.1, hc.2.2.2.1, hd.2.2.2.1]
  have hPsq : pa ^ 2 + pb ^ 2 + pc ^ 2 + pd ^ 2 ≤
      (pa + pb + pc + pd) ^ 2 := by
    have hab := mul_nonneg ha.1 hb.1
    have hac := mul_nonneg ha.1 hc.1
    have had := mul_nonneg ha.1 hd.1
    have hbc := mul_nonneg hb.1 hc.1
    have hbd := mul_nonneg hb.1 hd.1
    have hcd := mul_nonneg hc.1 hd.1
    dsimp [pa, pb, pc, pd] at hab hac had hbc hbd hcd ⊢
    nlinarith
  have hNsq : na ^ 2 + nb ^ 2 + nc ^ 2 + nd ^ 2 ≤
      (na + nb + nc + nd) ^ 2 := by
    have hab := mul_nonneg ha.2.1 hb.2.1
    have hac := mul_nonneg ha.2.1 hc.2.1
    have had := mul_nonneg ha.2.1 hd.2.1
    have hbc := mul_nonneg hb.2.1 hc.2.1
    have hbd := mul_nonneg hb.2.1 hd.2.1
    have hcd := mul_nonneg hc.2.1 hd.2.1
    dsimp [na, nb, nc, nd] at hab hac had hbc hbd hcd ⊢
    nlinarith
  dsimp [pa, pb, pc, pd, na, nb, nc, nd] at hP hPsq hNsq ⊢
  rw [ha.2.2.2.2, hb.2.2.2.2, hc.2.2.2.2, hd.2.2.2.2]
  have haSq : a ^ 2 =
      scalarPositivePart a ^ 2 + scalarNegativePart a ^ 2 := by
    calc
      a ^ 2 = (scalarPositivePart a - scalarNegativePart a) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) ha.2.2.2.1
      _ = scalarPositivePart a ^ 2 + scalarNegativePart a ^ 2 := by
        nlinarith [ha.2.2.1]
  have hbSq : b ^ 2 =
      scalarPositivePart b ^ 2 + scalarNegativePart b ^ 2 := by
    calc
      b ^ 2 = (scalarPositivePart b - scalarNegativePart b) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hb.2.2.2.1
      _ = scalarPositivePart b ^ 2 + scalarNegativePart b ^ 2 := by
        nlinarith [hb.2.2.1]
  have hcSq : c ^ 2 =
      scalarPositivePart c ^ 2 + scalarNegativePart c ^ 2 := by
    calc
      c ^ 2 = (scalarPositivePart c - scalarNegativePart c) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hc.2.2.2.1
      _ = scalarPositivePart c ^ 2 + scalarNegativePart c ^ 2 := by
        nlinarith [hc.2.2.1]
  have hdSq : d ^ 2 =
      scalarPositivePart d ^ 2 + scalarNegativePart d ^ 2 := by
    calc
      d ^ 2 = (scalarPositivePart d - scalarNegativePart d) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hd.2.2.2.1
      _ = scalarPositivePart d ^ 2 + scalarNegativePart d ^ 2 := by
        nlinarith [hd.2.2.1]
  rw [haSq, hbSq, hcSq, hdSq]
  nlinarith

theorem two_frobSq_le_traceNorm_sq_fin4
    {B : Matrix (Fin 4) (Fin 4) ℂ}
    (hB : B.IsHermitian) (htr : rtrace B = 0) :
    2 * frobSq B ≤ (Tail.traceNorm hB) ^ 2 := by
  have hsum :
      hB.eigenvalues 0 + hB.eigenvalues 1 + hB.eigenvalues 2 +
          hB.eigenvalues 3 = 0 := by
    rw [rtrace_eq_sum_eigenvalues hB] at htr
    simpa [Fin.sum_univ_succ, add_assoc] using htr
  have h := four_trace_zero_l1_sq
    (hB.eigenvalues 0) (hB.eigenvalues 1)
    (hB.eigenvalues 2) (hB.eigenvalues 3) hsum
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues hB, Tail.traceNorm]
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem two_mul_sqrt_two_delta_le_traceNorm_fin4
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {B : Matrix (Fin 4) (Fin 4) ℂ}
    (hB : B.IsHermitian) (htr : rtrace B = 0)
    (henergy : 4 * delta ≤ frobSq B) :
    2 * Real.sqrt (2 * delta) ≤ Tail.traceNorm hB := by
  have hmatrix := two_frobSq_le_traceNorm_sq_fin4 hB htr
  have h2delta : 0 ≤ 2 * delta := mul_nonneg (by norm_num) hdelta
  have hsqrtSq : (Real.sqrt (2 * delta)) ^ 2 = 2 * delta :=
    Real.sq_sqrt h2delta
  have hsqrtNonneg := Real.sqrt_nonneg (2 * delta)
  have htraceNonneg := Tail.traceNorm_nonneg hB
  nlinarith

/-! ## Four-point Gram energy -/

variable {d s β : Type*} [Fintype d] [DecidableEq d]
variable [Fintype s] [DecidableEq s]
variable [Fintype β] [DecidableEq β]

private lemma frobSq_eq_sum_norm_sq_four
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold frobSq
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum, Complex.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

lemma frobSq_fin4_of_diag_zero
    {B : Matrix (Fin 4) (Fin 4) ℂ} (hB : B.IsHermitian)
    (hdiag : ∀ i, B i i = 0) :
    frobSq B = 2 *
      (‖B 0 1‖ ^ 2 + ‖B 0 2‖ ^ 2 + ‖B 0 3‖ ^ 2 +
        ‖B 1 2‖ ^ 2 + ‖B 1 3‖ ^ 2 + ‖B 2 3‖ ^ 2) := by
  have hsymm : ∀ i j, ‖B j i‖ = ‖B i j‖ := by
    intro i j
    calc
      ‖B j i‖ = ‖star (B j i)‖ := (norm_star _).symm
      _ = ‖B i j‖ := by rw [hB.apply]
  have h10 := hsymm 0 1
  have h20 := hsymm 0 2
  have h30 := hsymm 0 3
  have h21 := hsymm 1 2
  have h31 := hsymm 1 3
  have h32 := hsymm 2 3
  rw [frobSq_eq_sum_norm_sq_four]
  simp [Fin.sum_univ_succ, hdiag, h10, h20, h30, h21, h31, h32]
  ring

def fourCorrelationEnergy (x : s → d → ℂ)
    (idx : β → Fin 4 → s) (b : β) : ℝ :=
  ‖gramMatrix x (idx b 0) (idx b 1)‖ ^ 2 +
    ‖gramMatrix x (idx b 0) (idx b 2)‖ ^ 2 +
    ‖gramMatrix x (idx b 0) (idx b 3)‖ ^ 2 +
    ‖gramMatrix x (idx b 1) (idx b 2)‖ ^ 2 +
    ‖gramMatrix x (idx b 1) (idx b 3)‖ ^ 2 +
    ‖gramMatrix x (idx b 2) (idx b 3)‖ ^ 2

lemma frobSq_gramDeviation_four
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    (idx : β → Fin 4 → s)
    (hinj : Function.Injective (fun br : β × Fin 4 => idx br.1 br.2))
    (b : β) :
    frobSq ((gramDeviation x).submatrix (idx b) (idx b)) =
      2 * fourCorrelationEnergy x idx b := by
  have hlocalNe : ∀ {r t : Fin 4}, r ≠ t → idx b r ≠ idx b t := by
    intro r t hrt heq
    have hp : (b, r) = (b, t) := hinj heq
    exact hrt (congrArg Prod.snd hp)
  have hdiag : ∀ r,
      (gramDeviation x).submatrix (idx b) (idx b) r r = 0 := fun r =>
    gramDeviation_diag_zero x hunit (idx b r)
  rw [frobSq_fin4_of_diag_zero
    ((gramDeviation_isHermitian x).submatrix (idx b)) hdiag]
  rw [gramDeviation_offdiag x (hlocalNe (by norm_num : (0 : Fin 4) ≠ 1)),
    gramDeviation_offdiag x (hlocalNe (by norm_num : (0 : Fin 4) ≠ 2)),
    gramDeviation_offdiag x (hlocalNe (by norm_num : (0 : Fin 4) ≠ 3)),
    gramDeviation_offdiag x (hlocalNe (by norm_num : (1 : Fin 4) ≠ 2)),
    gramDeviation_offdiag x (hlocalNe (by norm_num : (1 : Fin 4) ≠ 3)),
    gramDeviation_offdiag x (hlocalNe (by norm_num : (2 : Fin 4) ≠ 3))]
  rfl

theorem gram_fours_traceNorm_lower
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    (idx : β → Fin 4 → s)
    (hinj : Function.Injective (fun br : β × Fin 4 => idx br.1 br.2))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ b, 2 * delta ≤ fourCorrelationEnergy x idx b) :
    2 * (Fintype.card β : ℝ) * Real.sqrt (2 * delta) ≤
      Tail.traceNorm (gramDeviation_isHermitian x) := by
  have hlocalTrace : ∀ b, 2 * Real.sqrt (2 * delta) ≤
      Tail.traceNorm ((gramDeviation_isHermitian x).submatrix (idx b)) := by
    intro b
    apply two_mul_sqrt_two_delta_le_traceNorm_fin4 hdelta
      ((gramDeviation_isHermitian x).submatrix (idx b))
    · unfold rtrace Matrix.trace
      simp [gramDeviation_diag_zero x hunit]
    · rw [frobSq_gramDeviation_four x hunit idx hinj b]
      nlinarith [hlocal b]
  calc
    2 * (Fintype.card β : ℝ) * Real.sqrt (2 * delta) =
        ∑ b : β, 2 * Real.sqrt (2 * delta) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
    _ ≤ ∑ b, Tail.traceNorm
          ((gramDeviation_isHermitian x).submatrix (idx b)) :=
      Finset.sum_le_sum fun b _ => hlocalTrace b
    _ ≤ Tail.traceNorm (gramDeviation_isHermitian x) :=
      sum_traceNorm_principal_le idx hinj (gramDeviation_isHermitian x)

theorem two_card_sq_mul_delta_le_card_mul_belowOneDefect
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    (idx : β → Fin 4 → s)
    (hinj : Function.Injective (fun br : β × Fin 4 => idx br.1 br.2))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ b, 2 * delta ≤ fourCorrelationEnergy x idx b) :
    2 * (Fintype.card β : ℝ) ^ 2 * delta ≤
      (Fintype.card s : ℝ) * belowOneDefect (gramMatrix_isHermitian x) := by
  let V : ℝ := ∑ k, linearUnitDefect
    ((gramMatrix_isHermitian x).eigenvalues k)
  have hVNonneg : 0 ≤ V := Finset.sum_nonneg fun k _ =>
    linearUnitDefect_nonneg _
  have hlocalTrace := gram_fours_traceNorm_lower
    x hunit idx hinj hdelta hlocal
  have htraceUpper := traceNorm_gramDeviation_le_sum_abs_shift x
  have habs := sum_abs_gram_shift_eq_two_linearDefect x hunit
  have hTV : (Fintype.card β : ℝ) * Real.sqrt (2 * delta) ≤ V := by
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
  have h2delta : 0 ≤ 2 * delta := mul_nonneg (by norm_num) hdelta
  have hsqrtSq : (Real.sqrt (2 * delta)) ^ 2 = 2 * delta :=
    Real.sq_sqrt h2delta
  have hfactor :
      0 ≤ (V - (Fintype.card β : ℝ) * Real.sqrt (2 * delta)) *
        (V + (Fintype.card β : ℝ) * Real.sqrt (2 * delta)) :=
    mul_nonneg (sub_nonneg.mpr hTV)
      (add_nonneg hVNonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))
  have hsqTV :
      ((Fintype.card β : ℝ) * Real.sqrt (2 * delta)) ^ 2 ≤ V ^ 2 := by
    nlinarith
  calc
    2 * (Fintype.card β : ℝ) ^ 2 * delta =
        ((Fintype.card β : ℝ) * Real.sqrt (2 * delta)) ^ 2 := by
          rw [mul_pow, hsqrtSq]
          ring
    _ ≤ V ^ 2 := hsqTV
    _ ≤ (Fintype.card s : ℝ) *
        belowOneDefect (gramMatrix_isHermitian x) := hsqV

theorem rank_trace_two_with_local_gram_fours
    [Nonempty s]
    (x : s → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    (idx : β → Fin 4 → s)
    (hinj : Function.Injective (fun br : β × Fin 4 => idx br.1 br.2))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ b, 2 * delta ≤ fourCorrelationEnergy x idx b)
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (columnMatrix x * (columnMatrix x)ᴴ) -
        (Fintype.card s : ℝ) + 4 * rtrace Q - 4 * (b : ℝ) +
        2 * (Fintype.card β : ℝ) ^ 2 * delta /
          (Fintype.card s : ℝ) ≤
      frobSq (columnMatrix x * (columnMatrix x)ᴴ + Q) := by
  have hlower := two_card_sq_mul_delta_le_card_mul_belowOneDefect
    x hunit idx hinj hdelta hlocal
  rw [← belowOneDefect_columnMatrix_gram x] at hlower
  have hspos : 0 < (Fintype.card s : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hdiv :
      2 * (Fintype.card β : ℝ) ^ 2 * delta / (Fintype.card s : ℝ) ≤
        belowOneDefect
          (Matrix.posSemidef_conjTranspose_mul_self (columnMatrix x)).1 := by
    apply (div_le_iff₀ hspos).2
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hlower
  have hrefined := rank_trace_ineq_two_refined_gram (columnMatrix x) hQ hb
  linarith

/-! ## Four-at-a-time bin packing -/

lemma le_four_mul_div_four_add_three (r : ℕ) :
    r ≤ 4 * (r / 4) + 3 := by omega

theorem sum_le_four_mul_fourCount_add_three_card
    {B : Type*} [Fintype B] [DecidableEq B] (occupancy : B → ℕ) :
    ∑ b, occupancy b ≤
      4 * (∑ b, occupancy b / 4) + 3 * Fintype.card B := by
  calc
    ∑ b, occupancy b ≤ ∑ b, (4 * (occupancy b / 4) + 3) :=
      Finset.sum_le_sum fun b _ => le_four_mul_div_four_add_three (occupancy b)
    _ = 4 * (∑ b, occupancy b / 4) + 3 * Fintype.card B := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem fourCount_ge_width_six_target
    {B : Type*} [Fintype B] [DecidableEq B]
    (occupancy : B → ℕ) (D : ℝ)
    (hbins : (Fintype.card B : ℝ) ≤ D / 6 + 1) :
    (1 : ℝ) / 4 *
        max 0 (((∑ b, occupancy b : ℕ) : ℝ) - D / 2 - 3) ≤
      ((∑ b, occupancy b / 4 : ℕ) : ℝ) := by
  have hrawNat := sum_le_four_mul_fourCount_add_three_card occupancy
  have hraw : ((∑ b, occupancy b : ℕ) : ℝ) ≤
      4 * ((∑ b, occupancy b / 4 : ℕ) : ℝ) +
        3 * (Fintype.card B : ℝ) := by exact_mod_cast hrawNat
  have htarget :
      ((∑ b, occupancy b : ℕ) : ℝ) - D / 2 - 3 ≤
        4 * ((∑ b, occupancy b / 4 : ℕ) : ℝ) := by
    nlinarith
  have hcount0 : 0 ≤ ((∑ b, occupancy b / 4 : ℕ) : ℝ) := by positivity
  have hmax := max_le (by nlinarith :
      0 ≤ 4 * ((∑ b, occupancy b / 4 : ℕ) : ℝ)) htarget
  nlinarith

def fourSlot (r : ℕ) (q : Fin (r / 4)) (k : Fin 4) : Fin r :=
  ⟨4 * q.val + k.val, by
    have hq := q.isLt
    have hk := k.isLt
    omega⟩

abbrev PackedFour
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B) :=
  Σ b : B, Fin (E.occupancy b / 4)

def packedFourIndex
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B)
    (q : PackedFour E) (k : Fin 4) : S :=
  E.entry q.1 (fourSlot (E.occupancy q.1) q.2 k)

theorem packedFourIndex_injective
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B) :
    Function.Injective
      (fun qk : PackedFour E × Fin 4 => packedFourIndex E qk.1 qk.2) := by
  rintro ⟨⟨b, q⟩, k⟩ ⟨⟨b', q'⟩, k'⟩ h
  have hlocal := E.entry_injective h
  have hb : b = b' := hlocal.1
  subst b'
  have hv : 4 * q.val + k.val = 4 * q'.val + k'.val := hlocal.2
  have hqval : q.val = q'.val := by
    have hk := k.isLt
    have hk' := k'.isLt
    omega
  have hkval : k.val = k'.val := by omega
  have hq : q = q' := Fin.ext hqval
  have hk : k = k' := Fin.ext hkval
  subst q'
  subst k'
  rfl

@[simp] theorem card_packedFour
    {S B : Type*} [Fintype B] [DecidableEq B]
    (E : BinnedEnumeration S B) :
    Fintype.card (PackedFour E) = ∑ b, E.occupancy b / 4 := by
  simp [PackedFour]

theorem rank_trace_two_with_binned_gram_fours
    {S B d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S B)
    (hcover : ∑ b, E.occupancy b = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 6 + 1)
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ q : PackedFour E,
      2 * delta ≤ fourCorrelationEnergy x (packedFourIndex E) q)
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (columnMatrix x * (columnMatrix x)ᴴ) -
        (Fintype.card S : ℝ) + 4 * rtrace Q - 4 * (b : ℝ) +
        delta / (8 * (Fintype.card S : ℝ)) *
          max 0 ((Fintype.card S : ℝ) - D / 2 - 3) ^ 2 ≤
      frobSq (columnMatrix x * (columnMatrix x)ᴴ + Q) := by
  have hbase := rank_trace_two_with_local_gram_fours
    x hunit (packedFourIndex E) (packedFourIndex_injective E)
    hdelta hlocal hQ hb
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
  have hfactor : 0 ≤ 2 * delta / sR := by positivity
  have hgain : delta / (8 * sR) * target ^ 2 ≤
      2 * tR ^ 2 * delta / sR := by
    calc
      delta / (8 * sR) * target ^ 2 =
          (target / 4) ^ 2 * (2 * delta / sR) := by
            field_simp [ne_of_gt hspos]
            ring
      _ ≤ tR ^ 2 * (2 * delta / sR) :=
        mul_le_mul_of_nonneg_right hsquare hfactor
      _ = 2 * tR ^ 2 * delta / sR := by ring
  dsimp [sR, tR, target] at hgain
  linarith

theorem rank_trace_two_with_normalized_binned_fours
    {S B d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S B)
    (hcover : ∑ b, E.occupancy b = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 6 + 1)
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ q : PackedFour E,
      2 * delta ≤ fourCorrelationEnergy x (packedFourIndex E) q)
    (w : S → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    {A : Matrix d d ℂ} (hA : A.IsHermitian)
    {b : ℕ}
    (hb : posIndex
      (hA.sub (weightedProjectorSum_posSemidef x w hw0).isHermitian) ≤ b) :
    2 * rtrace (projectorSum x) - (Fintype.card S : ℝ) +
        4 * rtrace (A - projectorSum x) - 4 * (b : ℝ) +
        delta / (8 * (Fintype.card S : ℝ)) *
          max 0 ((Fintype.card S : ℝ) - D / 2 - 3) ^ 2 ≤
      frobSq A := by
  have hb' :
      posIndex (hA.sub (projectorSum_posSemidef x).isHermitian) ≤ b :=
    (posIndex_unit_complement_le_weighted_complement x w hw0 hw1 hA).trans hb
  have hmain := rank_trace_two_with_binned_gram_fours
    E hcover D hbins x hunit hdelta hlocal
    (hA.sub (projectorSum_posSemidef x).isHermitian) hb'
  rw [← projectorSum_eq_columnMatrix_mul_conjTranspose x] at hmain
  have hsum : projectorSum x + (A - projectorSum x) = A := by abel
  rw [hsum] at hmain
  exact hmain

end StrictImprovement
end Zeta23

end
