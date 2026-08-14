/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.MixedBlockPinching
import Zeta23.StrictImprovement.WideRepairEndpointInterface
import Zeta23.StrictImprovement.WideRepairBinning
import Zeta23.StrictImprovement.SpectralFourDefect

/-!
# Exact three--four--five residue packing

For occupancy `n = 5*u+r`, select the `u` complete five-blocks and retain the
remainder only for `r=3` or `r=4`.  The selected blocks have dependent orders,
so their global trace-norm contribution uses `MixedBlockPinching`.
-/

noncomputable section

open Matrix Finset Real
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

def wideRepairFiveSlot (r : ℕ) (q : Fin (r / 5)) (k : Fin 5) : Fin r :=
  ⟨5 * q.val + k.val, by
    have hq := q.isLt
    have hk := k.isLt
    omega⟩

def wideRepairResidualSlot (r rem : ℕ) (hrem : r % 5 = rem)
    (k : Fin rem) : Fin r :=
  ⟨5 * (r / 5) + k.val, by
    have hdecomp : r % 5 + 5 * (r / 5) = r := Nat.mod_add_div r 5
    have hk := k.isLt
    omega⟩

abbrev WideRepairFiveBlock
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B) :=
  Σ b : B, Fin (E.occupancy b / 5)

abbrev WideRepairThreeResidue
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B) :=
  Σ b : B, Fin (if E.occupancy b % 5 = 3 then 1 else 0)

abbrev WideRepairFourResidue
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B) :=
  Σ b : B, Fin (if E.occupancy b % 5 = 4 then 1 else 0)

abbrev WideRepairBlock
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B) :=
  WideRepairFiveBlock E ⊕ (WideRepairThreeResidue E ⊕ WideRepairFourResidue E)

def wideRepairThreeResidue_mod
    {S B : Type*} [Fintype B] {E : BinnedEnumeration S B}
    (q : WideRepairThreeResidue E) : E.occupancy q.1 % 5 = 3 := by
  by_contra h
  have hlt := q.2.isLt
  simp [h] at hlt

def wideRepairFourResidue_mod
    {S B : Type*} [Fintype B] {E : BinnedEnumeration S B}
    (q : WideRepairFourResidue E) : E.occupancy q.1 % 5 = 4 := by
  by_contra h
  have hlt := q.2.isLt
  simp [h] at hlt

def wideRepairBlockSize
    {S B : Type*} [Fintype B] {E : BinnedEnumeration S B} :
    WideRepairBlock E → ℕ
  | Sum.inl _ => 5
  | Sum.inr (Sum.inl _) => 3
  | Sum.inr (Sum.inr _) => 4

def wideRepairBlockIndex
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B)
    (q : WideRepairBlock E) : Fin (wideRepairBlockSize q) → S := by
  cases q with
  | inl q =>
      exact fun k => E.entry q.1 (wideRepairFiveSlot (E.occupancy q.1) q.2 k)
  | inr q =>
      cases q with
      | inl q =>
          exact fun k => E.entry q.1
            (wideRepairResidualSlot (E.occupancy q.1) 3
              (wideRepairThreeResidue_mod q) k)
      | inr q =>
          exact fun k => E.entry q.1
            (wideRepairResidualSlot (E.occupancy q.1) 4
              (wideRepairFourResidue_mod q) k)

/-- Every selected mixed block coordinate is globally distinct. -/
theorem wideRepairBlockIndex_injective
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B) :
    Function.Injective
      (fun qk : Σ q : WideRepairBlock E, Fin (wideRepairBlockSize q) =>
        wideRepairBlockIndex E qk.1 qk.2) := by
  rintro ⟨q, k⟩ ⟨q', k'⟩ h
  cases q with
  | inl q =>
      cases q' with
      | inl q' =>
          obtain ⟨b, u⟩ := q
          obtain ⟨b', u'⟩ := q'
          change Fin 5 at k k'
          have hlocal := E.entry_injective h
          have hb : b = b' := hlocal.1
          subst b'
          have hv : 5 * u.val + k.val = 5 * u'.val + k'.val := hlocal.2
          have hu : u = u' := by
            apply Fin.ext
            omega
          subst u'
          have hk : k = k' := by
            apply Fin.ext
            omega
          subst k'
          rfl
      | inr q' =>
          cases q' with
          | inl q' =>
              obtain ⟨b, u⟩ := q
              obtain ⟨b', z⟩ := q'
              change Fin 5 at k
              change Fin 3 at k'
              have hlocal := E.entry_injective h
              have hb : b = b' := hlocal.1
              subst b'
              have hv : 5 * u.val + k.val =
                  5 * (E.occupancy b / 5) + k'.val := hlocal.2
              have hu := u.isLt
              have hk := k.isLt
              omega
          | inr q' =>
              obtain ⟨b, u⟩ := q
              obtain ⟨b', z⟩ := q'
              change Fin 5 at k
              change Fin 4 at k'
              have hlocal := E.entry_injective h
              have hb : b = b' := hlocal.1
              subst b'
              have hv : 5 * u.val + k.val =
                  5 * (E.occupancy b / 5) + k'.val := hlocal.2
              have hu := u.isLt
              have hk := k.isLt
              omega
  | inr q =>
      cases q with
      | inl q =>
          cases q' with
          | inl q' =>
              obtain ⟨b, z⟩ := q
              obtain ⟨b', u⟩ := q'
              change Fin 3 at k
              change Fin 5 at k'
              have hlocal := E.entry_injective h
              have hb : b = b' := hlocal.1
              subst b'
              have hv : 5 * (E.occupancy b / 5) + k.val =
                  5 * u.val + k'.val := hlocal.2
              have hu := u.isLt
              have hk' := k'.isLt
              omega
          | inr q' =>
              cases q' with
              | inl q' =>
                  obtain ⟨b, z⟩ := q
                  obtain ⟨b', z'⟩ := q'
                  change Fin 3 at k k'
                  have hlocal := E.entry_injective h
                  have hb : b = b' := hlocal.1
                  subst b'
                  have hv : 5 * (E.occupancy b / 5) + k.val =
                      5 * (E.occupancy b / 5) + k'.val := hlocal.2
                  have hk : k = k' := Fin.ext (by omega)
                  have hres := wideRepairThreeResidue_mod ⟨b, z⟩
                  have hzlt := z.isLt
                  have hz'lt := z'.isLt
                  simp [hres] at hzlt hz'lt
                  have hz : z = z' := Fin.ext (by omega)
                  subst z'
                  subst k'
                  rfl
              | inr q' =>
                  obtain ⟨b, z⟩ := q
                  obtain ⟨b', z'⟩ := q'
                  change Fin 3 at k
                  change Fin 4 at k'
                  have hlocal := E.entry_injective h
                  have hb : b = b' := hlocal.1
                  subst b'
                  have h3 := wideRepairThreeResidue_mod ⟨b, z⟩
                  have h4 := wideRepairFourResidue_mod ⟨b, z'⟩
                  change E.occupancy b % 5 = 3 at h3
                  change E.occupancy b % 5 = 4 at h4
                  omega
      | inr q =>
          cases q' with
          | inl q' =>
              obtain ⟨b, z⟩ := q
              obtain ⟨b', u⟩ := q'
              change Fin 4 at k
              change Fin 5 at k'
              have hlocal := E.entry_injective h
              have hb : b = b' := hlocal.1
              subst b'
              have hv : 5 * (E.occupancy b / 5) + k.val =
                  5 * u.val + k'.val := hlocal.2
              have hu := u.isLt
              have hk' := k'.isLt
              omega
          | inr q' =>
              cases q' with
              | inl q' =>
                  obtain ⟨b, z⟩ := q
                  obtain ⟨b', z'⟩ := q'
                  change Fin 4 at k
                  change Fin 3 at k'
                  have hlocal := E.entry_injective h
                  have hb : b = b' := hlocal.1
                  subst b'
                  have h4 := wideRepairFourResidue_mod ⟨b, z⟩
                  have h3 := wideRepairThreeResidue_mod ⟨b, z'⟩
                  change E.occupancy b % 5 = 4 at h4
                  change E.occupancy b % 5 = 3 at h3
                  omega
              | inr q' =>
                  obtain ⟨b, z⟩ := q
                  obtain ⟨b', z'⟩ := q'
                  change Fin 4 at k k'
                  have hlocal := E.entry_injective h
                  have hb : b = b' := hlocal.1
                  subst b'
                  have hv : 5 * (E.occupancy b / 5) + k.val =
                      5 * (E.occupancy b / 5) + k'.val := hlocal.2
                  have hk : k = k' := Fin.ext (by omega)
                  have hres := wideRepairFourResidue_mod ⟨b, z⟩
                  have hzlt := z.isLt
                  have hz'lt := z'.isLt
                  simp [hres] at hzlt hz'lt
                  have hz : z = z' := Fin.ext (by omega)
                  subst z'
                  subst k'
                  rfl

def wideRepairBlockReward
    {S B : Type*} [Fintype B] {E : BinnedEnumeration S B} :
    WideRepairBlock E → ℝ
  | Sum.inl _ => wideRepairRewardFive
  | Sum.inr (Sum.inl _) => wideRepairRewardThree
  | Sum.inr (Sum.inr _) => wideRepairRewardFour

def wideRepairBinReward (n : ℕ) : ℝ :=
  (n / 5 : ℕ) * wideRepairRewardFive +
    (if n % 5 = 3 then wideRepairRewardThree else 0) +
    (if n % 5 = 4 then wideRepairRewardFour else 0)

theorem wideRepairBinReward_lower (n : ℕ) :
    wideRepairAlpha * (n : ℝ) - wideRepairDeficit ≤
      wideRepairBinReward n := by
  have hdecomp : n % 5 + 5 * (n / 5) = n := Nat.mod_add_div n 5
  have hdecomp' : (n : ℝ) = ((n % 5 : ℕ) : ℝ) +
      5 * ((n / 5 : ℕ) : ℝ) := by
    exact_mod_cast hdecomp.symm
  have hmod : n % 5 < 5 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 5 <;>
    rw [hdecomp'] <;>
    simp [wideRepairBinReward, h, wideRepairRewardThree,
      wideRepairRewardFour, wideRepairRewardFive, wideRepairAlpha,
      wideRepairDeficit] <;>
    norm_num <;>
    linarith

theorem sum_wideRepairBlockReward_eq
    {S B : Type*} [Fintype B] [DecidableEq B]
    (E : BinnedEnumeration S B) :
    ∑ q : WideRepairBlock E, wideRepairBlockReward q =
      ∑ b, wideRepairBinReward (E.occupancy b) := by
  simp only [wideRepairBinReward, Finset.sum_add_distrib]
  simp [WideRepairBlock, WideRepairFiveBlock, WideRepairThreeResidue,
    WideRepairFourResidue, wideRepairBlockReward]
  rw [Finset.sum_mul, ← Finset.sum_filter, ← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

theorem sum_wideRepairBlockReward_lower
    {S B : Type*} [Fintype B] [DecidableEq B]
    (E : BinnedEnumeration S B) :
    wideRepairAlpha * ((∑ b, E.occupancy b : ℕ) : ℝ) -
        wideRepairDeficit * (Fintype.card B : ℝ) ≤
      ∑ q : WideRepairBlock E, wideRepairBlockReward q := by
  rw [sum_wideRepairBlockReward_eq E]
  calc
    wideRepairAlpha * ((∑ b, E.occupancy b : ℕ) : ℝ) -
          wideRepairDeficit * (Fintype.card B : ℝ) =
        ∑ b : B, (wideRepairAlpha * (E.occupancy b : ℝ) -
          wideRepairDeficit) := by
      push_cast
      simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ ∑ b, wideRepairBinReward (E.occupancy b) :=
      Finset.sum_le_sum fun b _ => wideRepairBinReward_lower (E.occupancy b)

theorem mixed_blocks_traceNorm_lower
    {S B d : Type*} [Fintype S] [DecidableEq S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S B) (x : S → d → ℂ)
    {scale : ℝ}
    (hlocal : ∀ q : WideRepairBlock E,
      2 * (scale * wideRepairBlockReward q) ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix
          (wideRepairBlockIndex E q))) :
    2 * (scale * ∑ q : WideRepairBlock E, wideRepairBlockReward q) ≤
      Tail.traceNorm (gramDeviation_isHermitian x) := by
  calc
    2 * (scale * ∑ q : WideRepairBlock E, wideRepairBlockReward q) =
        ∑ q : WideRepairBlock E, 2 * (scale * wideRepairBlockReward q) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ∑ q : WideRepairBlock E,
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix
          (wideRepairBlockIndex E q)) :=
      Finset.sum_le_sum fun q _ => hlocal q
    _ ≤ Tail.traceNorm (gramDeviation_isHermitian x) :=
      sum_traceNorm_dependent_principal_le
        (wideRepairBlockIndex E) (wideRepairBlockIndex_injective E)
        (gramDeviation_isHermitian x)

/-- The exact residue table plus the width-sixteen bin count give the global
linear spectral-mass reward. -/
theorem mixed_blocks_traceNorm_target_lower
    {S B d : Type*} [Fintype S] [DecidableEq S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S B)
    (hcover : ∑ b, E.occupancy b = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 8 + 1)
    (x : S → d → ℂ) {scale : ℝ} (hscale : 0 ≤ scale)
    (hlocal : ∀ q : WideRepairBlock E,
      2 * (scale * wideRepairBlockReward q) ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix
          (wideRepairBlockIndex E q))) :
    2 * (scale * wideRepairAlpha *
        max 0 ((Fintype.card S : ℝ) - wideRepairPackingLoss * D -
          wideRepairPackingIntercept)) ≤
      Tail.traceNorm (gramDeviation_isHermitian x) := by
  have hrewards := sum_wideRepairBlockReward_lower E
  rw [hcover] at hrewards
  have hbase : wideRepairAlpha *
      ((Fintype.card S : ℝ) - wideRepairPackingLoss * D -
        wideRepairPackingIntercept) ≤
      ∑ q : WideRepairBlock E, wideRepairBlockReward q := by
    have hcard := hbins
    norm_num [wideRepairAlpha, wideRepairRewardFive, wideRepairDeficit,
      wideRepairRewardThree, wideRepairPackingLoss,
      wideRepairPackingIntercept] at hrewards ⊢
    nlinarith
  have hrewards0 : 0 ≤
      ∑ q : WideRepairBlock E, wideRepairBlockReward q := by
    apply Finset.sum_nonneg
    intro q _
    cases q with
    | inl _ => exact wideRepairRewardFive_nonneg
    | inr q =>
        cases q with
        | inl _ => exact wideRepairRewardThree_nonneg
        | inr _ => exact wideRepairRewardFour_nonneg
  have hmax : wideRepairAlpha *
      max 0 ((Fintype.card S : ℝ) - wideRepairPackingLoss * D -
        wideRepairPackingIntercept) ≤
      ∑ q : WideRepairBlock E, wideRepairBlockReward q := by
    by_cases harg : 0 ≤
        (Fintype.card S : ℝ) - wideRepairPackingLoss * D -
          wideRepairPackingIntercept
    · rw [max_eq_right harg]
      exact hbase
    · have harg' :
          (Fintype.card S : ℝ) - wideRepairPackingLoss * D -
            wideRepairPackingIntercept ≤ 0 :=
        le_of_not_ge harg
      rw [max_eq_left harg']
      simpa using hrewards0
  have hscaled := mul_le_mul_of_nonneg_left hmax hscale
  have htrace := mixed_blocks_traceNorm_lower E x hlocal
  calc
    2 * (scale * wideRepairAlpha *
        max 0 ((Fintype.card S : ℝ) - wideRepairPackingLoss * D -
          wideRepairPackingIntercept))
        ≤ 2 * (scale * ∑ q : WideRepairBlock E,
          wideRepairBlockReward q) := by
      nlinarith
    _ ≤ Tail.traceNorm (gramDeviation_isHermitian x) := htrace

/-- A trace-norm reward `R` for a unit Gram family yields the squared
below-one defect `R^2/card(S)`. -/
theorem reward_sq_le_card_mul_belowOneDefect_of_traceNorm
    {S d : Type*} [Fintype S] [DecidableEq S]
    [Fintype d] [DecidableEq d]
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {R : ℝ} (hR : 0 ≤ R)
    (htrace : 2 * R ≤ Tail.traceNorm (gramDeviation_isHermitian x)) :
    R ^ 2 ≤ (Fintype.card S : ℝ) *
      belowOneDefect (gramMatrix_isHermitian x) := by
  let V : ℝ := ∑ k, linearUnitDefect
    ((gramMatrix_isHermitian x).eigenvalues k)
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun k _ => linearUnitDefect_nonneg _
  have htraceUpper := traceNorm_gramDeviation_le_sum_abs_shift x
  have habs := sum_abs_gram_shift_eq_two_linearDefect x hunit
  have hRV : R ≤ V := by
    dsimp [V]
    linarith
  have hCS : V ^ 2 ≤ (Fintype.card S : ℝ) *
      ∑ k, (linearUnitDefect
        ((gramMatrix_isHermitian x).eigenvalues k)) ^ 2 := by
    dsimp [V]
    simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset S))
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
  rw [← hdefect] at hCS
  have hsq : R ^ 2 ≤ V ^ 2 := by nlinarith
  exact hsq.trans hCS

/-- Finite-dimensional rank--trace theorem carrying the saturated coefficient
`scale^2 * wideRepairAlpha^2`. -/
theorem rank_trace_two_with_mixed_blocks
    {S B d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S B)
    (hcover : ∑ b, E.occupancy b = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 8 + 1)
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hlocal : ∀ q : WideRepairBlock E,
      2 * (scale * wideRepairBlockReward q) ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix
          (wideRepairBlockIndex E q)))
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (columnMatrix x * (columnMatrix x)ᴴ) -
        (Fintype.card S : ℝ) + 4 * rtrace Q - 4 * (b : ℝ) +
        scale ^ 2 * wideRepairAlpha ^ 2 / (Fintype.card S : ℝ) *
          max 0 ((Fintype.card S : ℝ) -
            wideRepairPackingLoss * D - wideRepairPackingIntercept) ^ 2 ≤
      frobSq (columnMatrix x * (columnMatrix x)ᴴ + Q) := by
  let target : ℝ := max 0 ((Fintype.card S : ℝ) -
    wideRepairPackingLoss * D - wideRepairPackingIntercept)
  let R : ℝ := scale * wideRepairAlpha * target
  have hR0 : 0 ≤ R := by
    dsimp [R, target]
    positivity
  have htrace : 2 * R ≤ Tail.traceNorm (gramDeviation_isHermitian x) := by
    dsimp [R, target]
    exact mixed_blocks_traceNorm_target_lower E hcover D hbins x hscale hlocal
  have hlower := reward_sq_le_card_mul_belowOneDefect_of_traceNorm
    x hunit hR0 htrace
  rw [← belowOneDefect_columnMatrix_gram x] at hlower
  have hspos : 0 < (Fintype.card S : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hdiv : R ^ 2 / (Fintype.card S : ℝ) ≤
      belowOneDefect
        (Matrix.posSemidef_conjTranspose_mul_self (columnMatrix x)).1 := by
    apply (div_le_iff₀ hspos).2
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hlower
  have hrefined := rank_trace_ineq_two_refined_gram (columnMatrix x) hQ hb
  have hRform : R ^ 2 / (Fintype.card S : ℝ) =
      scale ^ 2 * wideRepairAlpha ^ 2 / (Fintype.card S : ℝ) *
        target ^ 2 := by
    dsimp [R]
    field_simp [ne_of_gt hspos]
    ring
  rw [hRform] at hdiv
  dsimp [target] at hdiv
  linarith

/-- Weighted normalized wrapper consumed by the zero-side seam. -/
theorem rank_trace_two_with_normalized_mixed_blocks
    {S B d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S B)
    (hcover : ∑ b, E.occupancy b = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 8 + 1)
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hlocal : ∀ q : WideRepairBlock E,
      2 * (scale * wideRepairBlockReward q) ≤
        Tail.traceNorm ((gramDeviation_isHermitian x).submatrix
          (wideRepairBlockIndex E q)))
    (w : S → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    {A : Matrix d d ℂ} (hA : A.IsHermitian)
    {b : ℕ}
    (hb : posIndex
      (hA.sub (weightedProjectorSum_posSemidef x w hw0).isHermitian) ≤ b) :
    2 * rtrace (projectorSum x) - (Fintype.card S : ℝ) +
        4 * rtrace (A - projectorSum x) - 4 * (b : ℝ) +
        scale ^ 2 * wideRepairAlpha ^ 2 / (Fintype.card S : ℝ) *
          max 0 ((Fintype.card S : ℝ) -
            wideRepairPackingLoss * D - wideRepairPackingIntercept) ^ 2 ≤
      frobSq A := by
  have hb' : posIndex (hA.sub (projectorSum_posSemidef x).isHermitian) ≤ b :=
    (posIndex_unit_complement_le_weighted_complement x w hw0 hw1 hA).trans hb
  have hmain := rank_trace_two_with_mixed_blocks E hcover D hbins x hunit
    hscale hlocal (hA.sub (projectorSum_posSemidef x).isHermitian) hb'
  rw [← projectorSum_eq_columnMatrix_mul_conjTranspose x] at hmain
  have hsum : projectorSum x + (A - projectorSum x) = A := by abel
  rw [hsum] at hmain
  exact hmain

end StrictImprovement
end Zeta23

end
