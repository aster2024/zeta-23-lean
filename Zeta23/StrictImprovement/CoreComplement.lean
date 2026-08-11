/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.FiniteFullNormalization
import Zeta23.ZeroSide.Mult

/-!
# Positive-index bound after selecting a core on-line subfamily

The frozen zero-side block splits into an on-line positive part and an
off-line Hermitian part of positive index at most `p`.  This module proves,
for an arbitrary subset of the on-line labels, that subtracting its positive
rank-one contribution leaves positive index at most

`card (onLine \ selected) + p`.

The later zeta caller will take `selected` to be the core simple zeros.  Then
the first cardinal is exactly the number of excluded simple labels plus the
number of multiple on-line labels.  No analytic estimate is used here.

This is a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open RHLinalg
open ZeroSide

variable {i d : Type*} [Fintype i] [DecidableEq i]
variable [Fintype d] [DecidableEq d]

namespace ZeroBlockData

variable (D : ZeroBlockData i d)

/-- The unscaled positive contribution of a selected on-line subfamily. -/
def selectedOnPart (S : Finset i) : Matrix d d ℂ :=
  ∑ z ∈ S, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

/-- The selected contribution in hat units. -/
def selectedHatPart (S : Finset i) (c : ℝ) : Matrix d d ℂ :=
  (((c⁻¹ : ℝ) : ℂ) • D.selectedOnPart S)

lemma selectedOnPart_posSemidef
    (S : Finset i) (hS : S ⊆ D.onLine) :
    (D.selectedOnPart S).PosSemidef := by
  unfold selectedOnPart
  refine posSemidef_sum _ fun z hz => ?_
  exact posSemidef_smul_vecMulVec
    (D.star_v_of_onLine ((D.mem_onLine).mp (hS hz)))
    (Nat.cast_nonneg (D.m z))

lemma rank_selectedOnPart_le (S : Finset i) :
    (D.selectedOnPart S).rank ≤ #S := by
  unfold selectedOnPart
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ =>
    rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

lemma selectedHatPart_posSemidef
    (S : Finset i) (hS : S ⊆ D.onLine) {c : ℝ} (hc : 0 < c) :
    (D.selectedHatPart S c).PosSemidef := by
  unfold selectedHatPart
  exact (D.selectedOnPart_posSemidef S hS).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))

lemma rank_selectedHatPart_le
    (S : Finset i) {c : ℝ} (hc : 0 < c) :
    (D.selectedHatPart S c).rank ≤ #S := by
  unfold selectedHatPart
  rw [rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero hc.ne'))]
  exact D.rank_selectedOnPart_le S

lemma S₁_subset_onLine : D.S₁ ⊆ D.onLine := by
  intro z hz
  simp only [ZeroSide.ZeroBlockData.S₁, ZeroSide.ZeroBlockData.onLine,
    Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  exact hz.1

/-- For a selected simple on-line family, the selected hat contribution is
the sum of the rank-one projectors of the frozen normalized vectors `vhat`. -/
lemma selectedHatPart_eq_sum_vhat
    (S : Finset i) (hS₁ : S ⊆ D.S₁) {c : ℝ} (hc : 0 < c) :
    D.selectedHatPart S c =
      ∑ z : S, rankOneProjector
        (D.vhat c ⟨z, D.S₁_subset_onLine (hS₁ z.2)⟩) := by
  ext a b
  simp only [selectedHatPart, selectedOnPart, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, Finset.mul_sum, rankOneProjector,
    Matrix.vecMulVec_apply]
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz₁ : z ∈ D.S₁ := hS₁ hz
  have hzon : z ∈ D.onLine := D.S₁_subset_onLine hz₁
  have hm : D.m z = 1 := by
    have hz₁' := hz₁
    simp only [ZeroSide.ZeroBlockData.S₁, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz₁'
    exact hz₁'.2
  have hreal : starRingEnd ℂ (D.v z b) = D.v z b := by
    have := congrFun (D.star_v_of_onLine ((D.mem_onLine).mp hzon)) b
    rwa [Pi.star_apply, RCLike.star_def] at this
  simp only [ZeroSide.ZeroBlockData.vhat, Pi.star_apply, RCLike.star_def,
    map_div₀, hreal, Complex.conj_ofReal, hm, Nat.cast_one, one_mul]
  have hsq : ((Real.sqrt c : ℂ)) ^ 2 = (c : ℂ) := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  have hc0 : (Real.sqrt c : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [div_mul_div_comm, ← sq, hsq]
  push_cast
  field_simp

/-- If the selected family consists only of simple on-line labels, its
on-line complement is the disjoint union of the excluded simple labels and
all multiple on-line labels. -/
lemma onLine_sdiff_selected_eq
    (S : Finset i) (hS₁ : S ⊆ D.S₁) :
    D.onLine \ S = (D.S₁ \ S) ∪ D.S₂ := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_union]
  rw [D.onLine_eq_S₁_union_S₂, Finset.mem_union]
  constructor
  · rintro ⟨hz₁ | hz₂, hzS⟩
    · exact Or.inl ⟨hz₁, hzS⟩
    · exact Or.inr hz₂
  · rintro (⟨hz₁, hzS⟩ | hz₂)
    · exact ⟨Or.inl hz₁, hzS⟩
    · refine ⟨Or.inr hz₂, ?_⟩
      intro hzS
      have hz₁ : z ∈ D.S₁ := hS₁ hzS
      exact Finset.disjoint_left.mp D.disjoint_S₁_S₂ hz₁ hz₂

lemma card_onLine_sdiff_selected
    (S : Finset i) (hS₁ : S ⊆ D.S₁) :
    #(D.onLine \ S) = #(D.S₁ \ S) + D.s₂ := by
  rw [D.onLine_sdiff_selected_eq S hS₁]
  have hdisj : Disjoint (D.S₁ \ S) D.S₂ := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    exact Finset.disjoint_left.mp D.disjoint_S₁_S₂
      (Finset.sdiff_subset hz₁) hz₂
  rw [Finset.card_union_of_disjoint hdisj]
  rfl

/-- Split the full on-line part into a selected family and its complement. -/
lemma onPart_eq_selected_add_complement
    (S : Finset i) (hS : S ⊆ D.onLine) :
    D.onPart = D.selectedOnPart S + D.selectedOnPart (D.onLine \ S) := by
  unfold ZeroBlockData.onPart selectedOnPart
  have hdiff := Finset.sum_sdiff hS
    (f := fun z => (D.m z : ℂ) • vecMulVec (D.v z) (D.v z))
  rw [hdiff]
  abel

lemma blockP_eq_selected_add_complement
    (S : Finset i) (hS : S ⊆ D.onLine) (c : ℝ) :
    D.blockP c =
      D.selectedHatPart S c + D.selectedHatPart (D.onLine \ S) c := by
  unfold ZeroBlockData.blockP selectedHatPart
  rw [D.onPart_eq_selected_add_complement S hS, smul_add]

variable (Pr : D.PairReps)

/-- Exact complement identity behind the core replacement. -/
lemma scaledBlockA_sub_selected_eq
    (S : Finset i) (hS : S ⊆ D.onLine) (c : ℝ) :
    (((c⁻¹ : ℝ) : ℂ) • D.blockA) - D.selectedHatPart S c =
      D.selectedHatPart (D.onLine \ S) c + D.blockQ c := by
  rw [← D.blockP_add_blockQ Pr c,
    D.blockP_eq_selected_add_complement S hS c]
  abel

/-- The positive index of the complement is bounded by the number of
unselected on-line labels plus the off-line-pair count. -/
theorem posIndex_scaledBlockA_sub_selected_le
    (S : Finset i) (hS : S ⊆ D.onLine) {c : ℝ} (hc : 0 < c)
    (hA : ((((c⁻¹ : ℝ) : ℂ) • D.blockA)).IsHermitian) :
    posIndex (hA.sub (D.selectedHatPart_posSemidef S hS hc).isHermitian) ≤
      #(D.onLine \ S) + Pr.p := by
  have hcomp := D.selectedHatPart_posSemidef (D.onLine \ S)
    Finset.sdiff_subset hc
  have hEq := D.scaledBlockA_sub_selected_eq Pr S hS c
  rw [hEq]
  have hsum := posIndex_add_le hcomp.isHermitian (D.blockQ_isHermitian c)
  rw [posIndex_eq_rank_of_posSemidef hcomp] at hsum
  exact hsum.trans (Nat.add_le_add
    (D.rank_selectedHatPart_le (D.onLine \ S) hc)
    (D.posIndex_blockQ_le Pr hc))

/-- Core-simple form of the same bound.  The three summands are respectively
excluded simple on-line labels, multiple on-line labels, and off-line pairs. -/
theorem posIndex_scaledBlockA_sub_selectedSimple_le
    (S : Finset i) (hS₁ : S ⊆ D.S₁) {c : ℝ} (hc : 0 < c)
    (hA : ((((c⁻¹ : ℝ) : ℂ) • D.blockA)).IsHermitian) :
    posIndex (hA.sub
      (D.selectedHatPart_posSemidef S
        (hS₁.trans D.S₁_subset_onLine) hc).isHermitian) ≤
      #(D.S₁ \ S) + D.s₂ + Pr.p := by
  have hSon : S ⊆ D.onLine := hS₁.trans D.S₁_subset_onLine
  have h := D.posIndex_scaledBlockA_sub_selected_le Pr S hSon hc hA
  rw [D.card_onLine_sdiff_selected S hS₁] at h
  exact h

end ZeroBlockData

end StrictImprovement
end Zeta23
