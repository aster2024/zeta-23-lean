/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q6SuperbinBinning
import Zeta23.StrictImprovement.Q6SuperbinResiduePacking
import Zeta23.StrictImprovement.WideRepairMixedPacking

/-!
# Concrete block inventory for the q6 superbin repair

Within each width-`32*pi` superbin, the left and right half bins are packed
separately into complete five-blocks.  Remainders of size four are retained;
remainders of size three are retained unless both halves have remainder three,
in which case the two remainders are merged into one six-block.

This file defines that dependent block family.  The global disjointness proof
and the endpoint lower bounds are kept in downstream modules.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Zeta23
namespace StrictImprovement

inductive Q6SuperbinBlockKind
  | fiveLeft
  | fiveRight
  | threeLeft
  | threeRight
  | fourLeft
  | fourRight
  | six
  deriving DecidableEq

instance q6SuperbinBlockKindFintype : Fintype Q6SuperbinBlockKind where
  elems := {.fiveLeft, .fiveRight, .threeLeft, .threeRight,
    .fourLeft, .fourRight, .six}
  complete x := by cases x <;> simp

lemma q6SuperbinBlockKind_univ :
    (Finset.univ : Finset Q6SuperbinBlockKind) =
      {.fiveLeft, .fiveRight, .threeLeft, .threeRight,
        .fourLeft, .fourRight, .six} := by
  ext x
  cases x <;> simp

def q6SuperbinLeftOccupancy
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B) : ℕ :=
  E.occupancy (b, 0)

def q6SuperbinRightOccupancy
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B) : ℕ :=
  E.occupancy (b, 1)

def q6SuperbinBlockCount
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B) :
    Q6SuperbinBlockKind → ℕ
  | .fiveLeft => q6SuperbinLeftOccupancy E b / 5
  | .fiveRight => q6SuperbinRightOccupancy E b / 5
  | .threeLeft =>
      if q6SuperbinLeftOccupancy E b % 5 = 3 ∧
          q6SuperbinRightOccupancy E b % 5 ≠ 3 then 1 else 0
  | .threeRight =>
      if q6SuperbinRightOccupancy E b % 5 = 3 ∧
          q6SuperbinLeftOccupancy E b % 5 ≠ 3 then 1 else 0
  | .fourLeft =>
      if q6SuperbinLeftOccupancy E b % 5 = 4 then 1 else 0
  | .fourRight =>
      if q6SuperbinRightOccupancy E b % 5 = 4 then 1 else 0
  | .six =>
      if q6SuperbinLeftOccupancy E b % 5 = 3 ∧
          q6SuperbinRightOccupancy E b % 5 = 3 then 1 else 0

def q6SuperbinBlockKindSize : Q6SuperbinBlockKind → ℕ
  | .fiveLeft | .fiveRight => 5
  | .threeLeft | .threeRight => 3
  | .fourLeft | .fourRight => 4
  | .six => 6

def q6SuperbinBlockKindReward : Q6SuperbinBlockKind → ℝ
  | .fiveLeft | .fiveRight => wideRepairRewardFive
  | .threeLeft | .threeRight => wideRepairRewardThree
  | .fourLeft | .fourRight => wideRepairRewardFour
  | .six => q6SuperbinReward

abbrev Q6SuperbinBlock
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :=
  Σ bk : B × Q6SuperbinBlockKind,
    Fin (q6SuperbinBlockCount E bk.1 bk.2)

def q6SuperbinBlockSize
    {S B : Type*} [Fintype B]
    {E : BinnedEnumeration S (B × Fin 2)}
    (q : Q6SuperbinBlock E) : ℕ :=
  q6SuperbinBlockKindSize q.1.2

def q6SuperbinBlockReward
    {S B : Type*} [Fintype B]
    {E : BinnedEnumeration S (B × Fin 2)}
    (q : Q6SuperbinBlock E) : ℝ :=
  q6SuperbinBlockKindReward q.1.2

/-- The concrete seven-kind inventory has exactly the pair reward used by the
25-case residue ledger. -/
theorem sum_q6SuperbinBlockReward_eq
    {S B : Type*} [Fintype B] [DecidableEq B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    ∑ q : Q6SuperbinBlock E, q6SuperbinBlockReward q =
      ∑ b, q6SuperbinPairReward
        (q6SuperbinLeftOccupancy E b)
        (q6SuperbinRightOccupancy E b) := by
  change
    (∑ q : (Σ bk : B × Q6SuperbinBlockKind,
        Fin (q6SuperbinBlockCount E bk.1 bk.2)),
      q6SuperbinBlockReward q) = _
  have hsum_kind (bk : B × Q6SuperbinBlockKind) :
      (∑ u : Fin (q6SuperbinBlockCount E bk.1 bk.2),
          q6SuperbinBlockReward
            (⟨bk, u⟩ : Q6SuperbinBlock E)) =
        (q6SuperbinBlockCount E bk.1 bk.2 : ℝ) *
          q6SuperbinBlockKindReward bk.2 := by
    simp [q6SuperbinBlockReward, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.sum_sigma'
    (fun bk u => q6SuperbinBlockReward (⟨bk, u⟩ : Q6SuperbinBlock E))]
  simp_rw [hsum_kind]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [q6SuperbinBlockKind_univ]
  have hleft : q6SuperbinLeftOccupancy E b % 5 < 5 :=
    Nat.mod_lt _ (by norm_num)
  have hright : q6SuperbinRightOccupancy E b % 5 < 5 :=
    Nat.mod_lt _ (by norm_num)
  interval_cases hl : q6SuperbinLeftOccupancy E b % 5 <;>
    interval_cases hr : q6SuperbinRightOccupancy E b % 5 <;>
    simp [q6SuperbinBlockCount, q6SuperbinBlockReward,
      q6SuperbinBlockKindReward, q6SuperbinPairReward,
      q6FineRemainderReward, hl, hr, Fintype.sum_sigma',
      nsmul_eq_mul] <;>
    ring

lemma q6_condition_of_fin_ite
    {p : Prop} [Decidable p] (u : Fin (if p then 1 else 0)) : p := by
  by_contra hp
  have hlt := u.isLt
  simp [hp] at hlt

private def q6WideThreeLeftWitness
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (h : q6SuperbinLeftOccupancy E b % 5 = 3) :
    Fin (if E.occupancy (b, 0) % 5 = 3 then 1 else 0) :=
  ⟨0, by
    change 0 < if q6SuperbinLeftOccupancy E b % 5 = 3 then 1 else 0
    simp [h]⟩

private def q6WideThreeRightWitness
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (h : q6SuperbinRightOccupancy E b % 5 = 3) :
    Fin (if E.occupancy (b, 1) % 5 = 3 then 1 else 0) :=
  ⟨0, by
    change 0 < if q6SuperbinRightOccupancy E b % 5 = 3 then 1 else 0
    simp [h]⟩

private def q6WideFourLeftWitness
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (h : q6SuperbinLeftOccupancy E b % 5 = 4) :
    Fin (if E.occupancy (b, 0) % 5 = 4 then 1 else 0) :=
  ⟨0, by
    change 0 < if q6SuperbinLeftOccupancy E b % 5 = 4 then 1 else 0
    simp [h]⟩

private def q6WideFourRightWitness
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (h : q6SuperbinRightOccupancy E b % 5 = 4) :
    Fin (if E.occupancy (b, 1) % 5 = 4 then 1 else 0) :=
  ⟨0, by
    change 0 < if q6SuperbinRightOccupancy E b % 5 = 4 then 1 else 0
    simp [h]⟩

def q6SuperbinBlockCoordinate
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2))
    (q : Q6SuperbinBlock E) :
    Fin (q6SuperbinBlockSize q) →
      Σ key : B × Fin 2, Fin (E.occupancy key) := by
  rcases q with ⟨⟨b, kind⟩, u⟩
  cases kind with
  | fiveLeft =>
      exact fun k => ⟨(b, 0),
        wideRepairFiveSlot (q6SuperbinLeftOccupancy E b) u k⟩
  | fiveRight =>
      exact fun k => ⟨(b, 1),
        wideRepairFiveSlot (q6SuperbinRightOccupancy E b) u k⟩
  | threeLeft =>
      have hcond : q6SuperbinLeftOccupancy E b % 5 = 3 ∧
          q6SuperbinRightOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      exact fun k => ⟨(b, 0),
        wideRepairResidualSlot (q6SuperbinLeftOccupancy E b) 3 hcond.1 k⟩
  | threeRight =>
      have hcond : q6SuperbinRightOccupancy E b % 5 = 3 ∧
          q6SuperbinLeftOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      exact fun k => ⟨(b, 1),
        wideRepairResidualSlot (q6SuperbinRightOccupancy E b) 3 hcond.1 k⟩
  | fourLeft =>
      have hcond : q6SuperbinLeftOccupancy E b % 5 = 4 :=
        q6_condition_of_fin_ite u
      exact fun k => ⟨(b, 0),
        wideRepairResidualSlot (q6SuperbinLeftOccupancy E b) 4 hcond k⟩
  | fourRight =>
      have hcond : q6SuperbinRightOccupancy E b % 5 = 4 :=
        q6_condition_of_fin_ite u
      exact fun k => ⟨(b, 1),
        wideRepairResidualSlot (q6SuperbinRightOccupancy E b) 4 hcond k⟩
  | six =>
      have hcond : q6SuperbinLeftOccupancy E b % 5 = 3 ∧
          q6SuperbinRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      intro k
      change Fin 6 at k
      by_cases hk : k.val < 3
      · exact ⟨(b, 0),
          wideRepairResidualSlot (q6SuperbinLeftOccupancy E b) 3 hcond.1
            ⟨k.val, hk⟩⟩
      · exact ⟨(b, 1),
          wideRepairResidualSlot (q6SuperbinRightOccupancy E b) 3 hcond.2
            ⟨k.val - 3, by omega⟩⟩

def q6SuperbinBlockIndex
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2))
    (q : Q6SuperbinBlock E) : Fin (q6SuperbinBlockSize q) → S :=
  fun k =>
    let c := q6SuperbinBlockCoordinate E q k
    E.entry c.1 c.2

/-- Forget the q6 merge and identify every selected point with its canonical
point in the old per-half three/four/five inventory.  For a six-block, the
first three points map to the left residual and the last three to the right
residual. -/
def q6SuperbinToWideRepairCoordinate
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    (Σ q : Q6SuperbinBlock E, Fin (q6SuperbinBlockSize q)) →
      Σ q : WideRepairBlock E, Fin (wideRepairBlockSize q) := by
  rintro ⟨⟨⟨b, kind⟩, u⟩, k⟩
  cases kind with
  | fiveLeft => exact ⟨Sum.inl ⟨(b, 0), u⟩, k⟩
  | fiveRight => exact ⟨Sum.inl ⟨(b, 1), u⟩, k⟩
  | threeLeft =>
      have hcond : q6SuperbinLeftOccupancy E b % 5 = 3 ∧
          q6SuperbinRightOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      exact ⟨Sum.inr (Sum.inl
        ⟨(b, 0), q6WideThreeLeftWitness E b hcond.1⟩), k⟩
  | threeRight =>
      have hcond : q6SuperbinRightOccupancy E b % 5 = 3 ∧
          q6SuperbinLeftOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      exact ⟨Sum.inr (Sum.inl
        ⟨(b, 1), q6WideThreeRightWitness E b hcond.1⟩), k⟩
  | fourLeft =>
      have hcond : q6SuperbinLeftOccupancy E b % 5 = 4 :=
        q6_condition_of_fin_ite u
      exact ⟨Sum.inr (Sum.inr
        ⟨(b, 0), q6WideFourLeftWitness E b hcond⟩), k⟩
  | fourRight =>
      have hcond : q6SuperbinRightOccupancy E b % 5 = 4 :=
        q6_condition_of_fin_ite u
      exact ⟨Sum.inr (Sum.inr
        ⟨(b, 1), q6WideFourRightWitness E b hcond⟩), k⟩
  | six =>
      have hcond : q6SuperbinLeftOccupancy E b % 5 = 3 ∧
          q6SuperbinRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      change Fin 6 at k
      by_cases hk : k.val < 3
      · exact ⟨Sum.inr (Sum.inl
          ⟨(b, 0), q6WideThreeLeftWitness E b hcond.1⟩),
            ⟨k.val, hk⟩⟩
      · have hk' : k.val - 3 < 3 := by omega
        exact ⟨Sum.inr (Sum.inl
          ⟨(b, 1), q6WideThreeRightWitness E b hcond.2⟩),
            (show Fin 3 from ⟨k.val - 3, hk'⟩)⟩

/-- Canonical inverse on the old selected inventory: a three-residue whose
partner is also a three-residue is routed into the merged six-block. -/
def wideRepairToQ6SuperbinCoordinate
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    (Σ q : WideRepairBlock E, Fin (wideRepairBlockSize q)) →
      Σ q : Q6SuperbinBlock E, Fin (q6SuperbinBlockSize q) := by
  rintro ⟨q, k⟩
  cases q with
  | inl q =>
      rcases q with ⟨⟨b, half⟩, u⟩
      by_cases hhalf : half.val = 0
      · have : half = 0 := Fin.ext hhalf
        subst half
        exact ⟨⟨⟨b, .fiveLeft⟩, u⟩, k⟩
      · have : half = 1 := Fin.ext (by omega)
        subst half
        exact ⟨⟨⟨b, .fiveRight⟩, u⟩, k⟩
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨⟨b, half⟩, z⟩
          have hmod := wideRepairThreeResidue_mod
            (E := E) ⟨(b, half), z⟩
          by_cases hhalf : half.val = 0
          · have : half = 0 := Fin.ext hhalf
            subst half
            change Fin 3 at k
            by_cases hp : q6SuperbinRightOccupancy E b % 5 = 3
            · exact ⟨⟨⟨b, .six⟩,
                ⟨0, by simp [q6SuperbinBlockCount,
                  q6SuperbinLeftOccupancy, hmod, hp]⟩⟩,
                  (show Fin 6 from ⟨k.val, by omega⟩)⟩
            · exact ⟨⟨⟨b, .threeLeft⟩,
                ⟨0, by simp [q6SuperbinBlockCount,
                  q6SuperbinLeftOccupancy, hmod, hp]⟩⟩, k⟩
          · have : half = 1 := Fin.ext (by omega)
            subst half
            change Fin 3 at k
            by_cases hp : q6SuperbinLeftOccupancy E b % 5 = 3
            · exact ⟨⟨⟨b, .six⟩,
                ⟨0, by simp [q6SuperbinBlockCount,
                  q6SuperbinRightOccupancy, hmod, hp]⟩⟩,
                  (show Fin 6 from ⟨k.val + 3, by omega⟩)⟩
            · exact ⟨⟨⟨b, .threeRight⟩,
                ⟨0, by simp [q6SuperbinBlockCount,
                  q6SuperbinRightOccupancy, hmod, hp]⟩⟩, k⟩
      | inr q =>
          rcases q with ⟨⟨b, half⟩, z⟩
          have hmod := wideRepairFourResidue_mod
            (E := E) ⟨(b, half), z⟩
          by_cases hhalf : half.val = 0
          · have : half = 0 := Fin.ext hhalf
            subst half
            exact ⟨⟨⟨b, .fourLeft⟩,
              ⟨0, by simp [q6SuperbinBlockCount,
                q6SuperbinLeftOccupancy, hmod]⟩⟩, k⟩
          · have : half = 1 := Fin.ext (by omega)
            subst half
            exact ⟨⟨⟨b, .fourRight⟩,
              ⟨0, by simp [q6SuperbinBlockCount,
                q6SuperbinRightOccupancy, hmod]⟩⟩, k⟩

private theorem q6SuperbinToWideRepairCoordinate_six_left
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (u : Fin (q6SuperbinBlockCount E b .six))
    (hcond : q6SuperbinLeftOccupancy E b % 5 = 3 ∧
      q6SuperbinRightOccupancy E b % 5 = 3)
    (k : Fin 6) (hk : k.val < 3) :
    q6SuperbinToWideRepairCoordinate E
        (⟨⟨⟨b, .six⟩, u⟩, k⟩ :
          Σ q : Q6SuperbinBlock E, Fin (q6SuperbinBlockSize q)) =
      ⟨Sum.inr (Sum.inl
          ⟨(b, 0), q6WideThreeLeftWitness E b hcond.1⟩),
        (⟨k.val, hk⟩ : Fin 3)⟩ := by
  dsimp only [q6SuperbinToWideRepairCoordinate, id]
  rw [dif_pos hk]
  rfl

private theorem q6SuperbinToWideRepairCoordinate_six_right
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (u : Fin (q6SuperbinBlockCount E b .six))
    (hcond : q6SuperbinLeftOccupancy E b % 5 = 3 ∧
      q6SuperbinRightOccupancy E b % 5 = 3)
    (k : Fin 6) (hk : ¬ k.val < 3) :
    q6SuperbinToWideRepairCoordinate E
        (⟨⟨⟨b, .six⟩, u⟩, k⟩ :
          Σ q : Q6SuperbinBlock E, Fin (q6SuperbinBlockSize q)) =
      ⟨Sum.inr (Sum.inl
          ⟨(b, 1), q6WideThreeRightWitness E b hcond.2⟩),
        (⟨k.val - 3, by omega⟩ : Fin 3)⟩ := by
  dsimp only [q6SuperbinToWideRepairCoordinate, id]
  rw [dif_neg hk]

theorem wideRepairToQ6_leftInverse
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    Function.LeftInverse
      (wideRepairToQ6SuperbinCoordinate E)
      (q6SuperbinToWideRepairCoordinate E) := by
  rintro ⟨⟨⟨b, kind⟩, u⟩, k⟩
  cases kind with
  | fiveLeft => rfl
  | fiveRight => rfl
  | threeLeft =>
      have hcond : q6SuperbinLeftOccupancy E b % 5 = 3 ∧
          q6SuperbinRightOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q6SuperbinBlockCount,
          hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q6SuperbinBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      simp [q6SuperbinToWideRepairCoordinate,
        wideRepairToQ6SuperbinCoordinate, hcond.1, hcond.2]
      rfl
  | threeRight =>
      have hcond : q6SuperbinRightOccupancy E b % 5 = 3 ∧
          q6SuperbinLeftOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q6SuperbinBlockCount,
          hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q6SuperbinBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      simp [q6SuperbinToWideRepairCoordinate,
        wideRepairToQ6SuperbinCoordinate, hcond.1, hcond.2]
      rfl
  | fourLeft =>
      have hcond : q6SuperbinLeftOccupancy E b % 5 = 4 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q6SuperbinBlockCount, hcond]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q6SuperbinBlockCount, hcond] at hlt
        omega
      subst u
      simp [q6SuperbinToWideRepairCoordinate,
        wideRepairToQ6SuperbinCoordinate, hcond]
  | fourRight =>
      have hcond : q6SuperbinRightOccupancy E b % 5 = 4 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q6SuperbinBlockCount, hcond]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q6SuperbinBlockCount, hcond] at hlt
        omega
      subst u
      simp [q6SuperbinToWideRepairCoordinate,
        wideRepairToQ6SuperbinCoordinate, hcond]
  | six =>
      have hcond : q6SuperbinLeftOccupancy E b % 5 = 3 ∧
          q6SuperbinRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q6SuperbinBlockCount,
          hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q6SuperbinBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      change Fin 6 at k
      by_cases hk : k.val < 3
      · rw [q6SuperbinToWideRepairCoordinate_six_left E b _ hcond k hk]
        simp [wideRepairToQ6SuperbinCoordinate, hcond.1, hcond.2]
        dsimp only [id]
      · have hk3 : 3 ≤ k.val := by omega
        have hval : k.val - 3 + 3 = k.val := Nat.sub_add_cancel hk3
        rw [q6SuperbinToWideRepairCoordinate_six_right E b _ hcond k hk]
        simp [wideRepairToQ6SuperbinCoordinate, hcond.1, hcond.2, hval]
        dsimp only [id]
        congr <;> omega

theorem q6SuperbinToWideRepairCoordinate_injective
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    Function.Injective (q6SuperbinToWideRepairCoordinate E) :=
  (wideRepairToQ6_leftInverse E).injective

theorem q6SuperbinBlockIndex_eq_wideRepair
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2))
    (qk : Σ q : Q6SuperbinBlock E, Fin (q6SuperbinBlockSize q)) :
    q6SuperbinBlockIndex E qk.1 qk.2 =
      wideRepairBlockIndex E
        (q6SuperbinToWideRepairCoordinate E qk).1
        (q6SuperbinToWideRepairCoordinate E qk).2 := by
  rcases qk with ⟨⟨⟨b, kind⟩, u⟩, k⟩
  cases kind with
  | fiveLeft => rfl
  | fiveRight => rfl
  | threeLeft => rfl
  | threeRight => rfl
  | fourLeft => rfl
  | fourRight => rfl
  | six =>
      have hcond : q6SuperbinLeftOccupancy E b % 5 = 3 ∧
          q6SuperbinRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q6SuperbinBlockCount,
          hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q6SuperbinBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      change Fin 6 at k
      by_cases hk : k.val < 3
      · rw [q6SuperbinToWideRepairCoordinate_six_left E b _ hcond k hk]
        simp [q6SuperbinBlockIndex, q6SuperbinBlockCoordinate,
          wideRepairBlockIndex, hcond.1, hk]
        dsimp only [id]
        rw [dif_pos hk]
        simp only [q6SuperbinLeftOccupancy]
      · rw [q6SuperbinToWideRepairCoordinate_six_right E b _ hcond k hk]
        simp [q6SuperbinBlockIndex, q6SuperbinBlockCoordinate,
          wideRepairBlockIndex, hcond.2, hk]
        dsimp only [id]
        rw [dif_neg hk]
        simp only [q6SuperbinRightOccupancy]

/-- All points selected by the merged q6 inventory are globally distinct. -/
theorem q6SuperbinBlockIndex_injective
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    Function.Injective
      (fun qk : Σ q : Q6SuperbinBlock E, Fin (q6SuperbinBlockSize q) =>
        q6SuperbinBlockIndex E qk.1 qk.2) := by
  intro qk qk' h
  have hwide :
      wideRepairBlockIndex E
          (q6SuperbinToWideRepairCoordinate E qk).1
          (q6SuperbinToWideRepairCoordinate E qk).2 =
        wideRepairBlockIndex E
          (q6SuperbinToWideRepairCoordinate E qk').1
          (q6SuperbinToWideRepairCoordinate E qk').2 := by
    rw [← q6SuperbinBlockIndex_eq_wideRepair E qk,
      ← q6SuperbinBlockIndex_eq_wideRepair E qk']
    exact h
  have hmap := wideRepairBlockIndex_injective E hwide
  exact q6SuperbinToWideRepairCoordinate_injective E hmap

end StrictImprovement
end Zeta23

end
