/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7FullSpectralBinning
import Zeta23.StrictImprovement.Q7FullSpectralResiduePacking
import Zeta23.StrictImprovement.WideRepairMixedPacking

/-!
# Concrete block inventory for the full-spectral q7 superbin repair

Within each width-`32*pi` superbin, the left and right half bins are packed
separately into complete five-blocks.  Isolated remainders of size three and
four are retained.  A `(3,3)` pair is merged into a six-block, while `(3,4)`
and `(4,3)` pairs are merged into the two oriented seven-blocks.

This file defines that dependent block family.  The global disjointness proof
and the endpoint lower bounds are kept in downstream modules.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Zeta23
namespace StrictImprovement

inductive Q7FullSpectralBlockKind
  | fiveLeft
  | fiveRight
  | threeLeft
  | threeRight
  | fourLeft
  | fourRight
  | six
  | sevenThreeFour
  | sevenFourThree
  deriving DecidableEq

instance q7FullSpectralBlockKindFintype : Fintype Q7FullSpectralBlockKind where
  elems := {.fiveLeft, .fiveRight, .threeLeft, .threeRight,
    .fourLeft, .fourRight, .six, .sevenThreeFour, .sevenFourThree}
  complete x := by cases x <;> simp

lemma q7FullSpectralBlockKind_univ :
    (Finset.univ : Finset Q7FullSpectralBlockKind) =
      {.fiveLeft, .fiveRight, .threeLeft, .threeRight,
        .fourLeft, .fourRight, .six, .sevenThreeFour, .sevenFourThree} := by
  ext x
  cases x <;> simp

def q7FullSpectralLeftOccupancy
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B) : ℕ :=
  E.occupancy (b, 0)

def q7FullSpectralRightOccupancy
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B) : ℕ :=
  E.occupancy (b, 1)

def q7FullSpectralBlockCount
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B) :
    Q7FullSpectralBlockKind → ℕ
  | .fiveLeft => q7FullSpectralLeftOccupancy E b / 5
  | .fiveRight => q7FullSpectralRightOccupancy E b / 5
  | .threeLeft =>
      if q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 3 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 4 then 1 else 0
  | .threeRight =>
      if q7FullSpectralRightOccupancy E b % 5 = 3 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 3 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 4 then 1 else 0
  | .fourLeft =>
      if q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 3 then 1 else 0
  | .fourRight =>
      if q7FullSpectralRightOccupancy E b % 5 = 4 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 3 then 1 else 0
  | .six =>
      if q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 then 1 else 0
  | .sevenThreeFour =>
      if q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 4 then 1 else 0
  | .sevenFourThree =>
      if q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 then 1 else 0

def q7FullSpectralBlockKindSize : Q7FullSpectralBlockKind → ℕ
  | .fiveLeft | .fiveRight => 5
  | .threeLeft | .threeRight => 3
  | .fourLeft | .fourRight => 4
  | .six => 6
  | .sevenThreeFour | .sevenFourThree => 7

def q7FullSpectralBlockKindReward : Q7FullSpectralBlockKind → ℝ
  | .fiveLeft | .fiveRight => wideRepairRewardFive
  | .threeLeft | .threeRight => wideRepairRewardThree
  | .fourLeft | .fourRight => wideRepairRewardFour
  | .six => q7FullSpectralSixReward
  | .sevenThreeFour | .sevenFourThree => q7FullSpectralSevenReward

abbrev Q7FullSpectralBlock
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :=
  Σ bk : B × Q7FullSpectralBlockKind,
    Fin (q7FullSpectralBlockCount E bk.1 bk.2)

def q7FullSpectralBlockSize
    {S B : Type*} [Fintype B]
    {E : BinnedEnumeration S (B × Fin 2)}
    (q : Q7FullSpectralBlock E) : ℕ :=
  q7FullSpectralBlockKindSize q.1.2

def q7FullSpectralBlockReward
    {S B : Type*} [Fintype B]
    {E : BinnedEnumeration S (B × Fin 2)}
    (q : Q7FullSpectralBlock E) : ℝ :=
  q7FullSpectralBlockKindReward q.1.2

/-- The concrete nine-kind inventory has exactly the pair reward used by the
25-case residue ledger. -/
theorem sum_q7FullSpectralBlockReward_eq
    {S B : Type*} [Fintype B] [DecidableEq B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    ∑ q : Q7FullSpectralBlock E, q7FullSpectralBlockReward q =
      ∑ b, q7FullSpectralPairReward
        (q7FullSpectralLeftOccupancy E b)
        (q7FullSpectralRightOccupancy E b) := by
  change
    (∑ q : (Σ bk : B × Q7FullSpectralBlockKind,
        Fin (q7FullSpectralBlockCount E bk.1 bk.2)),
      q7FullSpectralBlockReward q) = _
  have hsum_kind (bk : B × Q7FullSpectralBlockKind) :
      (∑ u : Fin (q7FullSpectralBlockCount E bk.1 bk.2),
          q7FullSpectralBlockReward
            (⟨bk, u⟩ : Q7FullSpectralBlock E)) =
        (q7FullSpectralBlockCount E bk.1 bk.2 : ℝ) *
          q7FullSpectralBlockKindReward bk.2 := by
    simp [q7FullSpectralBlockReward, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.sum_sigma'
    (fun bk u => q7FullSpectralBlockReward (⟨bk, u⟩ : Q7FullSpectralBlock E))]
  simp_rw [hsum_kind]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [q7FullSpectralBlockKind_univ]
  have hleft : q7FullSpectralLeftOccupancy E b % 5 < 5 :=
    Nat.mod_lt _ (by norm_num)
  have hright : q7FullSpectralRightOccupancy E b % 5 < 5 :=
    Nat.mod_lt _ (by norm_num)
  interval_cases hl : q7FullSpectralLeftOccupancy E b % 5 <;>
    interval_cases hr : q7FullSpectralRightOccupancy E b % 5 <;>
    simp [q7FullSpectralBlockCount, q7FullSpectralBlockReward,
      q7FullSpectralBlockKindReward, q7FullSpectralPairReward,
      q7FullSpectralFineRemainderReward, hl, hr, Fintype.sum_sigma',
      nsmul_eq_mul] <;>
    ring

private lemma q6_condition_of_fin_ite
    {p : Prop} [Decidable p] (u : Fin (if p then 1 else 0)) : p := by
  by_contra hp
  have hlt := u.isLt
  simp [hp] at hlt

private def q6WideThreeLeftWitness
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (h : q7FullSpectralLeftOccupancy E b % 5 = 3) :
    Fin (if E.occupancy (b, 0) % 5 = 3 then 1 else 0) :=
  ⟨0, by
    change 0 < if q7FullSpectralLeftOccupancy E b % 5 = 3 then 1 else 0
    simp [h]⟩

private def q6WideThreeRightWitness
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (h : q7FullSpectralRightOccupancy E b % 5 = 3) :
    Fin (if E.occupancy (b, 1) % 5 = 3 then 1 else 0) :=
  ⟨0, by
    change 0 < if q7FullSpectralRightOccupancy E b % 5 = 3 then 1 else 0
    simp [h]⟩

private def q6WideFourLeftWitness
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (h : q7FullSpectralLeftOccupancy E b % 5 = 4) :
    Fin (if E.occupancy (b, 0) % 5 = 4 then 1 else 0) :=
  ⟨0, by
    change 0 < if q7FullSpectralLeftOccupancy E b % 5 = 4 then 1 else 0
    simp [h]⟩

private def q6WideFourRightWitness
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (h : q7FullSpectralRightOccupancy E b % 5 = 4) :
    Fin (if E.occupancy (b, 1) % 5 = 4 then 1 else 0) :=
  ⟨0, by
    change 0 < if q7FullSpectralRightOccupancy E b % 5 = 4 then 1 else 0
    simp [h]⟩

def q7FullSpectralBlockCoordinate
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2))
    (q : Q7FullSpectralBlock E) :
    Fin (q7FullSpectralBlockSize q) →
      Σ key : B × Fin 2, Fin (E.occupancy key) := by
  rcases q with ⟨⟨b, kind⟩, u⟩
  cases kind with
  | fiveLeft =>
      exact fun k => ⟨(b, 0),
        wideRepairFiveSlot (q7FullSpectralLeftOccupancy E b) u k⟩
  | fiveRight =>
      exact fun k => ⟨(b, 1),
        wideRepairFiveSlot (q7FullSpectralRightOccupancy E b) u k⟩
  | threeLeft =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 3 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 4 :=
        q6_condition_of_fin_ite u
      exact fun k => ⟨(b, 0),
        wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 3 hcond.1 k⟩
  | threeRight =>
      have hcond : q7FullSpectralRightOccupancy E b % 5 = 3 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 3 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 4 :=
        q6_condition_of_fin_ite u
      exact fun k => ⟨(b, 1),
        wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 3 hcond.1 k⟩
  | fourLeft =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      exact fun k => ⟨(b, 0),
        wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 4 hcond.1 k⟩
  | fourRight =>
      have hcond : q7FullSpectralRightOccupancy E b % 5 = 4 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      exact fun k => ⟨(b, 1),
        wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 4 hcond.1 k⟩
  | six =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      intro k
      change Fin 6 at k
      by_cases hk : k.val < 3
      · exact ⟨(b, 0),
          wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 3 hcond.1
            ⟨k.val, hk⟩⟩
      · exact ⟨(b, 1),
          wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 3 hcond.2
            ⟨k.val - 3, by omega⟩⟩
  | sevenThreeFour =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 4 :=
        q6_condition_of_fin_ite u
      intro k
      change Fin 7 at k
      by_cases hk : k.val < 3
      · exact ⟨(b, 0),
          wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 3 hcond.1
            ⟨k.val, hk⟩⟩
      · exact ⟨(b, 1),
          wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 4 hcond.2
            ⟨k.val - 3, by omega⟩⟩
  | sevenFourThree =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      intro k
      change Fin 7 at k
      by_cases hk : k.val < 4
      · exact ⟨(b, 0),
          wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 4 hcond.1
            ⟨k.val, hk⟩⟩
      · exact ⟨(b, 1),
          wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 3 hcond.2
            ⟨k.val - 4, by omega⟩⟩

def q7FullSpectralBlockIndex
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2))
    (q : Q7FullSpectralBlock E) : Fin (q7FullSpectralBlockSize q) → S :=
  fun k =>
    let c := q7FullSpectralBlockCoordinate E q k
    E.entry c.1 c.2

/-- Forget the q7 merges and identify every selected point with its canonical
point in the old per-half three/four/five inventory. -/
def q7FullSpectralToWideRepairCoordinate
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    (Σ q : Q7FullSpectralBlock E, Fin (q7FullSpectralBlockSize q)) →
      Σ q : WideRepairBlock E, Fin (wideRepairBlockSize q) := by
  rintro ⟨⟨⟨b, kind⟩, u⟩, k⟩
  cases kind with
  | fiveLeft => exact ⟨Sum.inl ⟨(b, 0), u⟩, k⟩
  | fiveRight => exact ⟨Sum.inl ⟨(b, 1), u⟩, k⟩
  | threeLeft =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 3 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 4 :=
        q6_condition_of_fin_ite u
      exact ⟨Sum.inr (Sum.inl
        ⟨(b, 0), q6WideThreeLeftWitness E b hcond.1⟩), k⟩
  | threeRight =>
      have hcond : q7FullSpectralRightOccupancy E b % 5 = 3 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 3 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 4 :=
        q6_condition_of_fin_ite u
      exact ⟨Sum.inr (Sum.inl
        ⟨(b, 1), q6WideThreeRightWitness E b hcond.1⟩), k⟩
  | fourLeft =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      exact ⟨Sum.inr (Sum.inr
        ⟨(b, 0), q6WideFourLeftWitness E b hcond.1⟩), k⟩
  | fourRight =>
      have hcond : q7FullSpectralRightOccupancy E b % 5 = 4 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      exact ⟨Sum.inr (Sum.inr
        ⟨(b, 1), q6WideFourRightWitness E b hcond.1⟩), k⟩
  | six =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 :=
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
  | sevenThreeFour =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 4 :=
        q6_condition_of_fin_ite u
      change Fin 7 at k
      by_cases hk : k.val < 3
      · exact ⟨Sum.inr (Sum.inl
          ⟨(b, 0), q6WideThreeLeftWitness E b hcond.1⟩),
            ⟨k.val, hk⟩⟩
      · have hk' : k.val - 3 < 4 := by omega
        exact ⟨Sum.inr (Sum.inr
          ⟨(b, 1), q6WideFourRightWitness E b hcond.2⟩),
            (show Fin 4 from ⟨k.val - 3, hk'⟩)⟩
  | sevenFourThree =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      change Fin 7 at k
      by_cases hk : k.val < 4
      · exact ⟨Sum.inr (Sum.inr
          ⟨(b, 0), q6WideFourLeftWitness E b hcond.1⟩),
            ⟨k.val, hk⟩⟩
      · have hk' : k.val - 4 < 3 := by omega
        exact ⟨Sum.inr (Sum.inl
          ⟨(b, 1), q6WideThreeRightWitness E b hcond.2⟩),
            (show Fin 3 from ⟨k.val - 4, hk'⟩)⟩

/-- Canonical inverse on the old selected inventory.  Residue pairs `(3,3)`,
`(3,4)`, and `(4,3)` are routed to the merged six/seven blocks. -/
def wideRepairToQ7FullSpectralCoordinate
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    (Σ q : WideRepairBlock E, Fin (wideRepairBlockSize q)) →
      Σ q : Q7FullSpectralBlock E, Fin (q7FullSpectralBlockSize q) := by
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
            by_cases hp : q7FullSpectralRightOccupancy E b % 5 = 3
            · exact ⟨⟨⟨b, .six⟩,
                ⟨0, by simp [q7FullSpectralBlockCount,
                  q7FullSpectralLeftOccupancy, hmod, hp]⟩⟩,
                  (show Fin 6 from ⟨k.val, by omega⟩)⟩
            · by_cases hp4 : q7FullSpectralRightOccupancy E b % 5 = 4
              · exact ⟨⟨⟨b, .sevenThreeFour⟩,
                  ⟨0, by simp [q7FullSpectralBlockCount,
                    q7FullSpectralLeftOccupancy, hmod, hp, hp4]⟩⟩,
                    (show Fin 7 from ⟨k.val, by omega⟩)⟩
              · exact ⟨⟨⟨b, .threeLeft⟩,
                  ⟨0, by simp [q7FullSpectralBlockCount,
                    q7FullSpectralLeftOccupancy, hmod, hp, hp4]⟩⟩, k⟩
          · have : half = 1 := Fin.ext (by omega)
            subst half
            change Fin 3 at k
            by_cases hp : q7FullSpectralLeftOccupancy E b % 5 = 3
            · exact ⟨⟨⟨b, .six⟩,
                ⟨0, by simp [q7FullSpectralBlockCount,
                  q7FullSpectralRightOccupancy, hmod, hp]⟩⟩,
                  (show Fin 6 from ⟨k.val + 3, by omega⟩)⟩
            · by_cases hp4 : q7FullSpectralLeftOccupancy E b % 5 = 4
              · exact ⟨⟨⟨b, .sevenFourThree⟩,
                  ⟨0, by simp [q7FullSpectralBlockCount,
                    q7FullSpectralRightOccupancy, hmod, hp, hp4]⟩⟩,
                    (show Fin 7 from ⟨k.val + 4, by omega⟩)⟩
              · exact ⟨⟨⟨b, .threeRight⟩,
                  ⟨0, by simp [q7FullSpectralBlockCount,
                    q7FullSpectralRightOccupancy, hmod, hp, hp4]⟩⟩, k⟩
      | inr q =>
          rcases q with ⟨⟨b, half⟩, z⟩
          have hmod := wideRepairFourResidue_mod
            (E := E) ⟨(b, half), z⟩
          by_cases hhalf : half.val = 0
          · have : half = 0 := Fin.ext hhalf
            subst half
            change Fin 4 at k
            by_cases hp : q7FullSpectralRightOccupancy E b % 5 = 3
            · exact ⟨⟨⟨b, .sevenFourThree⟩,
                ⟨0, by simp [q7FullSpectralBlockCount,
                  q7FullSpectralLeftOccupancy, hmod, hp]⟩⟩,
                  (show Fin 7 from ⟨k.val, by omega⟩)⟩
            · exact ⟨⟨⟨b, .fourLeft⟩,
                ⟨0, by simp [q7FullSpectralBlockCount,
                  q7FullSpectralLeftOccupancy, hmod, hp]⟩⟩, k⟩
          · have : half = 1 := Fin.ext (by omega)
            subst half
            change Fin 4 at k
            by_cases hp : q7FullSpectralLeftOccupancy E b % 5 = 3
            · exact ⟨⟨⟨b, .sevenThreeFour⟩,
                ⟨0, by simp [q7FullSpectralBlockCount,
                  q7FullSpectralRightOccupancy, hmod, hp]⟩⟩,
                  (show Fin 7 from ⟨k.val + 3, by omega⟩)⟩
            · exact ⟨⟨⟨b, .fourRight⟩,
                ⟨0, by simp [q7FullSpectralBlockCount,
                  q7FullSpectralRightOccupancy, hmod, hp]⟩⟩, k⟩

private theorem q7FullSpectralToWideRepairCoordinate_six_left
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (u : Fin (q7FullSpectralBlockCount E b .six))
    (hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
      q7FullSpectralRightOccupancy E b % 5 = 3)
    (k : Fin 6) (hk : k.val < 3) :
    q7FullSpectralToWideRepairCoordinate E
        (⟨⟨⟨b, .six⟩, u⟩, k⟩ :
          Σ q : Q7FullSpectralBlock E, Fin (q7FullSpectralBlockSize q)) =
      ⟨Sum.inr (Sum.inl
          ⟨(b, 0), q6WideThreeLeftWitness E b hcond.1⟩),
        (⟨k.val, hk⟩ : Fin 3)⟩ := by
  dsimp only [q7FullSpectralToWideRepairCoordinate, id]
  rw [dif_pos hk]
  rfl

private theorem q7FullSpectralToWideRepairCoordinate_six_right
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (u : Fin (q7FullSpectralBlockCount E b .six))
    (hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
      q7FullSpectralRightOccupancy E b % 5 = 3)
    (k : Fin 6) (hk : ¬ k.val < 3) :
    q7FullSpectralToWideRepairCoordinate E
        (⟨⟨⟨b, .six⟩, u⟩, k⟩ :
          Σ q : Q7FullSpectralBlock E, Fin (q7FullSpectralBlockSize q)) =
      ⟨Sum.inr (Sum.inl
          ⟨(b, 1), q6WideThreeRightWitness E b hcond.2⟩),
        (⟨k.val - 3, by omega⟩ : Fin 3)⟩ := by
  dsimp only [q7FullSpectralToWideRepairCoordinate, id]
  rw [dif_neg hk]

private theorem q7FullSpectralToWideRepairCoordinate_sevenThreeFour_left
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (u : Fin (q7FullSpectralBlockCount E b .sevenThreeFour))
    (hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
      q7FullSpectralRightOccupancy E b % 5 = 4)
    (k : Fin 7) (hk : k.val < 3) :
    q7FullSpectralToWideRepairCoordinate E
        (⟨⟨⟨b, .sevenThreeFour⟩, u⟩, k⟩ :
          Σ q : Q7FullSpectralBlock E, Fin (q7FullSpectralBlockSize q)) =
      ⟨Sum.inr (Sum.inl
          ⟨(b, 0), q6WideThreeLeftWitness E b hcond.1⟩),
        (⟨k.val, hk⟩ : Fin 3)⟩ := by
  dsimp only [q7FullSpectralToWideRepairCoordinate, id]
  rw [dif_pos hk]
  rfl

private theorem q7FullSpectralToWideRepairCoordinate_sevenThreeFour_right
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (u : Fin (q7FullSpectralBlockCount E b .sevenThreeFour))
    (hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
      q7FullSpectralRightOccupancy E b % 5 = 4)
    (k : Fin 7) (hk : ¬ k.val < 3) :
    q7FullSpectralToWideRepairCoordinate E
        (⟨⟨⟨b, .sevenThreeFour⟩, u⟩, k⟩ :
          Σ q : Q7FullSpectralBlock E, Fin (q7FullSpectralBlockSize q)) =
      ⟨Sum.inr (Sum.inr
          ⟨(b, 1), q6WideFourRightWitness E b hcond.2⟩),
        (⟨k.val - 3, by omega⟩ : Fin 4)⟩ := by
  dsimp only [q7FullSpectralToWideRepairCoordinate, id]
  rw [dif_neg hk]

private theorem q7FullSpectralToWideRepairCoordinate_sevenFourThree_left
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (u : Fin (q7FullSpectralBlockCount E b .sevenFourThree))
    (hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
      q7FullSpectralRightOccupancy E b % 5 = 3)
    (k : Fin 7) (hk : k.val < 4) :
    q7FullSpectralToWideRepairCoordinate E
        (⟨⟨⟨b, .sevenFourThree⟩, u⟩, k⟩ :
          Σ q : Q7FullSpectralBlock E, Fin (q7FullSpectralBlockSize q)) =
      ⟨Sum.inr (Sum.inr
          ⟨(b, 0), q6WideFourLeftWitness E b hcond.1⟩),
        (⟨k.val, hk⟩ : Fin 4)⟩ := by
  dsimp only [q7FullSpectralToWideRepairCoordinate, id]
  rw [dif_pos hk]
  rfl

private theorem q7FullSpectralToWideRepairCoordinate_sevenFourThree_right
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) (b : B)
    (u : Fin (q7FullSpectralBlockCount E b .sevenFourThree))
    (hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
      q7FullSpectralRightOccupancy E b % 5 = 3)
    (k : Fin 7) (hk : ¬ k.val < 4) :
    q7FullSpectralToWideRepairCoordinate E
        (⟨⟨⟨b, .sevenFourThree⟩, u⟩, k⟩ :
          Σ q : Q7FullSpectralBlock E, Fin (q7FullSpectralBlockSize q)) =
      ⟨Sum.inr (Sum.inl
          ⟨(b, 1), q6WideThreeRightWitness E b hcond.2⟩),
        (⟨k.val - 4, by omega⟩ : Fin 3)⟩ := by
  dsimp only [q7FullSpectralToWideRepairCoordinate, id]
  rw [dif_neg hk]

theorem wideRepairToQ7FullSpectral_leftInverse
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    Function.LeftInverse
      (wideRepairToQ7FullSpectralCoordinate E)
      (q7FullSpectralToWideRepairCoordinate E) := by
  rintro ⟨⟨⟨b, kind⟩, u⟩, k⟩
  cases kind with
  | fiveLeft => rfl
  | fiveRight => rfl
  | threeLeft =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 3 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 4 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q7FullSpectralBlockCount,
          hcond.1, hcond.2.1, hcond.2.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q7FullSpectralBlockCount, hcond.1, hcond.2.1, hcond.2.2] at hlt
        omega
      subst u
      simp [q7FullSpectralToWideRepairCoordinate,
        wideRepairToQ7FullSpectralCoordinate, hcond.1, hcond.2.1, hcond.2.2]
      rfl
  | threeRight =>
      have hcond : q7FullSpectralRightOccupancy E b % 5 = 3 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 3 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 4 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q7FullSpectralBlockCount,
          hcond.1, hcond.2.1, hcond.2.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q7FullSpectralBlockCount, hcond.1, hcond.2.1, hcond.2.2] at hlt
        omega
      subst u
      simp [q7FullSpectralToWideRepairCoordinate,
        wideRepairToQ7FullSpectralCoordinate, hcond.1, hcond.2.1, hcond.2.2]
      rfl
  | fourLeft =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q7FullSpectralBlockCount, hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q7FullSpectralBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      simp [q7FullSpectralToWideRepairCoordinate,
        wideRepairToQ7FullSpectralCoordinate, hcond.1, hcond.2]
      rfl
  | fourRight =>
      have hcond : q7FullSpectralRightOccupancy E b % 5 = 4 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 3 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q7FullSpectralBlockCount, hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q7FullSpectralBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      simp [q7FullSpectralToWideRepairCoordinate,
        wideRepairToQ7FullSpectralCoordinate, hcond.1, hcond.2]
      rfl
  | six =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q7FullSpectralBlockCount,
          hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q7FullSpectralBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      change Fin 6 at k
      by_cases hk : k.val < 3
      · rw [q7FullSpectralToWideRepairCoordinate_six_left E b _ hcond k hk]
        simp [wideRepairToQ7FullSpectralCoordinate, hcond.1, hcond.2]
        dsimp only [id]
      · have hk3 : 3 ≤ k.val := by omega
        have hval : k.val - 3 + 3 = k.val := Nat.sub_add_cancel hk3
        rw [q7FullSpectralToWideRepairCoordinate_six_right E b _ hcond k hk]
        simp [wideRepairToQ7FullSpectralCoordinate, hcond.1, hcond.2, hval]
        dsimp only [id]
        congr <;> omega
  | sevenThreeFour =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 4 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q7FullSpectralBlockCount,
          hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q7FullSpectralBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      change Fin 7 at k
      by_cases hk : k.val < 3
      · rw [q7FullSpectralToWideRepairCoordinate_sevenThreeFour_left
          E b _ hcond k hk]
        simp [wideRepairToQ7FullSpectralCoordinate, hcond.1, hcond.2]
        dsimp only [id]
      · have hk3 : 3 ≤ k.val := by omega
        have hval : k.val - 3 + 3 = k.val := Nat.sub_add_cancel hk3
        rw [q7FullSpectralToWideRepairCoordinate_sevenThreeFour_right
          E b _ hcond k hk]
        simp [wideRepairToQ7FullSpectralCoordinate, hcond.1, hcond.2, hval]
        dsimp only [id]
        congr <;> omega
  | sevenFourThree =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q7FullSpectralBlockCount,
          hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q7FullSpectralBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      change Fin 7 at k
      by_cases hk : k.val < 4
      · rw [q7FullSpectralToWideRepairCoordinate_sevenFourThree_left
          E b _ hcond k hk]
        simp [wideRepairToQ7FullSpectralCoordinate, hcond.1, hcond.2]
        dsimp only [id]
      · have hk4 : 4 ≤ k.val := by omega
        have hval : k.val - 4 + 4 = k.val := Nat.sub_add_cancel hk4
        rw [q7FullSpectralToWideRepairCoordinate_sevenFourThree_right
          E b _ hcond k hk]
        simp [wideRepairToQ7FullSpectralCoordinate, hcond.1, hcond.2, hval]
        dsimp only [id]
        congr <;> omega

theorem q7FullSpectralToWideRepairCoordinate_injective
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    Function.Injective (q7FullSpectralToWideRepairCoordinate E) :=
  (wideRepairToQ7FullSpectral_leftInverse E).injective

theorem q7FullSpectralBlockIndex_eq_wideRepair
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2))
    (qk : Σ q : Q7FullSpectralBlock E, Fin (q7FullSpectralBlockSize q)) :
    q7FullSpectralBlockIndex E qk.1 qk.2 =
      wideRepairBlockIndex E
        (q7FullSpectralToWideRepairCoordinate E qk).1
        (q7FullSpectralToWideRepairCoordinate E qk).2 := by
  rcases qk with ⟨⟨⟨b, kind⟩, u⟩, k⟩
  cases kind with
  | fiveLeft => rfl
  | fiveRight => rfl
  | threeLeft => rfl
  | threeRight => rfl
  | fourLeft => rfl
  | fourRight => rfl
  | six =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q7FullSpectralBlockCount,
          hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q7FullSpectralBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      change Fin 6 at k
      by_cases hk : k.val < 3
      · rw [q7FullSpectralToWideRepairCoordinate_six_left E b _ hcond k hk]
        simp [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate,
          wideRepairBlockIndex, hcond.1, hk]
        dsimp only [id]
        rw [dif_pos hk]
        simp only [q7FullSpectralLeftOccupancy]
      · rw [q7FullSpectralToWideRepairCoordinate_six_right E b _ hcond k hk]
        simp [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate,
          wideRepairBlockIndex, hcond.2, hk]
        dsimp only [id]
        rw [dif_neg hk]
        simp only [q7FullSpectralRightOccupancy]
  | sevenThreeFour =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 4 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q7FullSpectralBlockCount,
          hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q7FullSpectralBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      change Fin 7 at k
      by_cases hk : k.val < 3
      · rw [q7FullSpectralToWideRepairCoordinate_sevenThreeFour_left
          E b _ hcond k hk]
        simp [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate,
          wideRepairBlockIndex, hcond.1, hk]
        dsimp only [id]
        rw [dif_pos hk]
        simp only [q7FullSpectralLeftOccupancy]
      · rw [q7FullSpectralToWideRepairCoordinate_sevenThreeFour_right
          E b _ hcond k hk]
        simp [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate,
          wideRepairBlockIndex, hcond.2, hk]
        dsimp only [id]
        rw [dif_neg hk]
        simp only [q7FullSpectralRightOccupancy]
  | sevenFourThree =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 :=
        q6_condition_of_fin_ite u
      have hu : u = ⟨0, by simp [q7FullSpectralBlockCount,
          hcond.1, hcond.2]⟩ := by
        apply Fin.ext
        have hlt := u.isLt
        simp [q7FullSpectralBlockCount, hcond.1, hcond.2] at hlt
        omega
      subst u
      change Fin 7 at k
      by_cases hk : k.val < 4
      · rw [q7FullSpectralToWideRepairCoordinate_sevenFourThree_left
          E b _ hcond k hk]
        simp [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate,
          wideRepairBlockIndex, hcond.1, hk]
        dsimp only [id]
        rw [dif_pos hk]
        simp only [q7FullSpectralLeftOccupancy]
      · rw [q7FullSpectralToWideRepairCoordinate_sevenFourThree_right
          E b _ hcond k hk]
        simp [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate,
          wideRepairBlockIndex, hcond.2, hk]
        dsimp only [id]
        rw [dif_neg hk]
        simp only [q7FullSpectralRightOccupancy]

/-- All points selected by the merged q7 inventory are globally distinct. -/
theorem q7FullSpectralBlockIndex_injective
    {S B : Type*} [Fintype B]
    (E : BinnedEnumeration S (B × Fin 2)) :
    Function.Injective
      (fun qk : Σ q : Q7FullSpectralBlock E, Fin (q7FullSpectralBlockSize q) =>
        q7FullSpectralBlockIndex E qk.1 qk.2) := by
  intro qk qk' h
  have hwide :
      wideRepairBlockIndex E
          (q7FullSpectralToWideRepairCoordinate E qk).1
          (q7FullSpectralToWideRepairCoordinate E qk).2 =
        wideRepairBlockIndex E
          (q7FullSpectralToWideRepairCoordinate E qk').1
          (q7FullSpectralToWideRepairCoordinate E qk').2 := by
    rw [← q7FullSpectralBlockIndex_eq_wideRepair E qk,
      ← q7FullSpectralBlockIndex_eq_wideRepair E qk']
    exact h
  have hmap := wideRepairBlockIndex_injective E hwide
  exact q7FullSpectralToWideRepairCoordinate_injective E hmap

end StrictImprovement
end Zeta23

end
