/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.CoreComplement

/-!
# The finite core of simple on-line zeros

This module defines the actual finite label type used by the strict
improvement argument.  A core label is a distinct zero in `I'`, on the
critical line, simple, and with ordinate in `[T+C, 2T-C]`.

Only exact finite-set identities and the zero-side positive-index consequence
are proved here.  The analytic estimate saying that the excluded count is
`o(N(T,2T))` is deliberately not assumed or hidden in this file.

This is a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open RHLinalg
open ZeroSide

variable (Z : ZeroConfig) (T C : ℝ)

/-- All distinct simple on-line labels in the paper's enlarged finite window
`I'`. -/
def nearSimple : Finset (ZI Z T) :=
  Finset.univ.filter fun z => (z : ℂ).re = 1 / 2 ∧ Z.mult z = 1

/-- Core simple labels with ordinate in the closed interior interval. -/
def coreSimple : Finset (ZI Z T) :=
  (nearSimple Z T).filter fun z =>
    T + C ≤ (z : ℂ).im ∧ (z : ℂ).im ≤ 2 * T - C

/-- The number of simple on-line labels in `I'` excluded from the core. -/
def excludedSimpleCount : ℕ :=
  #((nearSimple Z T) \ coreSimple Z T C)

/-- The finite type of core labels. -/
abbrev CoreSimpleLabel := ↑(coreSimple Z T C)

lemma coreSimple_subset_nearSimple :
    coreSimple Z T C ⊆ nearSimple Z T := by
  exact Finset.filter_subset _ _

variable (P : Params) (hconj : PhiHatConj T P)

private abbrev D : ZeroBlockData (ZI Z T) (Fin (P.d T)) :=
  blockData Z T P hconj

private abbrev Pr : (D Z T P hconj).PairReps :=
  mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)

/-- The direct set-theoretic definition of simple on-line labels agrees with
the frozen abstract block classification. -/
lemma blockData_S₁_eq_nearSimple :
    (D Z T P hconj).S₁ = nearSimple Z T := by
  ext z
  simp only [nearSimple, Finset.mem_filter, Finset.mem_univ, true_and,
    ZeroSide.ZeroBlockData.S₁]
  change
    ((ZeroSide.mkData Z T (evalVec Z T P) (evalVec_reflect hconj)).σ z = z ∧
      (ZeroSide.mkData Z T (evalVec Z T P) (evalVec_reflect hconj)).m z = 1) ↔
        (z : ℂ).re = 1 / 2 ∧ Z.mult z = 1
  rw [ZeroSide.mkData_σ_eq_iff, ZeroSide.mkData_m]

lemma coreSimple_subset_blockData_S₁ :
    coreSimple Z T C ⊆ (D Z T P hconj).S₁ := by
  rw [blockData_S₁_eq_nearSimple]
  exact coreSimple_subset_nearSimple Z T C

lemma card_blockData_S₁_sdiff_core :
    #((D Z T P hconj).S₁ \ coreSimple Z T C) =
      excludedSimpleCount Z T C := by
  rw [blockData_S₁_eq_nearSimple]
  rfl

/-- Exact finite identity: the unselected on-line labels consist of excluded
simple labels and all multiple on-line labels. -/
lemma card_onLine_sdiff_core :
    #((D Z T P hconj).onLine \ coreSimple Z T C) =
      excludedSimpleCount Z T C + Z.s2 T := by
  rw [(D Z T P hconj).card_onLine_sdiff_selected
    (coreSimple Z T C) (coreSimple_subset_blockData_S₁ Z T C P hconj)]
  rw [card_blockData_S₁_sdiff_core]
  have hs₂ : (D Z T P hconj).s₂ = Z.s2 T := by
    simpa [D, ZeroSide.blockData] using
      (ZeroSide.s2_eq_mk Z T (evalVec Z T P)
        (evalVec_reflect hconj)).symm
  rw [hs₂]

/-- Positive-index bound for the actual core contribution, still in exact
hat scaling `c = a L^2`.  The excluded count has not been estimated. -/
theorem posIndex_scaledBlockA_sub_core_le
    (hc : 0 < P.a T * P.L T ^ 2) :
    let hA :
        (((((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) •
          (D Z T P hconj).blockA)).IsHermitian :=
      ZeroSide.ZeroBlockData.isHermitian_real_smul
        (D Z T P hconj).blockA_isHermitian _
    posIndex (hA.sub
      ((D Z T P hconj).selectedHatPart_posSemidef
        (coreSimple Z T C)
        ((coreSimple_subset_blockData_S₁ Z T C P hconj).trans
          (D Z T P hconj).S₁_subset_onLine)
        hc).isHermitian) ≤
      excludedSimpleCount Z T C + Z.s2 T + Z.p T := by
  dsimp only
  have hraw :=
    (D Z T P hconj).posIndex_scaledBlockA_sub_selectedSimple_le
      (Pr Z T P hconj) (coreSimple Z T C)
      (coreSimple_subset_blockData_S₁ Z T C P hconj) hc
      (ZeroSide.ZeroBlockData.isHermitian_real_smul
        (D Z T P hconj).blockA_isHermitian _)
  rw [card_blockData_S₁_sdiff_core] at hraw
  have hs₂ : (D Z T P hconj).s₂ = Z.s2 T := by
    simpa [D, ZeroSide.blockData] using
      (ZeroSide.s2_eq_mk Z T (evalVec Z T P)
        (evalVec_reflect hconj)).symm
  have hp : (Pr Z T P hconj).p = Z.p T := by
    change #({z : ZI Z T | 1 / 2 < (z : ℂ).re}) = Z.p T
    have hp0 := ZeroSide.p_eq_mk Z T (evalVec Z T P)
      (evalVec_reflect hconj)
    change Z.p T = #({z : ZI Z T | 1 / 2 < (z : ℂ).re}) at hp0
    exact hp0.symm
  rw [hs₂, hp] at hraw
  exact hraw

end StrictImprovement
end Zeta23
