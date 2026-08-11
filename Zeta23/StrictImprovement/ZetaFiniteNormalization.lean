/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaCore

/-!
# Finite normalized vectors for the zeta core

This module instantiates the abstract finite/full normalization bridge with
the frozen zero-side vectors `vhat = v / sqrt(a L^2)`.  The truncated Poisson
identity supplies the exact upper bound on every finite squared norm.

Strict positivity of every core norm is a separate analytic input: it follows
later from the pointwise grid-tail estimate.  It is exposed as a hypothesis
here rather than hidden in a total normalization definition.

This is a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open RHLinalg
open ZeroSide
open ZeroSide.RankTraceMult

variable (Z : ZeroConfig) (T C : ℝ) (P : Params)
variable (hconj : PhiHatConj T P)

private abbrev D : ZeroBlockData (ZI Z T) (Fin (P.d T)) :=
  blockData Z T P hconj

/-- A core label regarded as a member of the full on-line subtype. -/
def coreOnLine (z : CoreSimpleLabel Z T C) : (D Z T P hconj).onLine :=
  ⟨z, (D Z T P hconj).S₁_subset_onLine
    (coreSimple_subset_blockData_S₁ Z T C P hconj z.2)⟩

/-- The finite vector already normalized by the full Poisson mass
`sqrt(a L^2)`. -/
def finiteCoreVec (z : CoreSimpleLabel Z T C) : Fin (P.d T) -> ℂ :=
  (D Z T P hconj).vhat (P.a T * P.L T ^ 2)
    (coreOnLine Z T C P hconj z)

/-- Its squared norm, which lies in `[0,1]`. -/
def finiteCoreWeight (z : CoreSimpleLabel Z T C) : ℝ :=
  vectorWeight (finiteCoreVec Z T C P hconj z)

/-- Unitized finite core vector.  The useful unit-norm theorem assumes that
the corresponding finite weight is positive. -/
def normalizedCoreVec (z : CoreSimpleLabel Z T C) : Fin (P.d T) -> ℂ :=
  unitize (finiteCoreVec Z T C P hconj z)

lemma finiteCoreWeight_nonneg (z : CoreSimpleLabel Z T C) :
    0 ≤ finiteCoreWeight Z T C P hconj z := by
  exact vectorWeight_nonneg _

lemma finiteCoreWeight_eq_xsq (z : CoreSimpleLabel Z T C) :
    finiteCoreWeight Z T C P hconj z =
      xsq ((D Z T P hconj).vhat (P.a T * P.L T ^ 2))
        (coreOnLine Z T C P hconj z) := by
  rfl

/-- The frozen truncated Poisson lemma gives the exact upper endpoint of the
finite weights. -/
lemma finiteCoreWeight_le_one
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (z : CoreSimpleLabel Z T C) :
    finiteCoreWeight Z T C P hconj z ≤ 1 := by
  let htrunc : ∀ q ∈ (D Z T P hconj).onLine,
      ∑ k, ‖(D Z T P hconj).v q k‖ ^ 2 ≤ P.a T * P.L T ^ 2 :=
    fun q hq => sum_normSq_v_le Z T P hconj hreal hPois q hq
  have h := (D Z T P hconj).xsq_vhat_le hc htrunc
    (coreOnLine Z T C P hconj z)
  simpa only [finiteCoreWeight_eq_xsq] using h

lemma normalizedCoreVec_isUnit
    (hpos : ∀ z, 0 < finiteCoreWeight Z T C P hconj z)
    (z : CoreSimpleLabel Z T C) :
    ∑ k, ‖normalizedCoreVec Z T C P hconj z k‖ ^ 2 = 1 := by
  exact unitize_isUnit _ (hpos z)

/-- Exact matrix identity: the selected finite core block is the weighted
sum of its unitized projectors. -/
lemma selectedHatPart_eq_weighted_normalizedCore
    (hc : 0 < P.a T * P.L T ^ 2)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T C P hconj z) :
    (D Z T P hconj).selectedHatPart (coreSimple Z T C)
        (P.a T * P.L T ^ 2) =
      weightedProjectorSum (normalizedCoreVec Z T C P hconj)
        (finiteCoreWeight Z T C P hconj) := by
  rw [(D Z T P hconj).selectedHatPart_eq_sum_vhat
    (coreSimple Z T C)
    (coreSimple_subset_blockData_S₁ Z T C P hconj) hc]
  symm
  exact weightedProjectorSum_unitize
    (finiteCoreVec Z T C P hconj) hpos

/-- The core-complement inertia bound in the exact weighted-projector form
consumed by `FiniteFullNormalization.lean`. -/
theorem posIndex_scaledBlockA_sub_weightedCore_le
    (hc : 0 < P.a T * P.L T ^ 2)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T C P hconj z) :
    let hA :
        (((((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) •
          (D Z T P hconj).blockA)).IsHermitian :=
      ZeroSide.ZeroBlockData.isHermitian_real_smul
        (D Z T P hconj).blockA_isHermitian _
    posIndex (hA.sub
      (weightedProjectorSum_posSemidef
        (normalizedCoreVec Z T C P hconj)
        (finiteCoreWeight Z T C P hconj)
        (finiteCoreWeight_nonneg Z T C P hconj)).isHermitian) ≤
      excludedSimpleCount Z T C + Z.s2 T + Z.p T := by
  dsimp only
  have h := posIndex_scaledBlockA_sub_core_le Z T C P hconj hc
  rw [selectedHatPart_eq_weighted_normalizedCore Z T C P hconj hc hpos] at h
  exact h

end StrictImprovement
end Zeta23

