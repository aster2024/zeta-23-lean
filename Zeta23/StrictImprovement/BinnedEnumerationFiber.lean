/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.TriplePackingCount

/-!
# Lossless enumeration of finite fibers

Given an arbitrary map from a finite label type to a finite bin type, this
module constructs the `BinnedEnumeration` used by the local pinching theorem.
The construction is exact: labels in distinct bins or distinct local slots
cannot collide, and the sum of the occupancies is exactly the total number of
labels.

This separates the purely finite bookkeeping from the later geometric choice
of bins for scaled zeta ordinates.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Zeta23
namespace StrictImprovement

/-- Number of labels in one fiber of a finite binning map. -/
noncomputable def fiberOccupancy
    {S B : Type*} [Fintype S] (bin : S → B) (b : B) : ℕ := by
  classical
  exact Fintype.card {s : S // bin s = b}

/-- A canonical, choice-independent-for-theorems indexing of one finite
fiber.  No order on the labels is required. -/
noncomputable def fiberEquivFin
    {S B : Type*} [Fintype S] (bin : S → B) (b : B) :
    {s : S // bin s = b} ≃ Fin (fiberOccupancy bin b) := by
  classical
  unfold fiberOccupancy
  exact Fintype.equivFin _

/-- Every finite binning map induces a duplicate-free enumeration of all of
its fibers. -/
noncomputable def fiberBinnedEnumeration
    {S B : Type*} [Fintype S] [Fintype B] (bin : S → B) :
    BinnedEnumeration S B where
  occupancy := fiberOccupancy bin
  entry := fun b i => ((fiberEquivFin bin b).symm i).1
  entry_injective := by
    intro b b' p q h
    have hb : b = b' := by
      calc
        b = bin ((fiberEquivFin bin b).symm p).1 :=
          ((fiberEquivFin bin b).symm p).2.symm
        _ = bin ((fiberEquivFin bin b').symm q).1 := congrArg bin h
        _ = b' := ((fiberEquivFin bin b').symm q).2
    subst b'
    have hs : (fiberEquivFin bin b).symm p =
        (fiberEquivFin bin b).symm q := Subtype.ext h
    have hpq : p = q := (fiberEquivFin bin b).symm.injective hs
    exact ⟨rfl, congrArg Fin.val hpq⟩

@[simp] theorem fiberBinnedEnumeration_at_bin
    {S B : Type*} [Fintype S] [Fintype B]
    (bin : S → B) (b : B)
    (i : Fin ((fiberBinnedEnumeration bin).occupancy b)) :
    bin ((fiberBinnedEnumeration bin).entry b i) = b := by
  exact ((fiberEquivFin bin b).symm i).2

/-- Fiber enumeration covers the source type exactly. -/
theorem fiberBinnedEnumeration_cover
    {S B : Type*} [Fintype S] [Fintype B]
    [DecidableEq B] (bin : S → B) :
    ∑ b, (fiberBinnedEnumeration bin).occupancy b = Fintype.card S := by
  classical
  change ∑ b, fiberOccupancy bin b = Fintype.card S
  calc
    ∑ b, fiberOccupancy bin b =
        Fintype.card (Σ b : B, {s : S // bin s = b}) := by
      simp [fiberOccupancy]
      rfl
    _ = Fintype.card S :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv bin)

/-- The exact fiber construction can be fed directly to the complete binned
rank--trace theorem; only geometric bin count and local-energy bounds remain
for the caller. -/
theorem rank_trace_two_with_fiber_binning
    {S B d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (bin : S → B)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 4 + 1)
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ q : PackedTriple (fiberBinnedEnumeration bin),
      delta ≤ tripleCorrelationEnergy x
        (packedTripleIndex (fiberBinnedEnumeration bin)) q)
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : RHLinalg.posIndex hQ ≤ b) :
    2 * RHLinalg.rtrace (columnMatrix x * Matrix.conjTranspose (columnMatrix x))
        - (Fintype.card S : ℝ)
        + 4 * RHLinalg.rtrace Q - 4 * (b : ℝ)
        + delta / (9 * (Fintype.card S : ℝ)) *
          max 0 ((Fintype.card S : ℝ) - D / 2 - 2) ^ 2
      ≤ frobSq (columnMatrix x * Matrix.conjTranspose (columnMatrix x) + Q) := by
  exact rank_trace_two_with_binned_gram_triples
    (fiberBinnedEnumeration bin) (fiberBinnedEnumeration_cover bin)
    D hbins x hunit hdelta hlocal hQ hb

end StrictImprovement
end Zeta23
