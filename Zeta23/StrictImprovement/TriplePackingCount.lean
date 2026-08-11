/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.FiniteDefect

/-!
# Exact count for disjoint triples inside bins

For a bin containing `r` labels, consecutive grouping produces `r / 3`
triples and leaves at most two labels.  Summing this exact integer statement
is the combinatorial count consumed by the local pinching argument.

This file deliberately separates the cardinal arithmetic from the later
construction of the actual injective index map.  It is a source draft until
checked by the pinned Lean toolchain recorded in `LEAN_FORMALIZATION_PLAN.md`.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

/-- Division by three leaves at most two unused labels. -/
lemma le_three_mul_div_three_add_two (r : ℕ) :
    r ≤ 3 * (r / 3) + 2 := by
  omega

/-- Sum of the per-bin discarded labels is at most twice the number of bins. -/
theorem sum_le_three_mul_tripleCount_add_two_card
    {B : Type*} [Fintype B] [DecidableEq B] (occupancy : B → ℕ) :
    ∑ b, occupancy b ≤
      3 * (∑ b, occupancy b / 3) + 2 * Fintype.card B := by
  calc
    ∑ b, occupancy b ≤ ∑ b, (3 * (occupancy b / 3) + 2) :=
      Finset.sum_le_sum fun b _ => le_three_mul_div_three_add_two (occupancy b)
    _ = 3 * (∑ b, occupancy b / 3) + 2 * Fintype.card B := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Real-cast form of the same exact count, avoiding truncated subtraction. -/
theorem cast_total_le_three_cast_tripleCount_add_two_card
    {B : Type*} [Fintype B] [DecidableEq B] (occupancy : B → ℕ) :
    ((∑ b, occupancy b : ℕ) : ℝ) ≤
      3 * ((∑ b, occupancy b / 3 : ℕ) : ℝ) +
        2 * (Fintype.card B : ℝ) := by
  exact_mod_cast sum_le_three_mul_tripleCount_add_two_card occupancy

/-- If the number of geometric bins is at most `D/4 + 1`, the exact integer
triple count has precisely the lower bound used by the hyperbolic-stable
defect theorem. -/
theorem tripleCount_ge_hyperbolic_target
    {B : Type*} [Fintype B] [DecidableEq B]
    (occupancy : B → ℕ) (D : ℝ)
    (hbins : (Fintype.card B : ℝ) ≤ D / 4 + 1) :
    (1 : ℝ) / 3 *
        max 0 (((∑ b, occupancy b : ℕ) : ℝ) - D / 2 - 2) ≤
      ((∑ b, occupancy b / 3 : ℕ) : ℝ) := by
  let total : ℝ := ((∑ b, occupancy b : ℕ) : ℝ)
  let triples : ℝ := ((∑ b, occupancy b / 3 : ℕ) : ℝ)
  have hraw := cast_total_le_three_cast_tripleCount_add_two_card occupancy
  have htarget : total - D / 2 - 2 ≤ 3 * triples := by
    dsimp [total, triples] at hraw ⊢
    nlinarith
  have htriple_nonneg : 0 ≤ triples := by
    dsimp [triples]
    positivity
  have hmax : max 0 (total - D / 2 - 2) ≤ 3 * triples := by
    apply max_le
    · nlinarith
    · exact htarget
  dsimp [total, triples] at hmax ⊢
  nlinarith

/-! ## Canonical triples from a binned enumeration -/

/-- A finite family written as disjoint, duplicate-free enumerations of its
bins.  Coverage is intentionally not part of this structure: the zeta caller
will separately identify the core label type with the union of these bins. -/
structure BinnedEnumeration (S B : Type*) [Fintype B] where
  occupancy : B → ℕ
  at : (b : B) → Fin (occupancy b) → S
  at_injective : ∀ {b b' : B} {p : Fin (occupancy b)} {q : Fin (occupancy b')},
    at b p = at b' q → b = b' ∧ p.val = q.val

/-- The `q`-th complete triple in a bin uses local slots `3q,3q+1,3q+2`. -/
def tripleSlot (r : ℕ) (q : Fin (r / 3)) (k : Fin 3) : Fin r :=
  ⟨3 * q.val + k.val, by
    have hq := q.isLt
    have hk := k.isLt
    omega⟩

lemma tripleSlot_pair_injective (r : ℕ) :
    Function.Injective
      (fun qk : Fin (r / 3) × Fin 3 => tripleSlot r qk.1 qk.2) := by
  intro qk qk' h
  have hv : 3 * qk.1.val + qk.2.val =
      3 * qk'.1.val + qk'.2.val := congrArg Fin.val h
  have hq : qk.1.val = qk'.1.val := by
    have hk := qk.2.isLt
    have hk' := qk'.2.isLt
    omega
  have hk : qk.2.val = qk'.2.val := by omega
  apply Prod.ext
  · exact Fin.ext hq
  · exact Fin.ext hk

/-- One block index for every complete triple in every bin. -/
abbrev PackedTriple
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B) :=
  Σ b : B, Fin (E.occupancy b / 3)

/-- Concrete global label index of every slot of every packed triple. -/
def packedTripleIndex
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B)
    (q : PackedTriple E) (k : Fin 3) : S :=
  E.at q.1 (tripleSlot (E.occupancy q.1) q.2 k)

/-- Distinct bin/triple/slot coordinates always select distinct labels. -/
theorem packedTripleIndex_injective
    {S B : Type*} [Fintype B] (E : BinnedEnumeration S B) :
    Function.Injective
      (fun qk : PackedTriple E × Fin 3 => packedTripleIndex E qk.1 qk.2) := by
  rintro ⟨⟨b, q⟩, k⟩ ⟨⟨b', q'⟩, k'⟩ h
  have hlocal := E.at_injective h
  have hb : b = b' := hlocal.1
  subst b'
  have hv : 3 * q.val + k.val = 3 * q'.val + k'.val := hlocal.2
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

/-- The type of packed triples has the expected exact floor-sum cardinality. -/
@[simp] theorem card_packedTriple
    {S B : Type*} [Fintype B] [DecidableEq B]
    (E : BinnedEnumeration S B) :
    Fintype.card (PackedTriple E) = ∑ b, E.occupancy b / 3 := by
  simp [PackedTriple]

/-- Cardinal form of the hyperbolic target count for the canonical packing. -/
theorem card_packedTriple_ge_hyperbolic_target
    {S B : Type*} [Fintype B] [DecidableEq B]
    (E : BinnedEnumeration S B) (D : ℝ)
    (hbins : (Fintype.card B : ℝ) ≤ D / 4 + 1) :
    (1 : ℝ) / 3 *
        max 0 (((∑ b, E.occupancy b : ℕ) : ℝ) - D / 2 - 2) ≤
      (Fintype.card (PackedTriple E) : ℝ) := by
  rw [card_packedTriple E]
  exact tripleCount_ge_hyperbolic_target E.occupancy D hbins

/-- The canonical packing plugs directly into the already formalized Gram
triple trace-norm theorem. -/
theorem binned_gram_triples_traceNorm_lower
    {S B d : Type*} [Fintype S] [DecidableEq S]
    [Fintype B] [DecidableEq B] [Fintype d]
    (E : BinnedEnumeration S B)
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ q : PackedTriple E,
      delta ≤ tripleCorrelationEnergy x (packedTripleIndex E) q) :
    2 * (Fintype.card (PackedTriple E) : ℝ) * Real.sqrt delta ≤
      Tail.traceNorm (gramDeviation_isHermitian x) := by
  exact gram_triples_traceNorm_lower x hunit (packedTripleIndex E)
    (packedTripleIndex_injective E) hdelta hlocal

/-- Complete finite-dimensional binned theorem.  The coverage identity is
the only cardinal interface required from the concrete zeta binning. -/
theorem rank_trace_two_with_binned_gram_triples
    {S B d : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype B] [DecidableEq B] [Fintype d] [DecidableEq d]
    (E : BinnedEnumeration S B)
    (hcover : ∑ b, E.occupancy b = Fintype.card S)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 4 + 1)
    (x : S → d → ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ q : PackedTriple E,
      delta ≤ tripleCorrelationEnergy x (packedTripleIndex E) q)
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian)
    {b : ℕ} (hb : RHLinalg.posIndex hQ ≤ b) :
    2 * RHLinalg.rtrace (columnMatrix x * (columnMatrix x)ᴴ)
        - (Fintype.card S : ℝ)
        + 4 * RHLinalg.rtrace Q - 4 * (b : ℝ)
        + delta / (9 * (Fintype.card S : ℝ)) *
          max 0 ((Fintype.card S : ℝ) - D / 2 - 2) ^ 2
      ≤ frobSq (columnMatrix x * (columnMatrix x)ᴴ + Q) := by
  have hbase := rank_trace_two_with_local_gram_triples
    x hunit (packedTripleIndex E) (packedTripleIndex_injective E)
    hdelta hlocal hQ hb
  have hcount := card_packedTriple_ge_hyperbolic_target E D hbins
  rw [hcover] at hcount
  let s : ℝ := Fintype.card S
  let t : ℝ := Fintype.card (PackedTriple E)
  let target : ℝ := max 0 (s - D / 2 - 2)
  have hspos : 0 < s := by
    dsimp [s]
    exact_mod_cast Fintype.card_pos
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have htarget0 : 0 ≤ target := by
    dsimp [target]
    exact le_max_left _ _
  have hcount' : target / 3 ≤ t := by
    dsimp [s, t, target] at hcount ⊢
    nlinarith
  have hsquare : (target / 3) ^ 2 ≤ t ^ 2 := by
    nlinarith
  have hfactor : 0 ≤ delta / s := div_nonneg hdelta hspos.le
  have hgain : delta / (9 * s) * target ^ 2 ≤ t ^ 2 * delta / s := by
    calc
      delta / (9 * s) * target ^ 2 = (target / 3) ^ 2 * (delta / s) := by
        field_simp [ne_of_gt hspos]
        ring
      _ ≤ t ^ 2 * (delta / s) :=
        mul_le_mul_of_nonneg_right hsquare hfactor
      _ = t ^ 2 * delta / s := by ring
  dsimp [s, t, target] at hgain
  linarith

end StrictImprovement
end Zeta23
