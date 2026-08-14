/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WideRepairBinning

/-!
# Paired width-sixteen bins

The superbin has width `32*pi` and is split into two half-open width-`16*pi`
halves.  This file supplies the exact `D/16+1` count and the translated
left/right coordinate bounds consumed by the q6 endpoint interface.
-/

noncomputable section

open Real Finset
open scoped BigOperators

namespace Zeta23
namespace StrictImprovement

def q6SuperbinCount (D : ℝ) : ℕ := ⌊D / 16⌋₊ + 1

noncomputable def q6Superbin
    {S : Type*} (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) (s : S) :
    Fin (q6SuperbinCount D) := by
  let q : ℝ := (coord s - base) / (32 * Real.pi)
  have hden : 0 < (32 : ℝ) * Real.pi := by positivity
  have hqD : q ≤ D / 16 := by
    apply (div_le_iff₀ hden).2
    calc
      coord s - base ≤ 2 * Real.pi * D := (hrange s).2
      _ = D / 16 * (32 * Real.pi) := by ring
  refine ⟨⌊q⌋₊, ?_⟩
  unfold q6SuperbinCount
  exact Nat.lt_succ_of_le (Nat.floor_mono hqD)

theorem q6Superbin_card_le {D : ℝ} (hD : 0 ≤ D) :
    (Fintype.card (Fin (q6SuperbinCount D)) : ℝ) ≤ D / 16 + 1 := by
  have hf : ((⌊D / 16⌋₊ : ℕ) : ℝ) ≤ D / 16 :=
    Nat.floor_le (div_nonneg hD (by norm_num))
  have hcardNat : Fintype.card (Fin (q6SuperbinCount D)) =
      q6SuperbinCount D := Fintype.card_fin _
  have hcardReal : (Fintype.card (Fin (q6SuperbinCount D)) : ℝ) =
      (q6SuperbinCount D : ℝ) := by exact_mod_cast hcardNat
  rw [hcardReal, q6SuperbinCount, Nat.cast_add, Nat.cast_one]
  linarith

/-- Coordinates translated by their superbin's left endpoint lie in
`[0,32*pi)`. -/
theorem q6Superbin_local_bounds
    {S : Type*} {D base : ℝ} {coord : S → ℝ}
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) (s : S) :
    let b := q6Superbin D base coord hrange s
    0 ≤ coord s - (base + (b.val : ℝ) * (32 * Real.pi)) ∧
      coord s - (base + (b.val : ℝ) * (32 * Real.pi)) < 32 * Real.pi := by
  let q : ℝ := (coord s - base) / (32 * Real.pi)
  have hden : 0 < (32 : ℝ) * Real.pi := by positivity
  have hq0 : 0 ≤ q := div_nonneg (hrange s).1 hden.le
  have hlo : ((⌊q⌋₊ : ℕ) : ℝ) ≤ q := Nat.floor_le hq0
  have hhi : q < ((⌊q⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one q
  have hlo' : ((⌊q⌋₊ : ℕ) : ℝ) * (32 * Real.pi) ≤
      coord s - base := (le_div_iff₀ hden).mp hlo
  have hhi' : coord s - base <
      (((⌊q⌋₊ : ℕ) : ℝ) + 1) * (32 * Real.pi) :=
    (div_lt_iff₀ hden).mp hhi
  change 0 ≤ coord s -
      (base + ((⌊q⌋₊ : ℕ) : ℝ) * (32 * Real.pi)) ∧
    coord s - (base + ((⌊q⌋₊ : ℕ) : ℝ) * (32 * Real.pi)) <
      32 * Real.pi
  constructor <;> nlinarith

noncomputable def q6SuperbinHalf
    {S : Type*} (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) (s : S) : Fin 2 :=
  if coord s -
      (base + ((q6Superbin D base coord hrange s).val : ℝ) *
        (32 * Real.pi)) < 16 * Real.pi then 0 else 1

theorem q6SuperbinHalf_zero_bounds
    {S : Type*} {D base : ℝ} {coord : S → ℝ}
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) {s : S}
    (hhalf : q6SuperbinHalf D base coord hrange s = 0) :
    let b := q6Superbin D base coord hrange s
    0 ≤ coord s - (base + (b.val : ℝ) * (32 * Real.pi)) ∧
      coord s - (base + (b.val : ℝ) * (32 * Real.pi)) ≤ 16 * Real.pi := by
  have hlocal := q6Superbin_local_bounds hrange s
  dsimp only at hlocal ⊢
  have hlt : coord s -
      (base + ((q6Superbin D base coord hrange s).val : ℝ) *
        (32 * Real.pi)) < 16 * Real.pi := by
    by_contra h
    have hdef : q6SuperbinHalf D base coord hrange s = 1 := by
      simp [q6SuperbinHalf, h]
    rw [hdef] at hhalf
    norm_num at hhalf
  exact ⟨hlocal.1, hlt.le⟩

theorem q6SuperbinHalf_one_bounds
    {S : Type*} {D base : ℝ} {coord : S → ℝ}
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) {s : S}
    (hhalf : q6SuperbinHalf D base coord hrange s = 1) :
    let b := q6Superbin D base coord hrange s
    16 * Real.pi ≤ coord s - (base + (b.val : ℝ) * (32 * Real.pi)) ∧
      coord s - (base + (b.val : ℝ) * (32 * Real.pi)) ≤ 32 * Real.pi := by
  have hlocal := q6Superbin_local_bounds hrange s
  dsimp only at hlocal ⊢
  have hge : 16 * Real.pi ≤ coord s -
      (base + ((q6Superbin D base coord hrange s).val : ℝ) *
        (32 * Real.pi)) := by
    by_contra h
    have hlt : coord s -
        (base + ((q6Superbin D base coord hrange s).val : ℝ) *
          (32 * Real.pi)) < 16 * Real.pi := lt_of_not_ge h
    have hdef : q6SuperbinHalf D base coord hrange s = 0 := by
      simp [q6SuperbinHalf, hlt]
    rw [hdef] at hhalf
    norm_num at hhalf
  exact ⟨hge, hlocal.2.le⟩

abbrev Q6HalfBinKey (D : ℝ) :=
  Σ _ : Fin (q6SuperbinCount D), Fin 2

noncomputable def q6HalfBinKey
    {S : Type*} (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) (s : S) : Q6HalfBinKey D :=
  ⟨q6Superbin D base coord hrange s,
    q6SuperbinHalf D base coord hrange s⟩

noncomputable def q6HalfBinEnumeration
    {S : Type*} [Fintype S]
    (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) :
    BinnedEnumeration S (Q6HalfBinKey D) :=
  fiberBinnedEnumeration (q6HalfBinKey D base coord hrange)

theorem q6HalfBinEnumeration_cover
    {S : Type*} [Fintype S]
    (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) :
    ∑ q, (q6HalfBinEnumeration D base coord hrange).occupancy q =
      Fintype.card S := by
  exact fiberBinnedEnumeration_cover (q6HalfBinKey D base coord hrange)

@[simp] theorem q6HalfBinEnumeration_entry_key
    {S : Type*} [Fintype S]
    (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D)
    (q : Q6HalfBinKey D)
    (k : Fin ((q6HalfBinEnumeration D base coord hrange).occupancy q)) :
    q6HalfBinKey D base coord hrange
      ((q6HalfBinEnumeration D base coord hrange).entry q k) = q := by
  exact fiberBinnedEnumeration_at_bin
    (q6HalfBinKey D base coord hrange) q k

end StrictImprovement
end Zeta23

end
