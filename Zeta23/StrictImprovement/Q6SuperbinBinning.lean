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
  Fin (q6SuperbinCount D) × Fin 2

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

theorem q6HalfBinEnumeration_superbin_cover
    {S : Type*} [Fintype S]
    (D base : ℝ) (coord : S → ℝ)
    (hrange : ∀ s, 0 ≤ coord s - base ∧
      coord s - base ≤ 2 * Real.pi * D) :
    ∑ b : Fin (q6SuperbinCount D),
        ((q6HalfBinEnumeration D base coord hrange).occupancy (b, 0) +
          (q6HalfBinEnumeration D base coord hrange).occupancy (b, 1)) =
      Fintype.card S := by
  rw [← q6HalfBinEnumeration_cover D base coord hrange]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  exact (Fin.sum_univ_two (fun h : Fin 2 =>
    (q6HalfBinEnumeration D base coord hrange).occupancy (b, h))).symm

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

variable (Z : ZeroConfig) (T C : ℝ) (P : Params)

noncomputable def coreQ6HalfBinEnumeration
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    BinnedEnumeration (CoreSimpleLabel Z T C)
      (Q6HalfBinKey (coreBinD T P)) :=
  q6HalfBinEnumeration (coreBinD T P) (coreBinBase T C P)
    (coreScaledOrdinate Z T C P)
    (coreScaledOrdinate_range Z T C P hL hC)

theorem coreQ6HalfBinEnumeration_superbin_cover
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    ∑ b : Fin (q6SuperbinCount (coreBinD T P)),
        ((coreQ6HalfBinEnumeration Z T C P hL hC).occupancy (b, 0) +
          (coreQ6HalfBinEnumeration Z T C P hL hC).occupancy (b, 1)) =
      Fintype.card (CoreSimpleLabel Z T C) := by
  exact q6HalfBinEnumeration_superbin_cover
    (coreBinD T P) (coreBinBase T C P)
    (coreScaledOrdinate Z T C P)
    (coreScaledOrdinate_range Z T C P hL hC)

theorem coreQ6Superbin_card_le
    (hL : 0 < P.L T) (hT : 0 ≤ T) :
    (Fintype.card (Fin (q6SuperbinCount (coreBinD T P))) : ℝ) ≤
      coreBinD T P / 16 + 1 := by
  apply q6Superbin_card_le
  unfold coreBinD
  positivity

theorem coreQ6LeftEntry_bounds
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (b : Fin (q6SuperbinCount (coreBinD T P)))
    (k : Fin ((coreQ6HalfBinEnumeration Z T C P hL hC).occupancy (b, 0))) :
    let z := (coreQ6HalfBinEnumeration Z T C P hL hC).entry (b, 0) k
    0 ≤ coreScaledOrdinate Z T C P z -
        (coreBinBase T C P + (b.val : ℝ) * (32 * Real.pi)) ∧
      coreScaledOrdinate Z T C P z -
        (coreBinBase T C P + (b.val : ℝ) * (32 * Real.pi)) ≤
          16 * Real.pi := by
  let E := coreQ6HalfBinEnumeration Z T C P hL hC
  let z := E.entry (b, 0) k
  have hkey := q6HalfBinEnumeration_entry_key
    (coreBinD T P) (coreBinBase T C P)
    (coreScaledOrdinate Z T C P)
    (coreScaledOrdinate_range Z T C P hL hC) (b, 0) k
  have hsuper : q6Superbin (coreBinD T P) (coreBinBase T C P)
      (coreScaledOrdinate Z T C P)
      (coreScaledOrdinate_range Z T C P hL hC) z = b :=
    congrArg Prod.fst hkey
  have hhalf : q6SuperbinHalf (coreBinD T P) (coreBinBase T C P)
      (coreScaledOrdinate Z T C P)
      (coreScaledOrdinate_range Z T C P hL hC) z = 0 :=
    congrArg Prod.snd hkey
  have hbounds := q6SuperbinHalf_zero_bounds
    (coreScaledOrdinate_range Z T C P hL hC) hhalf
  dsimp only at hbounds ⊢
  rw [hsuper] at hbounds
  exact hbounds

theorem coreQ6RightEntry_bounds
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (b : Fin (q6SuperbinCount (coreBinD T P)))
    (k : Fin ((coreQ6HalfBinEnumeration Z T C P hL hC).occupancy (b, 1))) :
    let z := (coreQ6HalfBinEnumeration Z T C P hL hC).entry (b, 1) k
    16 * Real.pi ≤ coreScaledOrdinate Z T C P z -
        (coreBinBase T C P + (b.val : ℝ) * (32 * Real.pi)) ∧
      coreScaledOrdinate Z T C P z -
        (coreBinBase T C P + (b.val : ℝ) * (32 * Real.pi)) ≤
          32 * Real.pi := by
  let E := coreQ6HalfBinEnumeration Z T C P hL hC
  let z := E.entry (b, 1) k
  have hkey := q6HalfBinEnumeration_entry_key
    (coreBinD T P) (coreBinBase T C P)
    (coreScaledOrdinate Z T C P)
    (coreScaledOrdinate_range Z T C P hL hC) (b, 1) k
  have hsuper : q6Superbin (coreBinD T P) (coreBinBase T C P)
      (coreScaledOrdinate Z T C P)
      (coreScaledOrdinate_range Z T C P hL hC) z = b :=
    congrArg Prod.fst hkey
  have hhalf : q6SuperbinHalf (coreBinD T P) (coreBinBase T C P)
      (coreScaledOrdinate Z T C P)
      (coreScaledOrdinate_range Z T C P hL hC) z = 1 :=
    congrArg Prod.snd hkey
  have hbounds := q6SuperbinHalf_one_bounds
    (coreScaledOrdinate_range Z T C P hL hC) hhalf
  dsimp only at hbounds ⊢
  rw [hsuper] at hbounds
  exact hbounds

end StrictImprovement
end Zeta23

end
