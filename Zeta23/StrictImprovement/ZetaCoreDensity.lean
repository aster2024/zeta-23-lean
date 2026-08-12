/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaBoundaryLoss

/-!
# Density bounds for the selected width-three core

The selected core differs from the enlarged-window simple-zero count by the
exact `excludedSimpleCount`.  This file converts that finite identity into
the two one-sided asymptotic bounds consumed by the quadratic gain:

* every baseline lower density for `N0s` is inherited by the core;
* the core has upper density at most one.

Both transfers keep their boundary terms explicit before using the already
proved `o(N)` estimates.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace StrictImprovement

/-- A nonnegative `o(N)` function is eventually at most `eps*N`. -/
lemma eventually_le_mul_of_nonneg_isLittleO
    {f N : ℝ → ℝ}
    (hf : ∀ᶠ T in atTop, 0 ≤ f T)
    (hN : ∀ᶠ T in atTop, 0 ≤ N T)
    (hsmall : f =o[atTop] N) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T in atTop, f T ≤ eps * N T := by
  filter_upwards [hsmall.def heps, hf, hN] with T h hfn hNn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hfn,
    abs_of_nonneg hNn] at h
  exact h

/-- The frozen enlarged-window count `NII` is negligible relative to the
main dyadic zero count. -/
  theorem NII_isLittleO_N
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    (fun T => (Assembly.NII Z T : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hR.local_count
  obtain ⟨C, hbound⟩ := Tail.eventually_NII_le Z hA₀ hloc
  have hO : (fun T => (Assembly.NII Z T : ℝ)) =O[atTop]
      (fun T => Real.sqrt T * l T) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [hbound, Assembly.eventually_l_pos] with T h hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    simpa [mul_assoc] using h
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl Z hR
      Assembly.isLittleO_sqrt_mul_l_Tl)

/-- Finite-height lower transfer from the main simple-zero count to the
selected core. -/
theorem eventually_coreCard_lower_of
    (Z : ZeroConfig) (Q : ℝ → Params) {H eps : ℝ}
    (hT : ∀ᶠ T : ℝ in atTop, 0 ≤ T)
    (hconj : ∀ᶠ T in atTop, ZeroSide.PhiHatConj T (Q T))
    (hbase : ∀ᶠ T in atTop,
      H * (Z.N T (2 * T) : ℝ) ≤ (Z.N0s T (2 * T) : ℝ))
    (hboundary : ∀ᶠ T in atTop,
      (excludedSimpleCount Z T 3 : ℝ) ≤
        eps * (Z.N T (2 * T) : ℝ)) :
    ∀ᶠ T in atTop,
      (H - eps) * (Z.N T (2 * T) : ℝ) ≤
        (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) := by
  filter_upwards [hT, hconj, hbase, hboundary] with T hT0 hc hb he
  have hcountNat := N0s_le_coreCard_add_excluded Z hT0 (Q T) hc
  have hcount : (Z.N0s T (2 * T) : ℝ) ≤
      (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) +
        (excludedSimpleCount Z T 3 : ℝ) := by
    exact_mod_cast hcountNat
  linarith

/-- Any epsilon-form lower density for main-window simple zeros is inherited
by the selected core. -/
theorem coreCard_lower_from_simple_epsilon_form
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (Q : ℝ → Params)
    (hconj : ∀ᶠ T in atTop, ZeroSide.PhiHatConj T (Q T))
    {H : ℝ}
    (hbase : ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (H - eps) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T)) :
    ∀ eps > 0, ∀ᶠ T in atTop,
      (H - eps) * (Z.N T (2 * T) : ℝ) ≤
        (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) := by
  intro eps heps
  obtain ⟨T₀, hb⟩ := hbase (eps / 2) (by linarith)
  have hbEv : ∀ᶠ T in atTop,
      (H - eps / 2) * (Z.N T (2 * T) : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) :=
    eventually_atTop.2 ⟨T₀, hb⟩
  have hN : ∀ᶠ T in atTop, 0 ≤ (Z.N T (2 * T) : ℝ) :=
    Eventually.of_forall fun T => Nat.cast_nonneg _
  have he0 : ∀ᶠ T in atTop, 0 ≤ (excludedSimpleCount Z T 3 : ℝ) :=
    Eventually.of_forall fun T => Nat.cast_nonneg _
  have he := eventually_le_mul_of_nonneg_isLittleO he0 hN
    (excludedSimpleCount_three_isLittleO Z hR) (show 0 < eps / 2 by linarith)
  have htransfer := eventually_coreCard_lower_of Z Q
    (eventually_ge_atTop (0 : ℝ)) hconj hbEv he
  filter_upwards [htransfer] with T h
  convert h using 1 <;> ring

/-- The selected core has upper density at most one. -/
theorem eventually_coreCard_le_one_add
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (Q : ℝ → Params)
    (hconj : ∀ᶠ T in atTop, ZeroSide.PhiHatConj T (Q T))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T in atTop,
      (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) ≤
        (1 + eps) * (Z.N T (2 * T) : ℝ) := by
  have hN : ∀ᶠ T in atTop, 0 ≤ (Z.N T (2 * T) : ℝ) :=
    Eventually.of_forall fun T => Nat.cast_nonneg _
  have hII0 : ∀ᶠ T in atTop, 0 ≤ (Assembly.NII Z T : ℝ) :=
    Eventually.of_forall fun T => Nat.cast_nonneg _
  have hII := eventually_le_mul_of_nonneg_isLittleO hII0 hN
    (NII_isLittleO_N Z hR) heps
  filter_upwards [eventually_ge_atTop (0 : ℝ), hconj, hII]
    with T hT hc hsmall
  have hcardNat := coreCard_le_N_add_NII Z (C := 3) hT (Q T) hc
  have hcard : (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) ≤
      (Z.N T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast hcardNat
  linarith

/-- A positive epsilon-form simple-zero density makes the selected core
eventually nonempty.  This is the noncircular gate needed before invoking the
division-by-core-card strict defect. -/
theorem eventually_core_nonempty_from_simple_epsilon_form
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (Q : ℝ → Params)
    (hconj : ∀ᶠ T in atTop, ZeroSide.PhiHatConj T (Q T))
    {H : ℝ} (hH : 0 < H)
    (hbase : ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (H - eps) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T)) :
    ∀ᶠ T in atTop, Nonempty (CoreSimpleLabel Z T 3) := by
  have hcore := coreCard_lower_from_simple_epsilon_form
    Z hR Q hconj hbase (H / 2) (by linarith)
  have hN := (Assembly.tendsto_N_atTop Z hR).eventually_gt_atTop 0
  filter_upwards [hcore, hN] with T hc hNT
  have hprod : 0 < (H - H / 2) * (Z.N T (2 * T) : ℝ) := by
    exact mul_pos (by linarith) hNT
  have hcardR : 0 < (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) :=
    hprod.trans_le hc
  have hcard : 0 < Fintype.card (CoreSimpleLabel Z T 3) := by
    exact_mod_cast hcardR
  exact Fintype.card_pos_iff.mp hcard

end StrictImprovement
end Zeta23

end
