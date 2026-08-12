/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Assembly.SeamMult
import Zeta23.StrictImprovement.ZetaWiderAtD
import Zeta23.StrictImprovement.ZetaWiderLocalDefect

/-!
# Tail-stable width-six four-point defect at a fixed height

This module transports the four-point core gain from the truncated zero matrix
`A_z` to the full matrix `G_z`.  The perturbation and boundary terms are exactly
the frozen multiplicity-aware seam terms; only the positive local gain changes
from the width-four triple coefficient to the width-six four-point coefficient.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset Real RHLinalg
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide

/-- The four-point strict-improvement version of `Assembly.seamA_mult2`. -/
theorem seamA_mult2_with_wider_core_gain
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P) (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    {θ₀ : ℝ} (hTl : Assembly.TailInputs Z P T θ₀)
    (ha : 0 < P.a T) (hL : 0 < P.L T) (hT : 0 ≤ T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 P hconj z)
    [Nonempty (CoreSimpleLabel Z T 3)]
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ q : PackedFour
      (coreWidthSixEnumeration Z T 3 P hL (by norm_num)),
      2 * delta ≤ fourCorrelationEnergy
        (normalizedCoreVec Z T 3 P hconj)
        (packedFourIndex
          (coreWidthSixEnumeration Z T 3 P hL (by norm_num))) q) :
    4 * rtrace (P.hat T (Z.Gz P T)) -
        frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ) -
        3 * (Assembly.NII Z T : ℝ) -
        θ₀ / (P.a T * P.L T) *
          (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) +
            θ₀ / (P.a T * P.L T)) +
        delta / (8 * (Fintype.card (CoreSimpleLabel Z T 3) : ℝ)) *
          max 0 ((Fintype.card (CoreSimpleLabel Z T 3) : ℝ) -
            coreBinD T P / 2 - 3) ^ 2
      ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3 := by
  obtain ⟨B, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE :
      P.hat T (Z.Gz P T) =
        P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← Assembly.hat_add]
    congr 1
    simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) :=
    div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_mult2_with_wider_core_gain
    Z T P hconj hreal hPois (by positivity) hL hT hpos hdelta hlocal
  have hpert := Assembly.ctr_sub_frobSq_perturb
    4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
      (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 :
      (Z.s1 T : ℝ) ≤
        (Z.N0s T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.s1_le Z hT
  have hNI :
      (Z.NIprime T : ℝ) =
        (Z.N T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

/-- Concrete `atD` specialization with all local scalar comparisons
discharged by `packedCoreFour_atD_local_energy`. -/
theorem seamA_mult2_atD_with_wider_explicit_gain
    (Z : ZeroConfig) {T : ℝ} {P : Params} (hP : P.Valid)
    (hconj : PhiHatConj T (P.atD T))
    (hreal : PhiHatReal T (P.atD T))
    (hPois : PoissonSq T (P.atD T))
    (hF : PrimeSide.LocalHypsCoreW (ThmD.cDT P.ϱ P.lam)
      ((P.atD T).toSetting T) ((P.atD T).localFun T))
    {θ₀ : ℝ} (hTl : Assembly.TailInputs Z (P.atD T) T θ₀)
    (hT : 0 < T)
    (hc : 0 < (P.atD T).a T * (P.atD T).L T ^ 2)
    (hbudget :
      coreTailBudget (ThmD.cDT P.ϱ P.lam) ((P.atD T).toSetting T) 3 <
        (P.atD T).a T * (P.atD T).L T ^ 2)
    (hwL : 16 * P.w ≤ P.L T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 (P.atD T) hconj z)
    [Nonempty (CoreSimpleLabel Z T 3)]
    (hdelta : 0 ≤ widerAtDLocalDelta T P) :
    4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
        frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
        2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ) -
        θ₀ / ((P.atD T).a T * (P.atD T).L T) *
          (4 + 2 * Real.sqrt
              (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
            θ₀ / ((P.atD T).a T * (P.atD T).L T)) +
        widerAtDLocalDelta T P /
            (8 * (Fintype.card (CoreSimpleLabel Z T 3) : ℝ)) *
          max 0 ((Fintype.card (CoreSimpleLabel Z T 3) : ℝ) -
            coreBinD T (P.atD T) / 2 - 3) ^ 2
      ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3 := by
  have hLD : 0 < (P.atD T).L T := by
    simpa using (show 0 < P.L T by linarith [hP.one_le_w])
  have haD : 0 < (P.atD T).a T := by
    have hs : 0 ≤ (P.atD T).L T ^ 2 := sq_nonneg _
    nlinarith
  apply seamA_mult2_with_wider_core_gain Z T (P.atD T)
    hconj hreal hPois hTl haD hLD hT.le hpos hdelta
  intro q
  exact packedCoreFour_atD_local_energy
    Z hP hconj hreal hF hT hc hbudget hwL hpos q

end StrictImprovement
end Zeta23

end
