/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Assembly.SeamMult
import Zeta23.StrictImprovement.Q7SalvagedZetaLocalDefect

/-! # Tail-stable seam with the q6 superbin gain -/

noncomputable section

open Matrix Finset Real RHLinalg
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide

theorem seamA_mult2_with_q7Salvaged_gain
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hconj : PhiHatConj T P) (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P)
    {theta0 : ℝ} (hTl : Assembly.TailInputs Z P T theta0)
    (ha : 0 < P.a T) (hL : 0 < P.L T) (hT : 0 ≤ T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 P hconj z)
    [Nonempty (CoreSimpleLabel Z T 3)]
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hlocal : ∀ q : Q7SalvagedBlock
      (coreQ6HalfBinEnumeration Z T 3 P hL (by norm_num)),
      2 * (scale * q7SalvagedBlockReward q) ≤ Tail.traceNorm
        ((gramDeviation_isHermitian
          (normalizedCoreVec Z T 3 P hconj)).submatrix
            (q7SalvagedBlockIndex
              (coreQ6HalfBinEnumeration Z T 3 P hL (by norm_num)) q))) :
    4 * rtrace (P.hat T (Z.Gz P T)) -
        frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ) -
        3 * (Assembly.NII Z T : ℝ) -
        theta0 / (P.a T * P.L T) *
          (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) +
            theta0 / (P.a T * P.L T)) +
        scale ^ 2 * wideRepairAlpha ^ 2 /
          (Fintype.card (CoreSimpleLabel Z T 3) : ℝ) *
          max 0 ((Fintype.card (CoreSimpleLabel Z T 3) : ℝ) -
            q7SalvagedPackingLoss * coreBinD T P -
            q7SalvagedPackingIntercept) ^ 2
      ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3 := by
  obtain ⟨B, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) =
      P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← Assembly.hat_add]
    congr 1
    simp [ZeroConfig.Ez]
  have hB0' : 0 ≤ theta0 / (P.a T * P.L T) :=
    div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_mult2_with_q7Salvaged_gain
    Z T P hconj hreal hPois (by positivity) hL hT hpos hscale hlocal
  have hpert := Assembly.ctr_sub_frobSq_perturb
    4 (by norm_num) hGAE hB0' (htrE.trans hBle)
      (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤
      (Z.N0s T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) =
      (Z.N T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

end StrictImprovement
end Zeta23

end
