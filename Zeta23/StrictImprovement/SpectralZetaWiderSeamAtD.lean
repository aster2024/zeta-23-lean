/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.SpectralZetaWiderAtD
import Zeta23.StrictImprovement.SpectralZetaWiderSeamDefect

/-!
# Concrete fixed-height seam with spectral four-point gain
-/

noncomputable section

open Matrix Finset Real RHLinalg
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide

/-- Concrete `atD` seam for any nonnegative spectral mass whose square-root
margin absorbs the finite/full correlation error. -/
theorem seamA_mult2_atD_with_spectral_explicit_gain
    (hcertificate : SpectralFourEndpointCertificate)
    (Z : ZeroConfig) {T : ℝ} {P : Params} (hP : P.Valid)
    (hconj : PhiHatConj T (P.atD T))
    (hreal : PhiHatReal T (P.atD T))
    (hPois : PoissonSq T (P.atD T))
    (hF : PrimeSide.LocalHypsCoreW (ThmD.cDT P.ϱ P.lam)
      ((P.atD T).toSetting T) ((P.atD T).localFun T))
    {theta0 : ℝ} (hTl : Assembly.TailInputs Z (P.atD T) T theta0)
    (hT : 0 < T)
    (hc : 0 < (P.atD T).a T * (P.atD T).L T ^ 2)
    (hbudget :
      coreTailBudget (ThmD.cDT P.ϱ P.lam) ((P.atD T).toSetting T) 3 <
        (P.atD T).a T * (P.atD T).L T ^ 2)
    (hwL : 16 * P.w ≤ P.L T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 (P.atD T) hconj z)
    [Nonempty (CoreSimpleLabel Z T 3)]
    {m : ℝ} (hm : 0 ≤ m)
    (hmargin : Real.sqrt m + 2 * Real.sqrt 3 *
        localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
          (12 * P.w / P.L T + 3 * (1 - P.lam)) ≤
      Real.sqrt spectralFourMassLower) :
    4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
        frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
        2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ) -
        theta0 / ((P.atD T).a T * (P.atD T).L T) *
          (4 + 2 * Real.sqrt
              (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
            theta0 / ((P.atD T).a T * (P.atD T).L T)) +
        m / (16 * (Fintype.card (CoreSimpleLabel Z T 3) : ℝ)) *
          max 0 ((Fintype.card (CoreSimpleLabel Z T 3) : ℝ) -
            coreBinD T (P.atD T) / 2 - 3) ^ 2
      ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3 := by
  have hLD : 0 < (P.atD T).L T := by
    simpa using (show 0 < P.L T by linarith [hP.one_le_w])
  have haD : 0 < (P.atD T).a T := by
    have hs : 0 ≤ (P.atD T).L T ^ 2 := sq_nonneg _
    nlinarith
  apply seamA_mult2_with_spectral_core_gain Z T (P.atD T)
    hconj hreal hPois hTl haD hLD hT.le hpos hm
  intro q
  exact packedCoreFour_atD_spectral_local_traceNorm
    hcertificate Z hP hconj hreal hF hT hc hbudget hwL hpos hm hmargin q

end StrictImprovement
end Zeta23

end
