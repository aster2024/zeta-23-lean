/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WidthSixBinning
import Zeta23.StrictImprovement.WiderThreeCoordinateEnergy
import Zeta23.StrictImprovement.CoreTripleEnergy

/-!
# Local energy of every packed width-six core four-tuple

All six finite Gram correlations are compared with the endpoint kernel.  The
four three-coordinate subsets each inherit the wider endpoint energy; summing
them counts every edge twice and gives the exact local hypothesis required by
`FourBlockDefect.lean`.
-/

noncomputable section

open Real Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

variable (Z : ZeroConfig) (T : ℝ) (P : Params)
variable (hconj : PhiHatConj T P)

private abbrev p : PrimeSide.Setting := P.toSetting T
private abbrev F : PrimeSide.LocalFun := P.localFun T
private abbrev mass : ℝ := P.a T * P.L T ^ 2

theorem packedCoreFour_local_energy
    (cRho : ℝ)
    (hreal : PhiHatReal T P)
    (hF : PrimeSide.LocalHypsCoreW cRho (p T P) (F T P))
    (hT : 0 < T) (hc : 0 < mass T P)
    (hbudget : coreTailBudget cRho (p T P) 3 < mass T P)
    (hL : 0 < P.L T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 P hconj z)
    {epsFull : ℝ} (hepsFull : 0 ≤ epsFull)
    (hfull : ∀ z z' : CoreSimpleLabel Z T 3,
      |fullCoreCorrelation Z T P z z' -
        endpointR (coreScaledOrdinate Z T 3 P z -
          coreScaledOrdinate Z T 3 P z')| ≤ epsFull)
    (q : PackedFour (coreWidthSixEnumeration Z T 3 P hL (by norm_num))) :
    2 * (widerDeltaLower - 6 * localCorrelationError T P cRho epsFull) ≤
      fourCorrelationEnergy (normalizedCoreVec Z T 3 P hconj)
        (packedFourIndex (coreWidthSixEnumeration Z T 3 P hL (by norm_num))) q := by
  let E := coreWidthSixEnumeration Z T 3 P hL (by norm_num)
  let idx := packedFourIndex E q
  let coord : Fin 4 → ℝ := fun r => coreScaledOrdinate Z T 3 P (idx r)
  let corr : Fin 4 → Fin 4 → ℝ := fun r t =>
    finiteNormalizedCoreCorrelation Z T P hconj (idx r) (idx t)
  let epsFin := 2 * (coreTailBudget cRho (p T P) 3 / mass T P)
  let eps := epsFull + epsFin
  have hbudget0 : 0 ≤ coreTailBudget cRho (p T P) 3 := by
    unfold coreTailBudget
    have hh : 0 ≤ (p T P).h⁻¹ := inv_nonneg.mpr (PrimeSide.h_pos hF).le
    positivity
  have hepsFin : 0 ≤ epsFin := by
    dsimp [epsFin]
    positivity
  have heps : 0 ≤ eps := add_nonneg hepsFull hepsFin
  have hdist : ∀ r t : Fin 4,
      |coord r - coord t| ≤ 12 * Real.pi := by
    intro r t
    exact (corePackedFour_pair_distance_lt_twelve_pi
      Z T 3 P hL (by norm_num) q r t).le
  have habs : ∀ r t : Fin 4, |corr r t| ≤ 1 := by
    intro r t
    exact finiteNormalizedCoreCorrelation_abs_le_one
      Z T P hconj hreal hc hpos (idx r) (idx t)
  have hclose : ∀ r t : Fin 4,
      |corr r t - endpointR (coord r - coord t)| ≤ eps := by
    intro r t
    have hfin := finiteNormalizedCoreCorrelation_close_full
      Z T P hconj hreal hF hT hc hbudget (idx r) (idx t)
    change |finiteNormalizedCoreCorrelation Z T P hconj (idx r) (idx t) -
        fullCoreCorrelation Z T P (idx r) (idx t)| ≤ epsFin at hfin
    have hlim := hfull (idx r) (idx t)
    dsimp [corr, coord, eps, epsFin]
    calc
      |finiteNormalizedCoreCorrelation Z T P hconj (idx r) (idx t) -
          endpointR (coreScaledOrdinate Z T 3 P (idx r) -
            coreScaledOrdinate Z T 3 P (idx t))|
        ≤ |finiteNormalizedCoreCorrelation Z T P hconj (idx r) (idx t) -
            fullCoreCorrelation Z T P (idx r) (idx t)| +
          |fullCoreCorrelation Z T P (idx r) (idx t) -
            endpointR (coreScaledOrdinate Z T 3 P (idx r) -
              coreScaledOrdinate Z T 3 P (idx t))| := abs_sub_le _ _ _
      _ ≤ epsFin + epsFull := add_le_add hfin hlim
      _ = _ := by
        dsimp [epsFin]
        ring
  have h012 := wider_threeCoordinateEnergy_stable heps
    (hdist 0 1) (hdist 0 2) (hdist 1 2)
    (habs 0 1) (habs 0 2) (habs 1 2)
    (hclose 0 1) (hclose 0 2) (hclose 1 2)
  have h013 := wider_threeCoordinateEnergy_stable heps
    (hdist 0 1) (hdist 0 3) (hdist 1 3)
    (habs 0 1) (habs 0 3) (habs 1 3)
    (hclose 0 1) (hclose 0 3) (hclose 1 3)
  have h023 := wider_threeCoordinateEnergy_stable heps
    (hdist 0 2) (hdist 0 3) (hdist 2 3)
    (habs 0 2) (habs 0 3) (habs 2 3)
    (hclose 0 2) (hclose 0 3) (hclose 2 3)
  have h123 := wider_threeCoordinateEnergy_stable heps
    (hdist 1 2) (hdist 1 3) (hdist 2 3)
    (habs 1 2) (habs 1 3) (habs 2 3)
    (hclose 1 2) (hclose 1 3) (hclose 2 3)
  unfold threeCoordinateEnergy at h012 h013 h023 h123
  dsimp [corr, coord, eps, epsFin] at h012 h013 h023 h123
  unfold fourCorrelationEnergy
  rw [gramMatrix_normalizedCoreVec_eq_finiteCorrelation
      Z T P hconj hreal hc hpos (idx 0) (idx 1),
    gramMatrix_normalizedCoreVec_eq_finiteCorrelation
      Z T P hconj hreal hc hpos (idx 0) (idx 2),
    gramMatrix_normalizedCoreVec_eq_finiteCorrelation
      Z T P hconj hreal hc hpos (idx 0) (idx 3),
    gramMatrix_normalizedCoreVec_eq_finiteCorrelation
      Z T P hconj hreal hc hpos (idx 1) (idx 2),
    gramMatrix_normalizedCoreVec_eq_finiteCorrelation
      Z T P hconj hreal hc hpos (idx 1) (idx 3),
    gramMatrix_normalizedCoreVec_eq_finiteCorrelation
      Z T P hconj hreal hc hpos (idx 2) (idx 3)]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold localCorrelationError
  nlinarith

end StrictImprovement
end Zeta23

end
