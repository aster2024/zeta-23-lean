/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaFiniteCorrelation
import Zeta23.StrictImprovement.ZetaCoreBinning
import Zeta23.StrictImprovement.ThreeCoordinateEnergy

/-!
# Local energy of every packed zeta-core triple

This module assembles the finite normalization, exact interval bins, and the
unordered endpoint three-point theorem.  Its only remaining analytic input is
a uniform comparison between the full Poisson correlation and `endpointR` on
core pairs.  Under an error `epsFull`, every packed finite Gram triple has
energy at least

`explicitDeltaLower - 6*(epsFull + 2*coreTailBudget/(aL²))`.

Thus the full-kernel/endpoint comparison is exposed as one scalar interface,
not hidden as an asymptotic placeholder.
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

def localCorrelationError (cRho epsFull : ℝ) : ℝ :=
  epsFull + 2 * (coreTailBudget cRho (p T P) 3 / mass T P)

/-- Every canonical packed core triple inherits the endpoint energy, with
exactly the sum of the full-kernel error and the finite-normalization error. -/
theorem packedCoreTriple_local_energy
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
    (q : PackedTriple (coreBinnedEnumeration Z T 3 P hL (by norm_num))) :
    explicitDeltaLower - 6 * localCorrelationError T P cRho epsFull ≤
      tripleCorrelationEnergy (normalizedCoreVec Z T 3 P hconj)
        (packedTripleIndex (coreBinnedEnumeration Z T 3 P hL (by norm_num))) q := by
  let E := coreBinnedEnumeration Z T 3 P hL (by norm_num)
  let idx := packedTripleIndex E q
  let x₀ := coreScaledOrdinate Z T 3 P (idx 0)
  let x₁ := coreScaledOrdinate Z T 3 P (idx 1)
  let x₂ := coreScaledOrdinate Z T 3 P (idx 2)
  let c₀₁ := finiteNormalizedCoreCorrelation Z T P hconj (idx 0) (idx 1)
  let c₀₂ := finiteNormalizedCoreCorrelation Z T P hconj (idx 0) (idx 2)
  let c₁₂ := finiteNormalizedCoreCorrelation Z T P hconj (idx 1) (idx 2)
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
  have hdiam := corePackedTriple_diameter_lt_eight_pi
    Z T 3 P hL (by norm_num) q
  have h01close : |c₀₁ - endpointR (x₀ - x₁)| ≤ eps := by
    have hfin := finiteNormalizedCoreCorrelation_close_full
      Z T P hconj hreal hF hT hc hbudget (idx 0) (idx 1)
    have hlim := hfull (idx 0) (idx 1)
    dsimp [c₀₁, x₀, x₁, eps, epsFin]
    calc
      |finiteNormalizedCoreCorrelation Z T P hconj (idx 0) (idx 1) -
          endpointR (coreScaledOrdinate Z T 3 P (idx 0) -
            coreScaledOrdinate Z T 3 P (idx 1))|
        ≤ |finiteNormalizedCoreCorrelation Z T P hconj (idx 0) (idx 1) -
            fullCoreCorrelation Z T P (idx 0) (idx 1)| +
          |fullCoreCorrelation Z T P (idx 0) (idx 1) -
            endpointR (coreScaledOrdinate Z T 3 P (idx 0) -
              coreScaledOrdinate Z T 3 P (idx 1))| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hfin hlim
  have h02close : |c₀₂ - endpointR (x₀ - x₂)| ≤ eps := by
    have hfin := finiteNormalizedCoreCorrelation_close_full
      Z T P hconj hreal hF hT hc hbudget (idx 0) (idx 2)
    have hlim := hfull (idx 0) (idx 2)
    dsimp [c₀₂, x₀, x₂, eps, epsFin]
    exact (abs_sub_le _ _ _).trans (add_le_add hfin hlim)
  have h12close : |c₁₂ - endpointR (x₁ - x₂)| ≤ eps := by
    have hfin := finiteNormalizedCoreCorrelation_close_full
      Z T P hconj hreal hF hT hc hbudget (idx 1) (idx 2)
    have hlim := hfull (idx 1) (idx 2)
    dsimp [c₁₂, x₁, x₂, eps, epsFin]
    exact (abs_sub_le _ _ _).trans (add_le_add hfin hlim)
  have henergy := threeCoordinateEnergy_stable heps
    hdiam.1.le hdiam.2.1.le hdiam.2.2.le
    (finiteNormalizedCoreCorrelation_abs_le_one
      Z T P hconj hreal hc hpos (idx 0) (idx 1))
    (finiteNormalizedCoreCorrelation_abs_le_one
      Z T P hconj hreal hc hpos (idx 0) (idx 2))
    (finiteNormalizedCoreCorrelation_abs_le_one
      Z T P hconj hreal hc hpos (idx 1) (idx 2))
    h01close h02close h12close
  dsimp [x₀, x₁, x₂, c₀₁, c₀₂, c₁₂] at henergy
  unfold tripleCorrelationEnergy
  rw [gramMatrix_normalizedCoreVec_eq_finiteCorrelation
      Z T P hconj hreal hc hpos (idx 0) (idx 1),
    gramMatrix_normalizedCoreVec_eq_finiteCorrelation
      Z T P hconj hreal hc hpos (idx 0) (idx 2),
    gramMatrix_normalizedCoreVec_eq_finiteCorrelation
      Z T P hconj hreal hc hpos (idx 1) (idx 2)]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa [localCorrelationError, eps, epsFin] using henergy

end StrictImprovement
end Zeta23
