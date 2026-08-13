/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.SpectralFourPointInterface
import Zeta23.StrictImprovement.CoreFourEnergy

/-!
# Spectral endpoint certificate on every packed finite core four-tuple

This is the analytic-to-linear-algebra seam missing from the first spectral
draft.  The interval certificate remains an explicit argument.  The theorem
combines the already formalized finite/full correlation comparison with the
new trace-norm perturbation lemma, rather than reusing the unrelated
six-squared-edge energy stability statement.
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

/-- A packed finite core block inherits a spectral trace-norm mass `m` once
the square-root margin absorbs the full finite/full correlation error. -/
theorem packedCoreFour_spectral_traceNorm_lower
    (hcertificate : SpectralFourEndpointCertificate)
    (cRho : ℝ)
    (hreal : PhiHatReal T P)
    (hF : PrimeSide.LocalHypsCoreW cRho (p T P) (F T P))
    (hT : 0 < T) (hc : 0 < mass T P)
    (hbudget : coreTailBudget cRho (p T P) 3 < mass T P)
    (hL : 0 < P.L T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 P hconj z)
    {epsFull m : ℝ} (hepsFull : 0 ≤ epsFull) (hm : 0 ≤ m)
    (hfull : ∀ z z' : CoreSimpleLabel Z T 3,
      |fullCoreCorrelation Z T P z z' -
        endpointR (coreScaledOrdinate Z T 3 P z -
          coreScaledOrdinate Z T 3 P z')| ≤ epsFull)
    (hmargin : Real.sqrt m + 2 * Real.sqrt 3 *
        localCorrelationError T P cRho epsFull ≤
      Real.sqrt spectralFourMassLower)
    (q : PackedFour (coreWidthSixEnumeration Z T 3 P hL (by norm_num))) :
    2 * Real.sqrt m ≤
      Tail.traceNorm
        ((gramDeviation_isHermitian
          (normalizedCoreVec Z T 3 P hconj)).submatrix
            (packedFourIndex
              (coreWidthSixEnumeration Z T 3 P hL (by norm_num)) q)) := by
  let E := coreWidthSixEnumeration Z T 3 P hL (by norm_num)
  let idx := packedFourIndex E q
  let x := normalizedCoreVec Z T 3 P hconj
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
  have hunit : ∀ z, ∑ k, ‖x z k‖ ^ 2 = 1 := by
    intro z
    dsimp [x]
    exact normalizedCoreVec_isUnit Z T 3 P hconj hpos z
  have hlocalNe : ∀ {r t : Fin 4}, r ≠ t → idx r ≠ idx t := by
    intro r t hrt hEq
    have hp : (q, r) = (q, t) := (packedFourIndex_injective E) hEq
    exact hrt (congrArg Prod.snd hp)
  let hB := (gramDeviation_isHermitian x).submatrix idx
  have hdiagB : ∀ r, (gramDeviation x).submatrix idx idx r r = 0 := by
    intro r
    exact gramDeviation_diag_zero x hunit (idx r)
  have hedge : ∀ {r t : Fin 4}, r ≠ t →
      ‖(gramDeviation x).submatrix idx idx r t -
          endpointFourDeviation coord r t‖ ≤ eps := by
    intro r t hrt
    rw [Matrix.submatrix_apply, gramDeviation_offdiag x (hlocalNe hrt),
      endpointFourDeviation_offdiag coord hrt,
      gramMatrix_normalizedCoreVec_eq_finiteCorrelation
        Z T P hconj hreal hc hpos (idx r) (idx t)]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hclose r t
  apply spectral_endpoint_to_nearby_traceNorm_lower
    hcertificate coord hdist hB hdiagB heps hm
  · simpa [eps, epsFin, localCorrelationError] using hmargin
  · exact hedge (by decide)
  · exact hedge (by decide)
  · exact hedge (by decide)
  · exact hedge (by decide)
  · exact hedge (by decide)
  · exact hedge (by decide)

end StrictImprovement
end Zeta23

end
