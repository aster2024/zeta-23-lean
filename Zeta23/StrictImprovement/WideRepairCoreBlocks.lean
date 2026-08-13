/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WideRepairMixedPacking
import Zeta23.StrictImprovement.ZetaFiniteCorrelation
import Zeta23.StrictImprovement.CoreTripleEnergy

/-!
# Finite/full transfer for every selected mixed block

This module connects the three explicit endpoint certificates to a finite
normalized core Gram matrix.  A single full-kernel comparison is shared by
all block orders; the dimension-dependent trace-norm losses remain explicit.
-/

noncomputable section

open Real Finset Matrix
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

variable (Z : ZeroConfig) (T : ℝ) (P : Params)
variable (hconj : PhiHatConj T P)

private abbrev p : PrimeSide.Setting := P.toSetting T
private abbrev F : PrimeSide.LocalFun := P.localFun T
private abbrev mass : ℝ := P.a T * P.L T ^ 2

/-- Every selected order-three, order-four, or order-five block inherits its
scaled endpoint reward. -/
theorem packedCoreWideRepairBlock_traceNorm_lower
    (hcertificates : WideRepairEndpointCertificates)
    (cRho : ℝ)
    (hreal : PhiHatReal T P)
    (hF : PrimeSide.LocalHypsCoreW cRho (p T P) (F T P))
    (hT : 0 < T) (hc : 0 < mass T P)
    (hbudget : coreTailBudget cRho (p T P) 3 < mass T P)
    (hL : 0 < P.L T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 P hconj z)
    {epsFull scale : ℝ} (hepsFull : 0 ≤ epsFull)
    (hfull : ∀ z z' : CoreSimpleLabel Z T 3,
      |fullCoreCorrelation Z T P z z' -
        endpointR (coreScaledOrdinate Z T 3 P z -
          coreScaledOrdinate Z T 3 P z')| ≤ epsFull)
    (hmargin3 : scale * wideRepairRewardThree +
        (3 * Real.sqrt 3 / 2) *
          localCorrelationError T P cRho epsFull ≤ wideRepairRewardThree)
    (hmargin4 : scale * wideRepairRewardFour +
        2 * Real.sqrt 3 *
          localCorrelationError T P cRho epsFull ≤ wideRepairRewardFour)
    (hmargin5 : scale * wideRepairRewardFive +
        (5 * Real.sqrt 5 / 2) *
          localCorrelationError T P cRho epsFull ≤ wideRepairRewardFive)
    (q : WideRepairBlock
      (coreWideRepairEnumeration Z T 3 P hL (by norm_num))) :
    2 * (scale * wideRepairBlockReward q) ≤
      Tail.traceNorm
        ((gramDeviation_isHermitian
          (normalizedCoreVec Z T 3 P hconj)).submatrix
            (wideRepairBlockIndex
              (coreWideRepairEnumeration Z T 3 P hL (by norm_num)) q)) := by
  let E := coreWideRepairEnumeration Z T 3 P hL (by norm_num)
  let idx := wideRepairBlockIndex E q
  let x := normalizedCoreVec Z T 3 P hconj
  let coord : Fin (wideRepairBlockSize q) → ℝ :=
    fun r => coreScaledOrdinate Z T 3 P (idx r)
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
  have hclose : ∀ z z' : CoreSimpleLabel Z T 3,
      |finiteNormalizedCoreCorrelation Z T P hconj z z' -
        endpointR (coreScaledOrdinate Z T 3 P z -
          coreScaledOrdinate Z T 3 P z')| ≤ eps := by
    intro z z'
    have hfin := finiteNormalizedCoreCorrelation_close_full
      Z T P hconj hreal hF hT hc hbudget z z'
    change |finiteNormalizedCoreCorrelation Z T P hconj z z' -
        fullCoreCorrelation Z T P z z'| ≤ epsFin at hfin
    have hlim := hfull z z'
    dsimp [eps, epsFin]
    calc
      |finiteNormalizedCoreCorrelation Z T P hconj z z' -
          endpointR (coreScaledOrdinate Z T 3 P z -
            coreScaledOrdinate Z T 3 P z')| ≤
          |finiteNormalizedCoreCorrelation Z T P hconj z z' -
            fullCoreCorrelation Z T P z z'| +
          |fullCoreCorrelation Z T P z z' -
            endpointR (coreScaledOrdinate Z T 3 P z -
              coreScaledOrdinate Z T 3 P z')| := abs_sub_le _ _ _
      _ ≤ epsFin + epsFull := add_le_add hfin hlim
      _ = epsFull + epsFin := add_comm _ _
  have hunit : ∀ z, ∑ k, ‖x z k‖ ^ 2 = 1 := by
    intro z
    dsimp [x]
    exact normalizedCoreVec_isUnit Z T 3 P hconj hpos z
  have hlocalNe : ∀ {r t : Fin (wideRepairBlockSize q)},
      r ≠ t → idx r ≠ idx t := by
    intro r t hrt heq
    have hp : (⟨q, r⟩ : Σ q, Fin (wideRepairBlockSize q)) = ⟨q, t⟩ :=
      (wideRepairBlockIndex_injective E) heq
    have hrt' : r = t := by
      cases hp
      rfl
    exact hrt hrt'
  let hB := (gramDeviation_isHermitian x).submatrix idx
  have hdiagB : ∀ r, (gramDeviation x).submatrix idx idx r r = 0 := by
    intro r
    exact gramDeviation_diag_zero x hunit (idx r)
  have hedge : ∀ {r t : Fin (wideRepairBlockSize q)}, r ≠ t →
      ‖(gramDeviation x).submatrix idx idx r t -
          wideEndpointDeviation coord r t‖ ≤ eps := by
    intro r t hrt
    rw [Matrix.submatrix_apply, gramDeviation_offdiag x (hlocalNe hrt),
      wideEndpointDeviation_offdiag coord hrt,
      gramMatrix_normalizedCoreVec_eq_finiteCorrelation
        Z T P hconj hreal hc hpos (idx r) (idx t)]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hclose (idx r) (idx t)
  have hedgeAll : ∀ r t : Fin (wideRepairBlockSize q),
      ‖(gramDeviation x).submatrix idx idx r t -
          wideEndpointDeviation coord r t‖ ≤ eps := by
    intro r t
    by_cases hrt : r = t
    · subst t
      rw [hdiagB r, wideEndpointDeviation_diag coord r]
      simp [heps]
    · exact hedge hrt
  have hdiam : ∀ r t : Fin (wideRepairBlockSize q),
      |coord r - coord t| < 16 * Real.pi := by
    intro r t
    cases q with
    | inl q =>
        exact coreWideRepairEntry_pair_distance_lt Z T 3 P hL
          (by norm_num) q.1
          (wideRepairFiveSlot (E.occupancy q.1) q.2 r)
          (wideRepairFiveSlot (E.occupancy q.1) q.2 t)
    | inr q =>
        cases q with
        | inl q =>
            exact coreWideRepairEntry_pair_distance_lt Z T 3 P hL
              (by norm_num) q.1
              (wideRepairResidualSlot (E.occupancy q.1) 3
                (wideRepairThreeResidue_mod q) r)
              (wideRepairResidualSlot (E.occupancy q.1) 3
                (wideRepairThreeResidue_mod q) t)
        | inr q =>
            exact coreWideRepairEntry_pair_distance_lt Z T 3 P hL
              (by norm_num) q.1
              (wideRepairResidualSlot (E.occupancy q.1) 4
                (wideRepairFourResidue_mod q) r)
              (wideRepairResidualSlot (E.occupancy q.1) 4
                (wideRepairFourResidue_mod q) t)
  have hdiamRat : ∀ r t : Fin (wideRepairBlockSize q),
      |coord r - coord t| ≤ (352 : ℝ) / 7 := by
    intro r t
    have hpi := Real.pi_lt_d4
    have hwide := hdiam r t
    nlinarith
  cases q with
  | inl q =>
      apply wideRepairFive_nearby_traceNorm_lower hcertificates.five
        coord (fun i j => (hdiam i j).le) hB heps hedgeAll
      simpa [eps, epsFin, localCorrelationError] using hmargin5
  | inr q =>
      cases q with
      | inl q =>
          apply wideRepairThree_nearby_traceNorm_lower hcertificates.three
            coord hdiamRat hB heps hedgeAll
          simpa [eps, epsFin, localCorrelationError] using hmargin3
      | inr q =>
          apply wideRepairFour_nearby_traceNorm_lower hcertificates.four
            coord hdiamRat hB hdiagB heps
          · simpa [eps, epsFin, localCorrelationError] using hmargin4
          · simpa [wideEndpointDeviation, endpointFourDeviation] using
              hedge (by omega : (0 : Fin 4) ≠ 1)
          · simpa [wideEndpointDeviation, endpointFourDeviation] using
              hedge (by omega : (0 : Fin 4) ≠ 2)
          · simpa [wideEndpointDeviation, endpointFourDeviation] using
              hedge (by omega : (0 : Fin 4) ≠ 3)
          · simpa [wideEndpointDeviation, endpointFourDeviation] using
              hedge (by omega : (1 : Fin 4) ≠ 2)
          · simpa [wideEndpointDeviation, endpointFourDeviation] using
              hedge (by omega : (1 : Fin 4) ≠ 3)
          · simpa [wideEndpointDeviation, endpointFourDeviation] using
              hedge (by omega : (2 : Fin 4) ≠ 3)

end StrictImprovement
end Zeta23

end
