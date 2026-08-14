/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q7FullSpectralLocal
import Zeta23.StrictImprovement.ZetaFiniteCorrelation
import Zeta23.StrictImprovement.CoreTripleEnergy

/-!
# Core geometry and finite/full transfer for full-spectral q7 superbin blocks
-/

noncomputable section

open Real Matrix Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

variable (Z : ZeroConfig) (T C : ℝ) (P : Params)

def coreQ7FullSpectralBlockCoordinate
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (q : Q7FullSpectralBlock (coreQ6HalfBinEnumeration Z T C P hL hC))
    (r : Fin (q7FullSpectralBlockSize q)) : ℝ :=
  coreScaledOrdinate Z T C P
      (q7FullSpectralBlockIndex
        (coreQ6HalfBinEnumeration Z T C P hL hC) q r) -
    (coreBinBase T C P + (q.1.1.val : ℝ) * (32 * Real.pi))

private lemma abs_sub_le_sixteen_of_left_bounds
    {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 16 * Real.pi)
    (hy : 0 ≤ y ∧ y ≤ 16 * Real.pi) :
    |x - y| ≤ 16 * Real.pi := by
  rw [abs_le]
  constructor <;> nlinarith

private lemma abs_sub_le_sixteen_of_right_bounds
    {x y : ℝ} (hx : 16 * Real.pi ≤ x ∧ x ≤ 32 * Real.pi)
    (hy : 16 * Real.pi ≤ y ∧ y ≤ 32 * Real.pi) :
    |x - y| ≤ 16 * Real.pi := by
  rw [abs_le]
  constructor <;> nlinarith

private lemma q7_condition_of_fin_ite
    {p : Prop} [Decidable p] (u : Fin (if p then 1 else 0)) : p := by
  by_contra hp
  have hlt := u.isLt
  simp [hp] at hlt

theorem coreQ7FullSpectralBlock_geometry
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (q : Q7FullSpectralBlock (coreQ6HalfBinEnumeration Z T C P hL hC)) :
    Q7FullSpectralBlockGeometry q
      (coreQ7FullSpectralBlockCoordinate Z T C P hL hC q) := by
  let E := coreQ6HalfBinEnumeration Z T C P hL hC
  rcases q with ⟨⟨b, kind⟩, u⟩
  cases kind with
  | fiveLeft =>
      intro i j
      have hi := coreQ6LeftEntry_bounds Z T C P hL hC b
        (wideRepairFiveSlot (q7FullSpectralLeftOccupancy E b) u i)
      have hj := coreQ6LeftEntry_bounds Z T C P hL hC b
        (wideRepairFiveSlot (q7FullSpectralLeftOccupancy E b) u j)
      exact abs_sub_le_sixteen_of_left_bounds hi hj
  | fiveRight =>
      intro i j
      have hi := coreQ6RightEntry_bounds Z T C P hL hC b
        (wideRepairFiveSlot (q7FullSpectralRightOccupancy E b) u i)
      have hj := coreQ6RightEntry_bounds Z T C P hL hC b
        (wideRepairFiveSlot (q7FullSpectralRightOccupancy E b) u j)
      exact abs_sub_le_sixteen_of_right_bounds hi hj
  | threeLeft =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 3 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 4 :=
        q7_condition_of_fin_ite u
      intro i j
      have hi := coreQ6LeftEntry_bounds Z T C P hL hC b
        (wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 3 hcond.1 i)
      have hj := coreQ6LeftEntry_bounds Z T C P hL hC b
        (wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 3 hcond.1 j)
      exact abs_sub_le_sixteen_of_left_bounds hi hj
  | threeRight =>
      have hcond : q7FullSpectralRightOccupancy E b % 5 = 3 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 3 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 4 :=
        q7_condition_of_fin_ite u
      intro i j
      have hi := coreQ6RightEntry_bounds Z T C P hL hC b
        (wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 3 hcond.1 i)
      have hj := coreQ6RightEntry_bounds Z T C P hL hC b
        (wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 3 hcond.1 j)
      exact abs_sub_le_sixteen_of_right_bounds hi hj
  | fourLeft =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 ≠ 3 :=
        q7_condition_of_fin_ite u
      intro i j
      have hi := coreQ6LeftEntry_bounds Z T C P hL hC b
        (wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 4 hcond.1 i)
      have hj := coreQ6LeftEntry_bounds Z T C P hL hC b
        (wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 4 hcond.1 j)
      exact abs_sub_le_sixteen_of_left_bounds hi hj
  | fourRight =>
      have hcond : q7FullSpectralRightOccupancy E b % 5 = 4 ∧
          q7FullSpectralLeftOccupancy E b % 5 ≠ 3 :=
        q7_condition_of_fin_ite u
      intro i j
      have hi := coreQ6RightEntry_bounds Z T C P hL hC b
        (wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 4 hcond.1 i)
      have hj := coreQ6RightEntry_bounds Z T C P hL hC b
        (wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 4 hcond.1 j)
      exact abs_sub_le_sixteen_of_right_bounds hi hj
  | six =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 :=
        q7_condition_of_fin_ite u
      constructor
      · intro i hi
        have hidx :
            q7FullSpectralBlockIndex E ⟨⟨b, .six⟩, u⟩ i =
              E.entry (b, 0)
                (wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 3
                  hcond.1 ⟨i.val, hi⟩) := by
          dsimp only [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate, id]
          rw [dif_pos hi]
        dsimp only [coreQ7FullSpectralBlockCoordinate]
        rw [hidx]
        have hb := coreQ6LeftEntry_bounds Z T C P hL hC b
          (wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 3
            hcond.1 ⟨i.val, hi⟩)
        constructor <;> nlinarith [hb.1, hb.2]
      · intro i hi
        have hnot : ¬ i.val < 3 := by omega
        have hi6 : i.val < 6 := by
          simpa [q7FullSpectralBlockSize, q7FullSpectralBlockKindSize] using i.isLt
        have hiright : i.val - 3 < 3 := by omega
        have hidx :
            q7FullSpectralBlockIndex E ⟨⟨b, .six⟩, u⟩ i =
              E.entry (b, 1)
                (wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 3
                  hcond.2 ⟨i.val - 3, hiright⟩) := by
          dsimp only [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate, id]
          rw [dif_neg hnot]
        dsimp only [coreQ7FullSpectralBlockCoordinate]
        rw [hidx]
        have hb := coreQ6RightEntry_bounds Z T C P hL hC b
          (wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 3
            hcond.2 ⟨i.val - 3, hiright⟩)
        constructor <;> nlinarith [hb.1, hb.2]
  | sevenThreeFour =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 3 ∧
          q7FullSpectralRightOccupancy E b % 5 = 4 :=
        q7_condition_of_fin_ite u
      constructor
      · intro i hi
        have hidx :
            q7FullSpectralBlockIndex E ⟨⟨b, .sevenThreeFour⟩, u⟩ i =
              E.entry (b, 0)
                (wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 3
                  hcond.1 ⟨i.val, hi⟩) := by
          dsimp only [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate, id]
          rw [dif_pos hi]
        dsimp only [coreQ7FullSpectralBlockCoordinate]
        rw [hidx]
        have hb := coreQ6LeftEntry_bounds Z T C P hL hC b
          (wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 3
            hcond.1 ⟨i.val, hi⟩)
        constructor <;> nlinarith [hb.1, hb.2]
      · intro i hi
        have hnot : ¬ i.val < 3 := by omega
        have hi7 : i.val < 7 := by
          simpa [q7FullSpectralBlockSize, q7FullSpectralBlockKindSize] using i.isLt
        have hiright : i.val - 3 < 4 := by omega
        have hidx :
            q7FullSpectralBlockIndex E ⟨⟨b, .sevenThreeFour⟩, u⟩ i =
              E.entry (b, 1)
                (wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 4
                  hcond.2 ⟨i.val - 3, hiright⟩) := by
          dsimp only [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate, id]
          rw [dif_neg hnot]
        dsimp only [coreQ7FullSpectralBlockCoordinate]
        rw [hidx]
        have hb := coreQ6RightEntry_bounds Z T C P hL hC b
          (wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 4
            hcond.2 ⟨i.val - 3, hiright⟩)
        constructor <;> nlinarith [hb.1, hb.2]
  | sevenFourThree =>
      have hcond : q7FullSpectralLeftOccupancy E b % 5 = 4 ∧
          q7FullSpectralRightOccupancy E b % 5 = 3 :=
        q7_condition_of_fin_ite u
      constructor
      · intro i hi
        have hidx :
            q7FullSpectralBlockIndex E ⟨⟨b, .sevenFourThree⟩, u⟩ i =
              E.entry (b, 0)
                (wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 4
                  hcond.1 ⟨i.val, hi⟩) := by
          dsimp only [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate, id]
          rw [dif_pos hi]
        dsimp only [coreQ7FullSpectralBlockCoordinate]
        rw [hidx]
        have hb := coreQ6LeftEntry_bounds Z T C P hL hC b
          (wideRepairResidualSlot (q7FullSpectralLeftOccupancy E b) 4
            hcond.1 ⟨i.val, hi⟩)
        constructor <;> nlinarith [hb.1, hb.2]
      · intro i hi
        have hnot : ¬ i.val < 4 := by omega
        have hi7 : i.val < 7 := by
          simpa [q7FullSpectralBlockSize, q7FullSpectralBlockKindSize] using i.isLt
        have hiright : i.val - 4 < 3 := by omega
        have hidx :
            q7FullSpectralBlockIndex E ⟨⟨b, .sevenFourThree⟩, u⟩ i =
              E.entry (b, 1)
                (wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 3
                  hcond.2 ⟨i.val - 4, hiright⟩) := by
          dsimp only [q7FullSpectralBlockIndex, q7FullSpectralBlockCoordinate, id]
          rw [dif_neg hnot]
        dsimp only [coreQ7FullSpectralBlockCoordinate]
        rw [hidx]
        have hb := coreQ6RightEntry_bounds Z T C P hL hC b
          (wideRepairResidualSlot (q7FullSpectralRightOccupancy E b) 3
            hcond.2 ⟨i.val - 4, hiright⟩)
        constructor <;> nlinarith [hb.1, hb.2]

private abbrev q6p (T : ℝ) (P : Params) : PrimeSide.Setting :=
  P.toSetting T

private abbrev q6F (T : ℝ) (P : Params) : PrimeSide.LocalFun :=
  P.localFun T

private abbrev q6mass (T : ℝ) (P : Params) : ℝ :=
  P.a T * P.L T ^ 2

/-- Every concrete q7 inventory block inherits its scaled endpoint reward. -/
theorem packedCoreQ7FullSpectralBlock_traceNorm_lower
    (hcertificates : Q7FullSpectralEndpointCertificates)
    (cRho : ℝ)
    (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P)
    (hF : PrimeSide.LocalHypsCoreW cRho (q6p T P) (q6F T P))
    (hT : 0 < T) (hc : 0 < q6mass T P)
    (hbudget : coreTailBudget cRho (q6p T P) 3 < q6mass T P)
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
    (hmargin6 : scale * q7FullSpectralSixReward +
        3 * Real.sqrt 6 *
          localCorrelationError T P cRho epsFull ≤ q7FullSpectralSixReward)
    (hmargin7 : scale * q7FullSpectralSevenReward +
        (7 * Real.sqrt 7 / 2) *
          localCorrelationError T P cRho epsFull ≤ q7FullSpectralSevenReward)
    (q : Q7FullSpectralBlock
      (coreQ6HalfBinEnumeration Z T 3 P hL (by norm_num))) :
    2 * (scale * q7FullSpectralBlockReward q) ≤
      Tail.traceNorm
        ((gramDeviation_isHermitian
          (normalizedCoreVec Z T 3 P hconj)).submatrix
            (q7FullSpectralBlockIndex
              (coreQ6HalfBinEnumeration Z T 3 P hL (by norm_num)) q)) := by
  classical
  let E := coreQ6HalfBinEnumeration Z T 3 P hL (by norm_num)
  let idx := q7FullSpectralBlockIndex E q
  let x := normalizedCoreVec Z T 3 P hconj
  let coord := coreQ7FullSpectralBlockCoordinate Z T 3 P hL (by norm_num) q
  let epsFin := 2 * (coreTailBudget cRho (q6p T P) 3 / q6mass T P)
  let eps := epsFull + epsFin
  have hbudget0 : 0 ≤ coreTailBudget cRho (q6p T P) 3 := by
    unfold coreTailBudget
    have hh : 0 ≤ (q6p T P).h⁻¹ := inv_nonneg.mpr (PrimeSide.h_pos hF).le
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
  have hlocalNe : ∀ {r t : Fin (q7FullSpectralBlockSize q)},
      r ≠ t → idx r ≠ idx t := by
    intro r t hrt heq
    have hp : (⟨q, r⟩ : Σ q, Fin (q7FullSpectralBlockSize q)) = ⟨q, t⟩ :=
      (q7FullSpectralBlockIndex_injective E) heq
    have hrt' : r = t := by
      cases hp
      rfl
    exact hrt hrt'
  let hB := (gramDeviation_isHermitian x).submatrix idx
  have hdiagB : ∀ r, (gramDeviation x).submatrix idx idx r r = 0 := by
    intro r
    exact gramDeviation_diag_zero x hunit (idx r)
  have hcloseCoord : ∀ r t : Fin (q7FullSpectralBlockSize q),
      |finiteNormalizedCoreCorrelation Z T P hconj (idx r) (idx t) -
        endpointR (coord r - coord t)| ≤ eps := by
    intro r t
    have h := hclose (idx r) (idx t)
    have harg : coord r - coord t =
        coreScaledOrdinate Z T 3 P (idx r) -
          coreScaledOrdinate Z T 3 P (idx t) := by
      dsimp [coord, idx, coreQ7FullSpectralBlockCoordinate]
      ring
    rw [harg]
    exact h
  have hedgeAll : ∀ r t : Fin (q7FullSpectralBlockSize q),
      ‖(gramDeviation x).submatrix idx idx r t -
          wideEndpointDeviation coord r t‖ ≤ eps := by
    intro r t
    by_cases hrt : r = t
    · subst t
      rw [hdiagB r, wideEndpointDeviation_diag coord r]
      simp [heps]
    · rw [Matrix.submatrix_apply, gramDeviation_offdiag x (hlocalNe hrt),
        wideEndpointDeviation_offdiag coord hrt,
        gramMatrix_normalizedCoreVec_eq_finiteCorrelation
          Z T P hconj hreal hc hpos (idx r) (idx t)]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hcloseCoord r t
  apply q7FullSpectralBlock_nearby_traceNorm_lower hcertificates q coord
    (coreQ7FullSpectralBlock_geometry Z T 3 P hL (by norm_num) q)
    hB hdiagB heps hedgeAll
  · simpa [eps, epsFin, localCorrelationError] using hmargin3
  · simpa [eps, epsFin, localCorrelationError] using hmargin4
  · simpa [eps, epsFin, localCorrelationError] using hmargin5
  · simpa [eps, epsFin, localCorrelationError] using hmargin6
  · simpa [eps, epsFin, localCorrelationError] using hmargin7

end StrictImprovement
end Zeta23

end
