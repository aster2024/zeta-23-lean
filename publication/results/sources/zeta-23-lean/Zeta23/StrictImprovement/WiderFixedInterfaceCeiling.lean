/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WiderFourPointEnergy

/-!
# Exact ceiling for the frozen width-six weighted-Cauchy interface

This module retains the exact rational slope lower bounds before the convenient
rounding in `WiderRootArithmetic`.  It proves a two-sided optimum for the
finite 216-row budget with the already fixed radius and separation floors.

The result is deliberately local: it is not a ceiling for different radii,
stronger analytic slope estimates, larger blocks, or the exact transcendental
endpoint gap.  This remains a source candidate until checked by the pinned
Lean toolchain.
-/

noncomputable section

namespace Zeta23
namespace StrictImprovement

/-- Exact pre-rounding rational slope lower bounds. -/
def widerExactSlope : Fin 6 → ℝ :=
  ![82354251 / 930982144,
    169559355 / 3442403584,
    85588153 / 2513265408,
    343969563 / 13223160064,
    431174667 / 20492495104,
    172793257 / 9782600448]

theorem widerExactSlope_pos (i : Fin 6) :
    0 < widerExactSlope i := by
  fin_cases i <;> norm_num [widerExactSlope]

/-- The displayed vector is exactly the rational derivative expression used
before denominator rounding. -/
theorem widerExactSlope_eq_formula (i : Fin 6) :
    widerExactSlope i =
      (3 / 2 : ℝ) * widerDerivativeLower ((i : ℕ) + 1) /
        ((44 * ((i : ℕ) + 1) : ℝ) / 7 + 21 / 40) ^ 2 := by
  fin_cases i <;>
    norm_num [widerExactSlope, widerDerivativeLower, widerCosLower]

def widerExactSlopeDenominator (i : Fin 6) : ℝ :=
  widerSlopeDenominator i

theorem widerExactSlopeDenominator_eq_inv (i : Fin 6) :
    widerExactSlopeDenominator i = (widerExactSlope i)⁻¹ := by
  fin_cases i <;>
    norm_num [widerExactSlopeDenominator, widerSlopeDenominator,
      widerExactSlope]

theorem widerExactSlopeDenominator_pos (i : Fin 6) :
    0 < widerExactSlopeDenominator i := by
  simpa [widerExactSlopeDenominator] using widerSlopeDenominator_pos i

/-- Exact optimum of the refined 216-row weighted-Cauchy budget. -/
def widerFixedDeltaCeiling : ℝ :=
  widerWeightedBudgetCeiling

theorem widerFixedDeltaCeiling_value :
    widerFixedDeltaCeiling =
      9755468468368320337833317374859207102505001 /
        1623000197669009639771565694101668583197612441600 := by
  rfl

def widerFixedBudget (i j k : Fin 6) : ℝ :=
  widerSeparationFloor i j k ^ 2 /
    (widerExactSlopeDenominator i ^ 2 +
      widerExactSlopeDenominator j ^ 2 +
      widerExactSlopeDenominator k ^ 2)

/-- Complete exact lower bound for all ordered root-index triples. -/
theorem widerFixedDeltaCeiling_le_budget (i j k : Fin 6) :
    widerFixedDeltaCeiling ≤ widerFixedBudget i j k := by
  have hi := widerExactSlopeDenominator_pos i
  have hj := widerExactSlopeDenominator_pos j
  have hk := widerExactSlopeDenominator_pos k
  have hsum : 0 <
      widerExactSlopeDenominator i ^ 2 +
        widerExactSlopeDenominator j ^ 2 +
        widerExactSlopeDenominator k ^ 2 := by
    positivity
  rw [widerFixedBudget]
  apply (le_div_iff₀ hsum).2
  simpa [widerFixedDeltaCeiling, widerExactSlopeDenominator] using
    widerSeparationFloor_budget_ceiling i j k

/-- The `(1,5,6)` row is a matching equality witness (one-based indices). -/
theorem widerFixedBudget_special :
    widerFixedBudget (0 : Fin 6) (4 : Fin 6) (5 : Fin 6) =
      widerFixedDeltaCeiling := by
  have h0 : widerExactSlopeDenominator (0 : Fin 6) =
      (930982144 : ℝ) / 82354251 := by rfl
  have h4 : widerExactSlopeDenominator (4 : Fin 6) =
      (20492495104 : ℝ) / 431174667 := by rfl
  have h5 : widerExactSlopeDenominator (5 : Fin 6) =
      (9782600448 : ℝ) / 172793257 := by rfl
  have hfloor : widerSeparationFloor (0 : Fin 6) (4 : Fin 6) (5 : Fin 6) =
      (11 : ℝ) / 60 := by
    norm_num [widerSeparationFloor, firstSixIndex]
  rw [widerFixedBudget, h0, h4, h5, hfloor]
  norm_num [widerFixedDeltaCeiling, widerWeightedBudgetCeiling]

/-- Two-sided method ceiling for the explicitly frozen finite interface. -/
theorem common_budget_iff_le_widerFixedDeltaCeiling {delta : ℝ} :
    (∀ i j k : Fin 6, delta ≤ widerFixedBudget i j k) ↔
      delta ≤ widerFixedDeltaCeiling := by
  constructor
  · intro h
    have hspecial := h (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)
    rwa [widerFixedBudget_special] at hspecial
  · intro h i j k
    exact h.trans (widerFixedDeltaCeiling_le_budget i j k)

/-- The refined weighted-Cauchy ceiling lies above the localization ceiling;
localization, rather than the finite budget, is now the active bottleneck. -/
theorem widerLocalizationSq_lt_fixedDeltaCeiling :
    widerCorrelationThreshold ^ 2 < widerFixedDeltaCeiling := by
  norm_num [widerFixedDeltaCeiling, widerWeightedBudgetCeiling,
    widerCorrelationThreshold]

/-- Supremum of local energy constants permitted by the strict localization
gate in this frozen interface.  It is not itself admissible because the gate is
strict. -/
def widerFixedActivationSupremum : ℝ :=
  widerCorrelationThreshold ^ 2

/-- Every constant strictly below the localization supremum automatically lies
below all 216 refined weighted-Cauchy budgets. -/
theorem widerBelowActivationSupremum_le_budget {delta : ℝ}
    (hdelta : delta < widerFixedActivationSupremum) (i j k : Fin 6) :
    delta ≤ widerFixedBudget i j k := by
  have hceiling : delta < widerFixedDeltaCeiling :=
    hdelta.trans (by
      simpa [widerFixedActivationSupremum] using
        widerLocalizationSq_lt_fixedDeltaCeiling)
  exact hceiling.le.trans (widerFixedDeltaCeiling_le_budget i j k)

/-- Two-sided strict method ceiling after coupling the 216-row budget to the
localization gate. -/
theorem refined_interface_feasible_iff_lt_activationSupremum {delta : ℝ} :
    ((∀ i j k : Fin 6, delta ≤ widerFixedBudget i j k) ∧
      delta < widerFixedActivationSupremum) ↔
      delta < widerFixedActivationSupremum := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨widerBelowActivationSupremum_le_budget h, h⟩

def widerFixedEndpointGain : ℝ :=
  widerFixedActivationSupremum / 8 * ((102239 : ℝ) / 592688) ^ 2

def widerFixedUnitEta : ℝ := 1 / 79828975

theorem widerFixedUnitEta_eq_widerEtaLower :
    widerFixedUnitEta = widerEtaLower := by
  rfl

theorem widerFixedEndpointGain_value :
    widerFixedEndpointGain =
      25097204303521 / 2003484094270714880000 := by
  norm_num [widerFixedEndpointGain, widerFixedActivationSupremum,
    widerCorrelationThreshold]

/-- The selected local constant makes the frozen rational endpoint product
exactly the public unit fraction. -/
theorem widerFixedUnitEta_eq_selected_gain :
    widerFixedUnitEta =
      widerDeltaLower / 8 * ((102239 : ℝ) / 592688) ^ 2 := by
  norm_num [widerFixedUnitEta, widerDeltaLower]

/-- The public unit fraction lies strictly below the unattained activation
supremum. -/
theorem widerFixedUnitEta_lt_gain :
    widerFixedUnitEta < widerFixedEndpointGain := by
  norm_num [widerFixedUnitEta, widerFixedEndpointGain,
    widerFixedActivationSupremum, widerCorrelationThreshold]

/-- The immediately larger unit fraction already reaches or exceeds the
unattained activation supremum, so it is impossible in this interface. -/
theorem widerFixedEndpointGain_le_next_unit :
    widerFixedEndpointGain ≤ (1 : ℝ) / 79828974 := by
  norm_num [widerFixedEndpointGain, widerFixedActivationSupremum,
    widerCorrelationThreshold]

/-- The same unit fraction is valid after replacing the frozen rational gap by
the actual endpoint gap. -/
theorem widerFixedUnitEta_le_actual_endpoint_gain :
    widerFixedUnitEta ≤
      widerDeltaLower / 8 * (ThmD.HD 1 - 1 / 2) ^ 2 := by
  have hgap0 : 0 ≤ (102239 : ℝ) / 592688 := by norm_num
  have hsq := pow_le_pow_left₀ hgap0 refined_endpoint_gap 2
  have hcoef : 0 ≤ widerDeltaLower / 8 := by
    norm_num [widerDeltaLower]
  calc
    widerFixedUnitEta ≤
        widerDeltaLower / 8 * ((102239 : ℝ) / 592688) ^ 2 := by
      rw [← widerFixedUnitEta_eq_selected_gain]
    _ ≤ widerDeltaLower / 8 * (ThmD.HD 1 - 1 / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef

end StrictImprovement
end Zeta23

end
