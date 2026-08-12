/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.CorrelationNormalization

/-!
# Unordered three-coordinate endpoint energy

The root-localization theorem is stated for consecutive nonnegative gaps
`a,b`.  Packed triples arrive in an arbitrary enumeration order.  This module
removes that mismatch: any three real coordinates of diameter at most
`8*pi` have the same certified endpoint energy, and three arbitrary bounded
scalar correlations inherit it under uniform perturbation.
-/

noncomputable section

open Real

namespace Zeta23
namespace StrictImprovement

/-- Unordered pair energy of three real coordinates. -/
def threeCoordinateEnergy (R : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  R (x - y) ^ 2 + R (x - z) ^ 2 + R (y - z) ^ 2

/-- Ordered version: the three pair distances are `y-x`, `z-y`, and
their sum. -/
theorem endpoint_threeCoordinateEnergy_ordered
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hdiam : |x - z| ≤ 8 * Real.pi) :
    explicitDeltaLower ≤ threeCoordinateEnergy endpointR x y z := by
  have ha : 0 ≤ y - x := by linarith
  have hb : 0 ≤ z - y := by linarith
  have hab : (y - x) + (z - y) ≤ 8 * Real.pi := by
    rw [abs_of_nonpos (by linarith : x - z ≤ 0)] at hdiam
    nlinarith
  have h := endpoint_three_point_energy_lower ha hb hab
  unfold threeCoordinateEnergy
  have hxy' : y - x = -(x - y) := by ring
  have hxz' : (y - x) + (z - y) = -(x - z) := by ring
  have hyz' : z - y = -(y - z) := by ring
  rw [hxz', hxy', hyz', endpointR_neg, endpointR_neg, endpointR_neg] at h
  linarith

/-- The endpoint lower bound is independent of the enumeration order of the
three coordinates. -/
theorem endpoint_threeCoordinateEnergy_lower
    {x y z : ℝ}
    (hxyD : |x - y| ≤ 8 * Real.pi)
    (hxzD : |x - z| ≤ 8 * Real.pi)
    (hyzD : |y - z| ≤ 8 * Real.pi) :
    explicitDeltaLower ≤ threeCoordinateEnergy endpointR x y z := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact endpoint_threeCoordinateEnergy_ordered hxy hyz hxzD
    · rcases le_total x z with hxz | hzx
      · have h := endpoint_threeCoordinateEnergy_ordered hxz hzy hxyD
        unfold threeCoordinateEnergy at h ⊢
        have hzy' : z - y = -(y - z) := by ring
        rw [hzy', endpointR_neg] at h
        linarith
      · have h := endpoint_threeCoordinateEnergy_ordered hzx hxy
          (by simpa [abs_sub_comm] using hyzD)
        unfold threeCoordinateEnergy at h ⊢
        have hzx' : z - x = -(x - z) := by ring
        have hzy' : z - y = -(y - z) := by ring
        rw [hzx', hzy', endpointR_neg, endpointR_neg] at h
        linarith
  · rcases le_total x z with hxz | hzx
    · have h := endpoint_threeCoordinateEnergy_ordered hyx hxz hyzD
      unfold threeCoordinateEnergy at h ⊢
      have hyx' : y - x = -(x - y) := by ring
      rw [hyx', endpointR_neg] at h
      linarith
    · rcases le_total y z with hyz | hzy
      · have h := endpoint_threeCoordinateEnergy_ordered hyz hzx
          (by simpa [abs_sub_comm] using hxyD)
        unfold threeCoordinateEnergy at h ⊢
        have hyx' : y - x = -(x - y) := by ring
        have hzx' : z - x = -(x - z) := by ring
        rw [hyx', hzx', endpointR_neg, endpointR_neg] at h
        linarith
      · have h := endpoint_threeCoordinateEnergy_ordered hzy hyx
          (by simpa [abs_sub_comm] using hxzD)
        unfold threeCoordinateEnergy at h ⊢
        have hzy' : z - y = -(y - z) := by ring
        have hzx' : z - x = -(x - z) := by ring
        have hyx' : y - x = -(x - y) := by ring
        rw [hzy', hzx', hyx', endpointR_neg, endpointR_neg, endpointR_neg] at h
        linarith

/-- Three arbitrary real correlations uniformly close to the three endpoint
pair correlations lose at most `6*eps` in total squared energy. -/
theorem threeCoordinateEnergy_stable
    {x y z cxy cxz cyz eps : ℝ}
    (heps : 0 ≤ eps)
    (hxyD : |x - y| ≤ 8 * Real.pi)
    (hxzD : |x - z| ≤ 8 * Real.pi)
    (hyzD : |y - z| ≤ 8 * Real.pi)
    (hcxy : |cxy| ≤ 1) (hcxz : |cxz| ≤ 1) (hcyz : |cyz| ≤ 1)
    (hxy : |cxy - endpointR (x - y)| ≤ eps)
    (hxz : |cxz - endpointR (x - z)| ≤ eps)
    (hyz : |cyz - endpointR (y - z)| ≤ eps) :
    explicitDeltaLower - 6 * eps ≤ cxy ^ 2 + cxz ^ 2 + cyz ^ 2 := by
  have hbase := endpoint_threeCoordinateEnergy_lower hxyD hxzD hyzD
  have h1 := sq_sub_two_eps_le_sq_of_close heps
    (endpointR_abs_le_one (x - y)) hcxy hxy
  have h2 := sq_sub_two_eps_le_sq_of_close heps
    (endpointR_abs_le_one (x - z)) hcxz hxz
  have h3 := sq_sub_two_eps_le_sq_of_close heps
    (endpointR_abs_le_one (y - z)) hcyz hyz
  unfold threeCoordinateEnergy at hbase
  nlinarith

end StrictImprovement
end Zeta23
