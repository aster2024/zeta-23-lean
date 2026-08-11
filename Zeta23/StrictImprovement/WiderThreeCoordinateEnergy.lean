/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WiderFourPointEnergy
import Zeta23.StrictImprovement.ThreeCoordinateEnergy

/-!
# Unordered width-six three-coordinate energy

This is the `12*pi`, endpoint-optimized counterpart of
`ThreeCoordinateEnergy.lean`.
It converts the ordered gap theorem into an enumeration-independent statement
and records the same exact `6*eps` stability loss.
-/

noncomputable section

open Real

namespace Zeta23
namespace StrictImprovement

theorem wider_endpoint_threeCoordinateEnergy_ordered
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hdiam : |x - z| ≤ 12 * Real.pi) :
    widerDeltaLower ≤ threeCoordinateEnergy endpointR x y z := by
  have ha : 0 ≤ y - x := by linarith
  have hb : 0 ≤ z - y := by linarith
  have hab : (y - x) + (z - y) ≤ 12 * Real.pi := by
    rw [abs_of_nonpos (by linarith : x - z ≤ 0)] at hdiam
    nlinarith
  have h := wider_endpoint_three_point_energy_lower ha hb hab
  unfold threeCoordinateEnergy
  have hxy' : y - x = -(x - y) := by ring
  have hxz' : (y - x) + (z - y) = -(x - z) := by ring
  have hyz' : z - y = -(y - z) := by ring
  rw [hxy', hxz', hyz', endpointR_neg, endpointR_neg, endpointR_neg] at h
  linarith

theorem wider_endpoint_threeCoordinateEnergy_lower
    {x y z : ℝ}
    (hxyD : |x - y| ≤ 12 * Real.pi)
    (hxzD : |x - z| ≤ 12 * Real.pi)
    (hyzD : |y - z| ≤ 12 * Real.pi) :
    widerDeltaLower ≤ threeCoordinateEnergy endpointR x y z := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact wider_endpoint_threeCoordinateEnergy_ordered hxy hyz hxzD
    · rcases le_total x z with hxz | hzx
      · have h := wider_endpoint_threeCoordinateEnergy_ordered hxz hzy hxyD
        unfold threeCoordinateEnergy at h ⊢
        have hzy' : z - y = -(y - z) := by ring
        rw [hzy', endpointR_neg] at h
        linarith
      · have h := wider_endpoint_threeCoordinateEnergy_ordered hzx hxy hyzD
        unfold threeCoordinateEnergy at h ⊢
        have hzx' : z - x = -(x - z) := by ring
        have hzy' : z - y = -(y - z) := by ring
        rw [hzx', hzy', endpointR_neg, endpointR_neg] at h
        linarith
  · rcases le_total x z with hxz | hzx
    · have h := wider_endpoint_threeCoordinateEnergy_ordered hyx hxz hyzD
      unfold threeCoordinateEnergy at h ⊢
      have hyx' : y - x = -(x - y) := by ring
      rw [hyx', endpointR_neg] at h
      linarith
    · rcases le_total y z with hyz | hzy
      · have h := wider_endpoint_threeCoordinateEnergy_ordered hyz hzx hxyD
        unfold threeCoordinateEnergy at h ⊢
        have hyx' : y - x = -(x - y) := by ring
        have hzx' : z - x = -(x - z) := by ring
        rw [hyx', hzx', endpointR_neg, endpointR_neg] at h
        linarith
      · have h := wider_endpoint_threeCoordinateEnergy_ordered hzy hyx hxzD
        unfold threeCoordinateEnergy at h ⊢
        have hzy' : z - y = -(y - z) := by ring
        have hzx' : z - x = -(x - z) := by ring
        rw [hzy', hzx', endpointR_neg, endpointR_neg] at h
        linarith

theorem wider_threeCoordinateEnergy_stable
    {x y z cxy cxz cyz eps : ℝ}
    (heps : 0 ≤ eps)
    (hxyD : |x - y| ≤ 12 * Real.pi)
    (hxzD : |x - z| ≤ 12 * Real.pi)
    (hyzD : |y - z| ≤ 12 * Real.pi)
    (hcxy : |cxy| ≤ 1) (hcxz : |cxz| ≤ 1) (hcyz : |cyz| ≤ 1)
    (hxy : |cxy - endpointR (x - y)| ≤ eps)
    (hxz : |cxz - endpointR (x - z)| ≤ eps)
    (hyz : |cyz - endpointR (y - z)| ≤ eps) :
    widerDeltaLower - 6 * eps ≤ cxy ^ 2 + cxz ^ 2 + cyz ^ 2 := by
  have hbase := wider_endpoint_threeCoordinateEnergy_lower hxyD hxzD hyzD
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

end
