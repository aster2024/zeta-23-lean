/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.KernelStability
import Zeta23.StrictImprovement.WiderQuadraticGain
import Zeta23.StrictImprovement.ZetaEndpointConstant

/-!
# Direct six-edge four-point certificate interface

This file records the exact algebraic interface supplied by the external Arb
certificate.  It does not formalize the interval computation itself: the
endpoint premise `m4 ≤ sum r_ij^2` remains explicit at the theorem boundary.
-/

noncomputable section

open Real

namespace Zeta23
namespace StrictImprovement

/-- Conservative endpoint six-edge energy certified by the external Arb
prefix tree. -/
def directFourEnergyLower : ℝ := 1 / 4000

/-- Public exact increment selected strictly below the rational endpoint
product. -/
def directFourEtaLower : ℝ := 1 / 2150796

/-- Six independent bounded correlations lose at most `12*eps` in their
total squared energy.  The ordering/geometry certificate is represented by
the explicit endpoint premise. -/
theorem direct_six_edge_energy_stable
    {m4 eps : ℝ}
    (heps : 0 ≤ eps)
    {r01 r02 r03 r12 r13 r23 : ℝ}
    {c01 c02 c03 c12 c13 c23 : ℝ}
    (hendpoint : m4 ≤
      r01 ^ 2 + r02 ^ 2 + r03 ^ 2 + r12 ^ 2 + r13 ^ 2 + r23 ^ 2)
    (hr01 : |r01| ≤ 1) (hr02 : |r02| ≤ 1) (hr03 : |r03| ≤ 1)
    (hr12 : |r12| ≤ 1) (hr13 : |r13| ≤ 1) (hr23 : |r23| ≤ 1)
    (hc01 : |c01| ≤ 1) (hc02 : |c02| ≤ 1) (hc03 : |c03| ≤ 1)
    (hc12 : |c12| ≤ 1) (hc13 : |c13| ≤ 1) (hc23 : |c23| ≤ 1)
    (h01 : |c01 - r01| ≤ eps) (h02 : |c02 - r02| ≤ eps)
    (h03 : |c03 - r03| ≤ eps) (h12 : |c12 - r12| ≤ eps)
    (h13 : |c13 - r13| ≤ eps) (h23 : |c23 - r23| ≤ eps) :
    m4 - 12 * eps ≤
      c01 ^ 2 + c02 ^ 2 + c03 ^ 2 + c12 ^ 2 + c13 ^ 2 + c23 ^ 2 := by
  have h01' := sq_sub_two_eps_le_sq_of_close heps hr01 hc01 h01
  have h02' := sq_sub_two_eps_le_sq_of_close heps hr02 hc02 h02
  have h03' := sq_sub_two_eps_le_sq_of_close heps hr03 hc03 h03
  have h12' := sq_sub_two_eps_le_sq_of_close heps hr12 hc12 h12
  have h13' := sq_sub_two_eps_le_sq_of_close heps hr13 hc13 h13
  have h23' := sq_sub_two_eps_le_sq_of_close heps hr23 hc23 h23
  nlinarith

/-- If finite normalized correlations have total error `eps`, then half of
the six-edge energy is a valid four-block defect parameter. -/
theorem direct_four_defect_parameter
    {m4 eps delta energy : ℝ}
    (henergy : m4 - 12 * eps ≤ energy)
    (hdelta : delta ≤ m4 / 2 - 6 * eps) :
    2 * delta ≤ energy := by
  linarith

/-- Exact endpoint arithmetic for the direct four-point candidate. -/
theorem directFourEtaLower_le_endpoint_gain :
    directFourEtaLower ≤
      directFourEnergyLower / 16 * (ThmD.HD 1 - 1 / 2) ^ 2 := by
  have hgap0 : 0 ≤ (102239 : ℝ) / 592688 := by norm_num
  have hsq := pow_le_pow_left₀ hgap0 refined_endpoint_gap 2
  have hcoef : 0 ≤ directFourEnergyLower / 16 := by
    norm_num [directFourEnergyLower]
  calc
    directFourEtaLower
        ≤ directFourEnergyLower / 16 * ((102239 : ℝ) / 592688) ^ 2 := by
          norm_num [directFourEtaLower, directFourEnergyLower]
    _ ≤ directFourEnergyLower / 16 * (ThmD.HD 1 - 1 / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef

theorem directFourEtaLower_gt_previous :
    (1 : ℝ) / 79828975 * 37 < directFourEtaLower := by
  norm_num [directFourEtaLower]

end StrictImprovement
end Zeta23

end
