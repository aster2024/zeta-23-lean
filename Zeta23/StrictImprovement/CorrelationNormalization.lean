/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.KernelStability

/-!
# Stability under finite-vector unit normalization

This file isolates the scalar calculation behind the finite/full correlation
transfer.  If two truncated squared norms lie in `[1-q,1]`, their geometric
normalization denominator lies in the same interval.  If the unnormalized
correlation is already within `q` of the full correlation, unit normalization
increases the error to at most `2q`.

The result is exact and deliberately independent of zeta notation.
-/

noncomputable section

open Real

namespace Zeta23
namespace StrictImprovement

/-- The product of the two square-root norm factors remains in `[1-q,1]`. -/
theorem sqrt_weight_product_mem
    {q w₁ w₂ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hw₁lo : 1 - q ≤ w₁) (hw₁hi : w₁ ≤ 1)
    (hw₂lo : 1 - q ≤ w₂) (hw₂hi : w₂ ≤ 1) :
    1 - q ≤ Real.sqrt w₁ * Real.sqrt w₂ ∧
      Real.sqrt w₁ * Real.sqrt w₂ ≤ 1 := by
  have hbase0 : 0 ≤ 1 - q := by linarith
  have hw₁0 : 0 ≤ w₁ := hbase0.trans hw₁lo
  have hw₂0 : 0 ≤ w₂ := hbase0.trans hw₂lo
  have hs₁lo : Real.sqrt (1 - q) ≤ Real.sqrt w₁ :=
    Real.sqrt_le_sqrt hw₁lo
  have hs₂lo : Real.sqrt (1 - q) ≤ Real.sqrt w₂ :=
    Real.sqrt_le_sqrt hw₂lo
  have hprodlo : Real.sqrt (1 - q) * Real.sqrt (1 - q) ≤
      Real.sqrt w₁ * Real.sqrt w₂ :=
    mul_le_mul hs₁lo hs₂lo (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs₁hi : Real.sqrt w₁ ≤ 1 := Real.sqrt_le_one.mpr hw₁hi
  have hs₂hi : Real.sqrt w₂ ≤ 1 := Real.sqrt_le_one.mpr hw₂hi
  have hprodhi : Real.sqrt w₁ * Real.sqrt w₂ ≤ 1 * 1 :=
    mul_le_mul hs₁hi hs₂hi (Real.sqrt_nonneg _) (by norm_num)
  constructor
  · rw [Real.mul_self_sqrt hbase0] at hprodlo
    exact hprodlo
  · simpa using hprodhi

/-- Scalar unit-normalization stability.  Here `k` is the finite
unnormalized correlation, `f` is the full correlation, and `u` is the product
of the two norm factors. -/
theorem normalized_scalar_close
    {q u k f : ℝ} (hq0 : 0 ≤ q)
    (hulo : 1 - q ≤ u) (huhi : u ≤ 1) (hu0 : 0 < u)
    (hk : |k| ≤ u) (hfk : |f - k| ≤ q) :
    |k / u - f| ≤ 2 * q := by
  have hinv0 : 0 ≤ 1 / u - 1 := by
    rw [sub_nonneg, one_le_div hu0]
    exact huhi
  have hscale : |k / u - k| ≤ 1 - u := by
    have heq : k / u - k = k * (1 / u - 1) := by
      field_simp [hu0.ne']
      ring
    rw [heq, abs_mul, abs_of_nonneg hinv0]
    calc
      |k| * (1 / u - 1) ≤ u * (1 / u - 1) :=
        mul_le_mul_of_nonneg_right hk hinv0
      _ = 1 - u := by field_simp [hu0.ne']; ring
  have hscaleq : |k / u - k| ≤ q := by linarith
  calc
    |k / u - f| ≤ |k / u - k| + |k - f| := abs_sub_le _ _ _
    _ ≤ q + q := add_le_add hscaleq (by simpa [abs_sub_comm] using hfk)
    _ = 2 * q := by ring

/-- Ready-to-use form in which the denominator is built from two squared
norms. -/
theorem normalized_scalar_close_of_weights
    {q w₁ w₂ k f : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hw₁lo : 1 - q ≤ w₁) (hw₁hi : w₁ ≤ 1)
    (hw₂lo : 1 - q ≤ w₂) (hw₂hi : w₂ ≤ 1)
    (hk : |k| ≤ Real.sqrt w₁ * Real.sqrt w₂)
    (hfk : |f - k| ≤ q) :
    |k / (Real.sqrt w₁ * Real.sqrt w₂) - f| ≤ 2 * q := by
  have hu := sqrt_weight_product_mem hq0 hq1 hw₁lo hw₁hi hw₂lo hw₂hi
  have hw₁pos : 0 < w₁ := lt_of_lt_of_le (sub_pos.mpr hq1) hw₁lo
  have hw₂pos : 0 < w₂ := lt_of_lt_of_le (sub_pos.mpr hq1) hw₂lo
  have hupos : 0 < Real.sqrt w₁ * Real.sqrt w₂ :=
    mul_pos (Real.sqrt_pos.mpr hw₁pos) (Real.sqrt_pos.mpr hw₂pos)
  exact normalized_scalar_close hq0 hu.1 hu.2 hupos hk hfk

end StrictImprovement
end Zeta23
