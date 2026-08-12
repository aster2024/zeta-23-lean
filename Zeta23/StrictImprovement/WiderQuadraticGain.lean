/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Algebraic lower bound for the width-six four-point gain

This file is the exact `(q,d)=(4,6)` analogue of `QuadraticGain.lean`.
The denominator is `8` and four-at-a-time packing leaves at most `3` points
per bin.  No zeta or asymptotic input occurs here.
-/

noncomputable section

open Real

namespace Zeta23
namespace StrictImprovement

/-- If `s` has lower density `h` and upper density `u`, the width parameter
has density at most `d`, and the packing remainder `3` costs at most `r*N`,
then the width-six four-point gain is linear in `N` with the displayed exact
coefficient. -/
theorem wider_quadratic_core_gain_lower
    {s N D delta delta₀ h d r u q : ℝ}
    (hs : 0 < s) (hN : 0 < N) (hu : 0 < u)
    (hdelta₀ : 0 ≤ delta₀) (hdelta : delta₀ ≤ delta)
    (hslo : h * N ≤ s) (hshi : s ≤ u * N)
    (hD : D ≤ d * N) (hconst : 3 ≤ r * N)
    (hq : q = h - d / 2 - r) (hq0 : 0 ≤ q) :
    delta / (8 * s) * max 0 (s - D / 2 - 3) ^ 2 ≥
      delta₀ * q ^ 2 / (8 * u) * N := by
  have hqN0 : 0 ≤ q * N := mul_nonneg hq0 hN.le
  have ha : q * N ≤ s - D / 2 - 3 := by
    rw [hq]
    nlinarith
  have ha0 : 0 ≤ s - D / 2 - 3 := hqN0.trans ha
  rw [max_eq_right ha0]
  have hsq : (q * N) ^ 2 ≤ (s - D / 2 - 3) ^ 2 := by
    exact pow_le_pow_left₀ hqN0 ha 2
  have hnum : delta₀ * (q * N) ^ 2 ≤
      delta * (s - D / 2 - 3) ^ 2 := by
    exact mul_le_mul hdelta hsq (sq_nonneg _) (hdelta₀.trans hdelta)
  rw [show delta / (8 * s) * (s - D / 2 - 3) ^ 2 =
      delta * (s - D / 2 - 3) ^ 2 / (8 * s) by ring]
  apply (le_div_iff₀ (mul_pos (by norm_num) hs)).2
  calc
    delta₀ * q ^ 2 / (8 * u) * N * (8 * s)
        = delta₀ * q ^ 2 * N * s / u := by
            field_simp [hu.ne']
            ring
    _ ≤ delta₀ * q ^ 2 * N * (u * N) / u := by
          gcongr
          positivity
    _ = delta₀ * (q * N) ^ 2 := by
          field_simp [hu.ne']
          ring
    _ ≤ delta * (s - D / 2 - 3) ^ 2 := hnum

end StrictImprovement
end Zeta23

end
