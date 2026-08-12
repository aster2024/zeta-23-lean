/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Algebraic lower bound for the quadratic core gain

This file isolates the denominator-sensitive algebra used by the strict
endgame.  It is deliberately independent of the zeta application.

This is a source draft pending the pinned Lean build.
-/

noncomputable section

open Real

namespace Zeta23
namespace StrictImprovement

/-- If `s` has a lower density `h` and upper density `u`, the bin parameter
has density at most `d`, and the additive constant `2` costs at most `r*N`,
then the local quadratic gain has the displayed linear-in-`N` lower bound.

The hypotheses retain `q = h-d/2-r` explicitly so callers can use rational
arithmetic before invoking this lemma. -/
theorem quadratic_core_gain_lower
    {s N D delta delta₀ h d r u q : ℝ}
    (hs : 0 < s) (hN : 0 < N) (hu : 0 < u)
    (hdelta₀ : 0 ≤ delta₀) (hdelta : delta₀ ≤ delta)
    (hslo : h * N ≤ s) (hshi : s ≤ u * N)
    (hD : D ≤ d * N) (hconst : 2 ≤ r * N)
    (hq : q = h - d / 2 - r) (hq0 : 0 ≤ q) :
    delta / (9 * s) * max 0 (s - D / 2 - 2) ^ 2 ≥
      delta₀ * q ^ 2 / (9 * u) * N := by
  have hqN0 : 0 ≤ q * N := mul_nonneg hq0 hN.le
  have ha : q * N ≤ s - D / 2 - 2 := by
    rw [hq]
    nlinarith
  have ha0 : 0 ≤ s - D / 2 - 2 := hqN0.trans ha
  rw [max_eq_right ha0]
  have hsq : (q * N) ^ 2 ≤ (s - D / 2 - 2) ^ 2 := by
    exact pow_le_pow_left₀ hqN0 ha 2
  have hnum : delta₀ * (q * N) ^ 2 ≤
      delta * (s - D / 2 - 2) ^ 2 := by
    exact mul_le_mul hdelta hsq (sq_nonneg _) (hdelta₀.trans hdelta)
  rw [show delta / (9 * s) * (s - D / 2 - 2) ^ 2 =
      delta * (s - D / 2 - 2) ^ 2 / (9 * s) by ring]
  apply (le_div_iff₀ (mul_pos (by norm_num) hs)).2
  calc
    delta₀ * q ^ 2 / (9 * u) * N * (9 * s)
        = delta₀ * q ^ 2 * N * s / u := by
            field_simp [hu.ne']
    _ ≤ delta₀ * q ^ 2 * N * (u * N) / u := by
          gcongr
    _ = delta₀ * (q * N) ^ 2 := by
          field_simp [hu.ne']
    _ ≤ delta * (s - D / 2 - 2) ^ 2 := hnum

end StrictImprovement
end Zeta23

end
