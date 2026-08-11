/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaSeamDefect
import Zeta23.StrictImprovement.ZetaBoundaryLoss
import Zeta23.ThmD.AssemblyD

/-!
# Algebraic and asymptotic interfaces for the strict endgame

The finite-height lemma keeps the new quadratic gain through the standard
trace/Frobenius elimination.  The asymptotic lemma then absorbs exactly two
`o(N)` terms: the frozen trace/seam error and the newly exposed width-three
boundary loss.

Neither lemma makes a zeta-specific density assumption.  The remaining
zeta task is therefore isolated to proving a linear lower bound for the
quadratic core gain.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace Zeta23
namespace StrictImprovement

/-- The exact Theorem-D trace elimination with an additional nonnegative
gain and an explicit boundary term.  No sign condition on `gain` or
`boundary` is needed for this algebraic transport. -/
theorem N0simple_lower_c_with_gain
    {N0simple boundary gain N NII trGh frGh B cinv R₁ R₂ : ℝ}
    (hB : 0 ≤ B)
    (h0 : 4 * trGh - frGh - 2 * N - 3 * NII -
        B * (4 + 2 * Real.sqrt frGh + B) + gain ≤
          N0simple + boundary)
    (htr : |trGh - N| ≤ R₁) (hfr : frGh ≤ cinv * N + R₂) :
    (2 - cinv) * N -
        (4 * R₁ + R₂ + 3 * NII +
          B * (4 + 2 * Real.sqrt (cinv * N + R₂) + B)) + gain ≤
      N0simple + boundary := by
  have hbase :
      4 * trGh - frGh - 2 * N - 3 * NII -
          B * (4 + 2 * Real.sqrt frGh + B) ≤
        N0simple + boundary - gain := by
    linarith
  have h := ThmD.N0star_lower_c hB hbase htr hfr
  linarith

/-- Abstract strict asymptotic transfer.  A finite-height gain of at least
`eta*N` improves the baseline coefficient from `H` to `H+eta`; both the
standard error and the boundary correction are required to be `o(N)`.

This formulation is deliberately additive, so a caller cannot hide a
main-order boundary loss inside an unnamed error term. -/
theorem eps_form_of_isLittleO_with_gain
    {H eta : ℝ} {N lower err boundary gain : ℝ → ℝ}
    (hmain : ∀ᶠ T in atTop,
      H * N T - err T + gain T ≤ lower T + boundary T)
    (hN : ∀ᶠ T in atTop, 0 ≤ N T)
    (herr : err =o[atTop] N)
    (hboundary : boundary =o[atTop] N)
    (hgain : ∀ᶠ T in atTop, eta * N T ≤ gain T) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (H + eta - eps) * N T ≤ lower T := by
  have hstrict : ∀ᶠ T in atTop,
      (H + eta) * N T - (err T + boundary T) ≤ lower T := by
    filter_upwards [hmain, hgain] with T hm hg
    linarith
  have hsmall : (fun T => err T + boundary T) =o[atTop] N :=
    herr.add hboundary
  exact Assembly.eps_form_of_isLittleO hstrict hN hsmall

/-- A convenient version where the gain itself is known only up to an
additional `o(N)` loss. -/
theorem eps_form_of_isLittleO_with_approx_gain
    {H eta : ℝ} {N lower err boundary gain gainErr : ℝ → ℝ}
    (hmain : ∀ᶠ T in atTop,
      H * N T - err T + gain T ≤ lower T + boundary T)
    (hN : ∀ᶠ T in atTop, 0 ≤ N T)
    (herr : err =o[atTop] N)
    (hboundary : boundary =o[atTop] N)
    (hgainErr : gainErr =o[atTop] N)
    (hgain : ∀ᶠ T in atTop,
      eta * N T - gainErr T ≤ gain T) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (H + eta - eps) * N T ≤ lower T := by
  have hstrict : ∀ᶠ T in atTop,
      (H + eta) * N T - (err T + boundary T + gainErr T) ≤ lower T := by
    filter_upwards [hmain, hgain] with T hm hg
    linarith
  have hsmall : (fun T => err T + boundary T + gainErr T) =o[atTop] N :=
    (herr.add hboundary).add hgainErr
  exact Assembly.eps_form_of_isLittleO hstrict hN hsmall

end StrictImprovement
end Zeta23

end
