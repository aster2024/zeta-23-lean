/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.Q6SuperbinBinning

/-!
# Binning reused by the full-spectral q7 repair

The q7 improvement changes only how residual three- and four-blocks inside a
width-`32*pi` superbin are merged.  The superbin assignment, half-bin split,
coverage, and geometric bounds are exactly the already kernel-checked q6
construction, so this file reuses them rather than redeclaring a parallel copy.
-/

noncomputable section

namespace Zeta23
namespace StrictImprovement

/-- Alias used in the q7 arithmetic and documentation. -/
def q7FullSpectralCount (D : ℝ) : ℕ := q6SuperbinCount D

theorem q7FullSpectral_card_le {D : ℝ} (hD : 0 ≤ D) :
    (Fintype.card (Fin (q7FullSpectralCount D)) : ℝ) ≤ D / 16 + 1 := by
  change (Fintype.card (Fin (q6SuperbinCount D)) : ℝ) ≤ D / 16 + 1
  exact q6Superbin_card_le hD

/-- The core q7 selector uses the same width-32 superbin count as q6. -/
theorem coreQ7FullSpectral_card_le
    (T : ℝ) (P : Params) (hL : 0 < P.L T) (hT : 0 ≤ T) :
    (Fintype.card (Fin (q7FullSpectralCount (coreBinD T P))) : ℝ) ≤
      coreBinD T P / 16 + 1 := by
  change (Fintype.card (Fin (q6SuperbinCount (coreBinD T P))) : ℝ) ≤
    coreBinD T P / 16 + 1
  exact coreQ6Superbin_card_le T P hL hT

end StrictImprovement
end Zeta23

end
