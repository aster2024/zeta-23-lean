/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaSeamDefect
import Zeta23.StrictImprovement.ZetaCoreGain

/-!
# Eventual discharge of the strict seam side conditions

For a fixed valid Montgomery--Taylor parameter family, this file packages all
large-height conditions needed by `seamA_mult2_atD_with_explicit_gain`:

* the exact D-window Poisson identity;
* the window-generic local hypotheses;
* positive mass and the explicit finite-grid tail gate;
* nonvanishing of every selected finite core vector;
* positivity of the fixed-height local defect.

Only the frozen tail package and eventual nonemptiness of the selected core
remain as caller inputs.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Filter Topology Real Matrix RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

/-- The strict seam inequality holds eventually once the selected core is
known to be nonempty. -/
theorem eventually_seamA_mult2_atD_with_explicit_gain
    (Z : ZeroConfig) (P : Params) (hP : P.Valid)
    (theta₀ : ℝ → ℝ)
    (hTail : ∀ᶠ T in atTop,
      Assembly.TailInputs Z (P.atD T) T (theta₀ T))
    (hNonempty : ∀ᶠ T in atTop,
      Nonempty (CoreSimpleLabel Z T 3))
    (hdelta : 18 * (1 - P.lam) < explicitDeltaLower) :
    ∀ᶠ T in atTop,
      4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
          frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) -
          2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ) -
          theta₀ T / ((P.atD T).a T * (P.atD T).L T) *
            (4 + 2 * Real.sqrt
                (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))) +
              theta₀ T / ((P.atD T).a T * (P.atD T).L T)) +
          atDCoreGain Z T P
        ≤ Z.N0s T (2 * T) + excludedSimpleCount Z T 3 := by
  obtain ⟨T₀, hlocal⟩ := ThmD.localHypsCoreD_eventually hP
  have hLtop := ThmD.tendsto_L hP
  have haRange := ThmD.eventually_aD_range hP
  have hdeltaEv := eventually_atDLocalDelta_pos hP hdelta
  filter_upwards [hTail, hNonempty, eventually_ge_atTop T₀,
      hLtop.eventually_ge_atTop (16 * P.w),
      hLtop.eventually_gt_atTop ((ThmD.cDT P.ϱ P.lam) ^ 2),
      haRange, hdeltaEv, eventually_gt_atTop (0 : ℝ)]
    with T hTl hne hT₀ h16 hlarge haD hdeltaT hT
  letI : Nonempty (CoreSimpleLabel Z T 3) := hne
  have hFcore := hlocal T hT₀
  have hF : PrimeSide.LocalHypsCoreW (ThmD.cDT P.ϱ P.lam)
      ((P.atD T).toSetting T) ((P.atD T).localFun T) := by
    simpa [Params.atD_toSetting, Params.atD_localFun T hP] using
      hFcore.toCoreW
  have hL : 0 < P.L T := by
    simpa [Params.atD_toSetting, Params.toSetting_L] using hF.L_pos
  have hLD : 0 < (P.atD T).L T := by simpa using hL
  have ha : 0 < (P.atD T).a T := by linarith [haD.1]
  have hc : 0 < (P.atD T).a T * (P.atD T).L T ^ 2 :=
    mul_pos ha (sq_pos_of_pos hLD)
  have hlargeF : (ThmD.cDT P.ϱ P.lam) ^ 2 <
      ((P.atD T).toSetting T).L := by
    simpa [Params.atD_toSetting, Params.toSetting_L] using hlarge
  have htailHalf := coreTailBudget_three_lt_half_L_sq hF hlargeF
  have hscale : (P.atD T).L T ^ 2 / 2 ≤
      (P.atD T).a T * (P.atD T).L T ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right haD.1
      (sq_nonneg ((P.atD T).L T))
    nlinarith
  have hbudget :
      coreTailBudget (ThmD.cDT P.ϱ P.lam)
          ((P.atD T).toSetting T) 3 <
        (P.atD T).a T * (P.atD T).L T ^ 2 :=
    htailHalf.trans_le hscale
  let hconj : PhiHatConj T (P.atD T) :=
    fun z => GzGp.phiHat_conj (P.atD T) T z
  let hreal : PhiHatReal T (P.atD T) :=
    fun r => GzGp.phiHat_ofReal (P.atD T) T r
  have hpos : ∀ z,
      0 < finiteCoreWeight Z T 3 (P.atD T) hconj z := by
    intro z
    have hz := z.2
    simp only [coreSimple, Finset.mem_filter] at hz
    have hrhoLe := rho_core_le_budget hF hT (show (1 : ℝ) < 3 by norm_num)
      hz.2
    exact finiteCoreWeight_pos_of_rho_lt Z T 3 (P.atD T) hconj
      hreal hc z (hrhoLe.trans_lt hbudget)
  have h8 : 8 * P.w ≤ P.L T := by
    nlinarith [hP.one_le_w]
  have hPois : PoissonSq T (P.atD T) := ThmD.poissonSqD hP h8
  have hseam := seamA_mult2_atD_with_explicit_gain
    Z hP hconj hreal hPois hF hTl hT hc hbudget h16 hpos hdeltaT.le
  simpa [atDCoreGain] using hseam

end StrictImprovement
end Zeta23

end
