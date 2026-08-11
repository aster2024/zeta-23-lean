/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.IntervalBinning
import Zeta23.StrictImprovement.ZetaCore

/-!
# Exact interval bins for the zeta core

The ordinate map `gamma ↦ L*gamma` sends the core interval
`[T+C,2T-C]` into an interval of length at most `L*T = 2*pi*D`, where
`D=L*T/(2*pi)`.  This module instantiates the generic width-`8*pi` floor
bins and the lossless fiber enumeration for the actual finite type of core
simple on-line zeros.

Only exact finite and order statements occur here.  Kernel correlation and
asymptotic zero-count estimates remain separate interfaces.
-/

noncomputable section

open Finset Real
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

variable (Z : ZeroConfig) (T C : ℝ) (P : Params)

/-- Scaled ordinate used by the endpoint correlation kernel. -/
def coreScaledOrdinate (z : CoreSimpleLabel Z T C) : ℝ :=
  P.L T * (z : ℂ).im

/-- Left endpoint of the scaled core interval. -/
def coreBinBase : ℝ := P.L T * (T + C)

/-- Dimension parameter in the local pinching count. -/
def coreBinD : ℝ := P.L T * T / (2 * Real.pi)

/-- The scaled core ordinates satisfy the generic interval-binning range. -/
theorem coreScaledOrdinate_range
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    ∀ z : CoreSimpleLabel Z T C,
      0 ≤ coreScaledOrdinate Z T C P z - coreBinBase T C P ∧
      coreScaledOrdinate Z T C P z - coreBinBase T C P ≤
        2 * Real.pi * coreBinD T P := by
  intro z
  have hz := z.2
  simp only [coreSimple, Finset.mem_filter] at hz
  have hzlo : T + C ≤ (z : ℂ).im := hz.2.1
  have hzhi : (z : ℂ).im ≤ 2 * T - C := hz.2.2
  have hgap0 : 0 ≤ (z : ℂ).im - (T + C) := by linarith
  have hgapT : (z : ℂ).im - (T + C) ≤ T := by linarith
  have hlo := mul_nonneg hL.le hgap0
  have hhi := mul_le_mul_of_nonneg_left hgapT hL.le
  have hrhs : 2 * Real.pi * coreBinD T P = P.L T * T := by
    unfold coreBinD
    field_simp [Real.pi_ne_zero]
    ring
  constructor
  · unfold coreScaledOrdinate coreBinBase
    nlinarith
  · rw [hrhs]
    unfold coreScaledOrdinate coreBinBase
    nlinarith

/-- Concrete width-`8*pi` bin of a core simple zero. -/
noncomputable def coreIntervalBin
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (z : CoreSimpleLabel Z T C) : Fin (intervalBinCount (coreBinD T P)) :=
  intervalBin (coreBinD T P) (coreBinBase T C P)
    (coreScaledOrdinate Z T C P) (coreScaledOrdinate_range Z T C P hL hC) z

/-- Exact no-loss enumeration of the concrete core interval bins. -/
noncomputable def coreBinnedEnumeration
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    BinnedEnumeration (CoreSimpleLabel Z T C)
      (Fin (intervalBinCount (coreBinD T P))) :=
  fiberBinnedEnumeration (coreIntervalBin Z T C P hL hC)

/-- Every core label occurs exactly once in the concrete binned
enumeration. -/
theorem coreBinnedEnumeration_cover
    (hL : 0 < P.L T) (hC : 0 ≤ C) :
    ∑ b, (coreBinnedEnumeration Z T C P hL hC).occupancy b =
      Fintype.card (CoreSimpleLabel Z T C) := by
  exact fiberBinnedEnumeration_cover (coreIntervalBin Z T C P hL hC)

/-- The concrete number of bins has the count required by the hyperbolic
target, namely at most `D/4+1`. -/
theorem coreIntervalBin_card_le
    (hL : 0 < P.L T) (hT : 0 ≤ T) :
    (Fintype.card (Fin (intervalBinCount (coreBinD T P))) : ℝ) ≤
      coreBinD T P / 4 + 1 := by
  apply intervalBin_card_le
  unfold coreBinD
  positivity

/-- Each selected slot remembers its exact concrete bin. -/
@[simp] theorem corePackedTripleIndex_bin
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (q : PackedTriple (coreBinnedEnumeration Z T C P hL hC)) (k : Fin 3) :
    coreIntervalBin Z T C P hL hC
      (packedTripleIndex (coreBinnedEnumeration Z T C P hL hC) q k) = q.1 := by
  exact fiberBinnedEnumeration_at_bin
    (coreIntervalBin Z T C P hL hC) q.1 _

/-- Every canonical packed core triple has scaled diameter below `8*pi`. -/
theorem corePackedTriple_diameter_lt_eight_pi
    (hL : 0 < P.L T) (hC : 0 ≤ C)
    (q : PackedTriple (coreBinnedEnumeration Z T C P hL hC)) :
    let idx := packedTripleIndex (coreBinnedEnumeration Z T C P hL hC) q
    |coreScaledOrdinate Z T C P (idx 0) -
        coreScaledOrdinate Z T C P (idx 1)| < 8 * Real.pi ∧
      |coreScaledOrdinate Z T C P (idx 0) -
        coreScaledOrdinate Z T C P (idx 2)| < 8 * Real.pi ∧
      |coreScaledOrdinate Z T C P (idx 1) -
        coreScaledOrdinate Z T C P (idx 2)| < 8 * Real.pi := by
  dsimp
  apply triple_diameter_lt_eight_pi_of_intervalBin_eq
    (coreScaledOrdinate_range Z T C P hL hC)
  · rw [corePackedTripleIndex_bin, corePackedTripleIndex_bin]
  · rw [corePackedTripleIndex_bin, corePackedTripleIndex_bin]

end StrictImprovement
end Zeta23
