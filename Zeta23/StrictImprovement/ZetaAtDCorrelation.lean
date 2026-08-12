/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.CoreTripleEnergy
import Zeta23.StrictImprovement.WindowFourierLimit
import Zeta23.ThmD.ParamsD

/-!
# The concrete `atD` full correlation and the endpoint kernel

This file discharges the scalar hypothesis left open in
`CoreTripleEnergy.lean`.  The important bookkeeping point is that the
Montgomery--Taylor window is represented on the zero side by `P.atD T`, not
by the original flat-window parameter `P`.

For `16*w <= L`, the exact uniform error is

`12*w/L + 3*(1-lam)`.

The first term is the finite smooth-window error and tends to zero at fixed
`lam`; the second is the fixed-`lam` to endpoint error and tends to zero as
`lam -> 1-`.  This is a source draft until compiled with the pinned toolchain.
-/

noncomputable section

open Real
open scoped ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

/-- The exact fixed-height defect surviving the full-kernel and finite/full
normalization errors for the concrete Montgomery--Taylor family. -/
def atDLocalDelta (T : ℝ) (P : Params) : ℝ :=
  explicitDeltaLower -
    6 * localCorrelationError T (P.atD T) (ThmD.cDT P.ϱ P.lam)
      (12 * P.w / P.L T + 3 * (1 - P.lam))

/-- The full Poisson correlation for the window-realizing family `P.atD T`
is exactly the finite-window normalized Fourier kernel at the scaled
ordinate difference. -/
theorem fullCoreCorrelation_atD_eq_phiDNormalizedKernel
    (Z : ZeroConfig) {T : ℝ} {P : Params} (hP : P.Valid)
    (hL : 0 < P.L T) (z z' : CoreSimpleLabel Z T 3) :
    fullCoreCorrelation Z T (P.atD T) z z' =
      phiDNormalizedKernel P.ϱ P.lam (P.L T) P.w
        (coreScaledOrdinate Z T 3 P z - coreScaledOrdinate Z T 3 P z') := by
  unfold fullCoreCorrelation
  change PrimeSide.Kinf ((P.atD T).toSetting T) ((P.atD T).localFun T)
      (z : ℂ).im (z' : ℂ).im /
        ((P.atD T).a T * (P.atD T).L T ^ 2) = _
  rw [show (P.atD T).localFun T = P.localFunD T from Params.atD_localFun T hP]
  unfold PrimeSide.Kinf phiDNormalizedKernel
  rw [Params.atD_a T hP]
  unfold Params.localFunD Params.phiD AdmWindow.localFun AdmWindow.av
  simp only [Params.atD_toSetting, Params.toSetting_L, Params.atD_L,
    coreScaledOrdinate]
  have hx :
      (P.L T * (z : ℂ).im - P.L T * (z' : ℂ).im) / P.L T =
        (z : ℂ).im - (z' : ℂ).im := by
    field_simp [hL.ne']
  rw [hx]
  field_simp [hL.ne']

/-- Uniform full-correlation comparison for the concrete `atD` family. -/
theorem fullCoreCorrelation_atD_close_endpointR
    (Z : ZeroConfig) {T : ℝ} {P : Params} (hP : P.Valid)
    (hwL : 16 * P.w ≤ P.L T) (z z' : CoreSimpleLabel Z T 3) :
    |fullCoreCorrelation Z T (P.atD T) z z' -
        endpointR (coreScaledOrdinate Z T 3 P z -
          coreScaledOrdinate Z T 3 P z')| ≤
      12 * P.w / P.L T + 3 * (1 - P.lam) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  let x := coreScaledOrdinate Z T 3 P z - coreScaledOrdinate Z T 3 P z'
  have hfinite := phiDNormalizedKernel_close_endpointRAt
    hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w hwL x
  have hlam := endpointRAt_close_endpointR hP.lam_pos hP.lam_le_one x
  rw [fullCoreCorrelation_atD_eq_phiDNormalizedKernel Z hP hL z z']
  dsimp [x] at hfinite hlam ⊢
  exact (abs_sub_le _ _ _).trans (add_le_add hfinite hlam)

/-- Ready-to-use discharge of the scalar hypothesis in
`packedCoreTriple_local_energy`, for the concrete `atD` family. -/
theorem packedCoreTriple_atD_local_energy
    (Z : ZeroConfig) {T : ℝ} {P : Params} (hP : P.Valid)
    (hconj : PhiHatConj T (P.atD T))
    (hreal : PhiHatReal T (P.atD T))
    (hF : PrimeSide.LocalHypsCoreW (ThmD.cDT P.ϱ P.lam)
      ((P.atD T).toSetting T) ((P.atD T).localFun T))
    (hT : 0 < T)
    (hc : 0 < (P.atD T).a T * (P.atD T).L T ^ 2)
    (hbudget : coreTailBudget (ThmD.cDT P.ϱ P.lam) ((P.atD T).toSetting T) 3 <
      (P.atD T).a T * (P.atD T).L T ^ 2)
    (hwL : 16 * P.w ≤ P.L T)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 (P.atD T) hconj z)
    (q : PackedTriple (coreBinnedEnumeration Z T 3 (P.atD T)
      (by simpa using (show 0 < P.L T by linarith [hP.one_le_w])) (by norm_num))) :
    atDLocalDelta T P ≤
      tripleCorrelationEnergy
        (normalizedCoreVec Z T 3 (P.atD T) hconj)
        (packedTripleIndex
          (coreBinnedEnumeration Z T 3 (P.atD T)
      (by simpa using (show 0 < P.L T by linarith [hP.one_le_w]))
            (by norm_num))) q := by
  unfold atDLocalDelta
  have hL : 0 < (P.atD T).L T := by
    simpa using (show 0 < P.L T by linarith [hP.one_le_w])
  have heps : 0 ≤ 12 * P.w / P.L T + 3 * (1 - P.lam) := by
    have hL' : 0 < P.L T := by linarith [hP.one_le_w]
    have hw0 : 0 ≤ P.w := by linarith [hP.one_le_w]
    have hlam0 : 0 ≤ 1 - P.lam := sub_nonneg.mpr hP.lam_le_one
    have hfinite0 : 0 ≤ 12 * P.w / P.L T :=
      div_nonneg (mul_nonneg (by norm_num) hw0) hL'.le
    nlinarith
  apply packedCoreTriple_local_energy Z T (P.atD T) hconj
    (ThmD.cDT P.ϱ P.lam)
    hreal hF hT hc hbudget hL hpos heps
  · intro z z'
    simpa only [Params.atD_L, coreScaledOrdinate] using
      (fullCoreCorrelation_atD_close_endpointR Z hP hwL z z')

end StrictImprovement
end Zeta23

end
