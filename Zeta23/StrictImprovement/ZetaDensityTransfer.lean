/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaBoundaryLoss
import Zeta23.StrictImprovement.ZetaCoreBinning

/-!
# Density transfer for the core size and bin parameter

This module records the Riemann--von Mangoldt normalization needed by the
quadratic gain.  In particular,

`coreBinD(T,P) / N(T,2T) -> P.lam`.

The proof keeps the `ell1 = l + c₀` correction and the RvM error explicit;
neither is silently dropped.

This is a source draft pending the pinned Lean build.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace StrictImprovement

/-- The Riemann--von Mangoldt remainder is negligible relative to the dyadic
zero count itself. -/
theorem rvmMainError_isLittleO_N
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    (fun T => (Z.N T (2 * T) : ℝ) -
      T / (2 * Real.pi) * ell1 T) =o[atTop]
        (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨C, T₀, hmain⟩ := hR.main
  have hO :
      (fun T => (Z.N T (2 * T) : ℝ) -
        T / (2 * Real.pi) * ell1 T) =O[atTop] Real.log := by
    refine IsBigO.of_bound |C| ?_
    filter_upwards [eventually_ge_atTop T₀, Assembly.eventually_log_nonneg]
      with T hT hlog
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog]
    calc
      |(Z.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T|
          ≤ C * Real.log T := hmain T hT
      _ ≤ |C| * Real.log T :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hlog
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl Z hR Assembly.isLittleO_log_Tl)

/-- `T = o(N(T,2T))`, in the exact normalization used below. -/
theorem id_isLittleO_N
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    (fun T : ℝ => T) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
  have hT : (fun T : ℝ => T) =o[atTop] (fun T => T * l T) := by
    refine (isLittleO_iff).2 fun c hc => ?_
    filter_upwards [Assembly.tendsto_l_atTop.eventually_ge_atTop c⁻¹,
      eventually_gt_atTop (0 : ℝ)] with T hl hT0
    have hlpos : 0 < l T := (inv_pos.mpr hc).trans_le hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT0,
      abs_of_pos (mul_pos hT0 hlpos)]
    have hone : 1 ≤ c * l T := by
      have := mul_le_mul_of_nonneg_left hl hc.le
      rwa [mul_inv_cancel₀ hc.ne'] at this
    nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hone)]
  exact Assembly.isLittleO_N_of_isLittleO_Tl Z hR hT

/-- Additive form of the bin-density limit. -/
theorem coreBinD_sub_lam_mul_N_isLittleO
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (P : Params) :
    (fun T => coreBinD T P - P.lam * (Z.N T (2 * T) : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
  have h1 := (rvmMainError_isLittleO_N Z hR).const_mul_left (-P.lam)
  have h2 := (id_isLittleO_N Z hR).const_mul_left
    (-P.lam * Assembly.c₀ / (2 * Real.pi))
  refine (h1.add h2).congr_left ?_
  intro T
  unfold coreBinD Params.L
  rw [Assembly.ell1_eq]
  ring

/-- Exact RvM normalization of the interval-binning parameter. -/
theorem tendsto_coreBinD_div_N
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (P : Params) :
    Tendsto (fun T => coreBinD T P / (Z.N T (2 * T) : ℝ))
      atTop (𝓝 P.lam) := by
  have hNtop := Assembly.tendsto_N_atTop Z hR
  have hNpos : ∀ᶠ T in atTop, 0 < (Z.N T (2 * T) : ℝ) :=
    hNtop.eventually_gt_atTop 0
  have hzero :
      Tendsto (fun T =>
        (coreBinD T P - P.lam * (Z.N T (2 * T) : ℝ)) /
          (Z.N T (2 * T) : ℝ)) atTop (𝓝 0) := by
    apply (isLittleO_iff_tendsto' _).mp
      (coreBinD_sub_lam_mul_N_isLittleO Z hR P)
    filter_upwards [hNpos] with T hT
    exact hT.ne'
  refine (tendsto_const_nhds.add hzero).congr' ?_
  filter_upwards [hNpos] with T hT
  field_simp [hT.ne']
  ring

/-- One-sided form consumed by the finite-height gain estimate. -/
theorem eventually_coreBinD_le
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (P : Params)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      coreBinD T P ≤ (P.lam + ε) * (Z.N T (2 * T) : ℝ) := by
  have hratio := (tendsto_coreBinD_div_N Z hR P).eventually
    (eventually_lt_nhds (show P.lam < P.lam + ε by linarith))
  have hNpos := (Assembly.tendsto_N_atTop Z hR).eventually_gt_atTop 0
  filter_upwards [hratio, hNpos] with T hratio hN
  rw [div_lt_iff₀ hN] at hratio
  exact hratio.le

end StrictImprovement
end Zeta23

end
