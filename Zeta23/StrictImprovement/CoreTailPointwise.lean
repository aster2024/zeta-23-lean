/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ZetaFiniteNormalization
import Zeta23.PrimeSideA.EndsE1
import Zeta23.PrimeSideA.Bridge

/-!
# Pointwise finite-grid tail for core atoms

The frozen prime-side development already defines

`rho(tau) = a L^2 - sum_{0 <= k < d} phiHat(tau-tau_k)^2`

and proves a pointwise majorant.  This module turns that majorant into an
explicit rational expression in the two endpoint distances and identifies
`rho/(a L^2)` with the norm deficit of the concrete finite core vector.

No asymptotic notation occurs in these statements.

This is a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset Real Set Filter Topology
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open RHLinalg
open ZeroSide
open PrimeSide

variable {cϱ : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}

/-- Explicit decay bound for the one-sided missing-grid majorant. -/
lemma Wfun_le_explicit
    (hF : PrimeSide.LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 < Δ) :
    PrimeSide.Wfun cϱ p Δ ≤
      (cϱ / p.w) ^ 2 / Δ ^ 4 +
        p.h⁻¹ * ((cϱ / p.w) ^ 2 / (3 * Δ ^ 3)) := by
  have hψ0 := PrimeSide.psiA_nonneg_of hF Δ
  have hψ := PrimeSide.psiA_le_div_sq (cϱ := cϱ) (p := p) hΔ.ne'
  have hsq : PrimeSide.psiA cϱ p Δ ^ 2 ≤
      (cϱ / p.w) ^ 2 / Δ ^ 4 := by
    calc PrimeSide.psiA cϱ p Δ ^ 2
        ≤ (cϱ / (p.w * Δ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hψ0 hψ 2
      _ = (cϱ / p.w) ^ 2 / Δ ^ 4 := by field_simp
  have hint := PrimeSide.setIntegral_psiA_sq_Ioi_le_div hF hΔ
  have hh : 0 ≤ p.h⁻¹ := inv_nonneg.mpr (PrimeSide.h_pos hF).le
  unfold PrimeSide.Wfun
  exact add_le_add hsq (mul_le_mul_of_nonneg_left hint hh)

lemma Wfun_antitoneOn
    (hF : PrimeSide.LocalHypsCoreW cϱ p F) :
    AntitoneOn (PrimeSide.Wfun cϱ p) (Set.Ici 0) := by
  intro a ha b hb hab
  unfold PrimeSide.Wfun
  have hψ := PrimeSide.psiA_sq_antitoneOn hF ha hb hab
  have hint := PrimeSide.antitone_setIntegral_psiA_sq_Ioi hF hab
  have hh : 0 ≤ p.h⁻¹ := inv_nonneg.mpr (PrimeSide.h_pos hF).le
  exact add_le_add hψ (mul_le_mul_of_nonneg_left hint hh)

/-- Uniform explicit budget for an interior interval at distance `C` from
both endpoints.  The last term uses `C-1`, not `C`, because the frozen grid
only proves `tau_d > 2T-h` and `h <= 1`. -/
def coreTailBudget (cϱ : ℝ) (p : PrimeSide.Setting) (C : ℝ) : ℝ :=
  2 * ((cϱ / p.w) ^ 2 / C ^ 4 +
    p.h⁻¹ * ((cϱ / p.w) ^ 2 / (3 * C ^ 3))) +
    (cϱ / p.w) ^ 2 / (C - 1) ^ 4

/-- Every point of the core interval has missing-grid mass at most the single
uniform scalar budget above. -/
theorem rho_core_le_budget
    (hF : PrimeSide.LocalHypsCoreW cϱ p F) (hT : 0 < p.T)
    {C τ : ℝ} (hC : 1 < C)
    (hcore : p.T + C ≤ τ ∧ τ ≤ 2 * p.T - C) :
    PrimeSide.rho p F τ ≤ coreTailBudget cϱ p C := by
  have hC0 : 0 ≤ C := by linarith
  have hCm1 : 0 < C - 1 := by linarith
  have hτ : τ ∈ Set.Icc p.T (2 * p.T) := by
    constructor <;> linarith
  have hleft : C ≤ τ - p.T := by linarith
  have hright : C ≤ 2 * p.T - τ := by linarith
  have hh1 := PrimeSide.h_le_one hF
  have htd := PrimeSide.tau_d_gt hF.L_pos hT
  have hafter : C - 1 ≤ p.tau p.d - τ := by linarith
  have hbase := PrimeSide.rho_le_majorant hF hT hτ
  have hWanti := Wfun_antitoneOn hF
  have hWL : PrimeSide.Wfun cϱ p (τ - p.T) ≤
      PrimeSide.Wfun cϱ p C :=
    hWanti hC0 (show 0 ≤ τ - p.T by linarith) hleft
  have hWR : PrimeSide.Wfun cϱ p (2 * p.T - τ) ≤
      PrimeSide.Wfun cϱ p C :=
    hWanti hC0 (show 0 ≤ 2 * p.T - τ by linarith) hright
  have hψanti := PrimeSide.psiA_sq_antitoneOn hF
  have hlast0 : 0 ≤ p.tau p.d - τ := by linarith
  have hlast : PrimeSide.psiA cϱ p (p.tau p.d - τ) ^ 2 ≤
      PrimeSide.psiA cϱ p (C - 1) ^ 2 :=
    hψanti hCm1.le hlast0 hafter
  have hWC := Wfun_le_explicit hF (show 0 < C by linarith)
  have hψ0 := PrimeSide.psiA_nonneg_of hF (C - 1)
  have hψ := PrimeSide.psiA_le_div_sq (cϱ := cϱ) (p := p) hCm1.ne'
  have hlastExplicit : PrimeSide.psiA cϱ p (C - 1) ^ 2 ≤
      (cϱ / p.w) ^ 2 / (C - 1) ^ 4 := by
    calc PrimeSide.psiA cϱ p (C - 1) ^ 2
        ≤ (cϱ / (p.w * (C - 1) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hψ0 hψ 2
      _ = (cϱ / p.w) ^ 2 / (C - 1) ^ 4 := by
        field_simp
  unfold coreTailBudget
  linarith

/-- Fully explicit pointwise bound for `rho`; the last denominator is the
distance from `tau` to the first grid point after the finite range. -/
theorem rho_le_explicit
    (hF : PrimeSide.LocalHypsCoreW cϱ p F) (hT : 0 < p.T)
    {τ : ℝ} (hτ : τ ∈ Set.Icc p.T (2 * p.T))
    (hleft : 0 < τ - p.T) (hright : 0 < 2 * p.T - τ)
    (hafter : 0 < p.tau p.d - τ) :
    PrimeSide.rho p F τ ≤
      (cϱ / p.w) ^ 2 / (τ - p.T) ^ 4 +
        p.h⁻¹ * ((cϱ / p.w) ^ 2 / (3 * (τ - p.T) ^ 3)) +
      ((cϱ / p.w) ^ 2 / (2 * p.T - τ) ^ 4 +
        p.h⁻¹ * ((cϱ / p.w) ^ 2 / (3 * (2 * p.T - τ) ^ 3))) +
      (cϱ / p.w) ^ 2 / (p.tau p.d - τ) ^ 4 := by
  have hbase := PrimeSide.rho_le_majorant hF hT hτ
  have hWL := Wfun_le_explicit hF hleft
  have hWR := Wfun_le_explicit hF hright
  have hψ0 := PrimeSide.psiA_nonneg_of hF (p.tau p.d - τ)
  have hψ := PrimeSide.psiA_le_div_sq (cϱ := cϱ) (p := p) hafter.ne'
  have hlast : PrimeSide.psiA cϱ p (p.tau p.d - τ) ^ 2 ≤
      (cϱ / p.w) ^ 2 / (p.tau p.d - τ) ^ 4 := by
    calc PrimeSide.psiA cϱ p (p.tau p.d - τ) ^ 2
        ≤ (cϱ / (p.w * (p.tau p.d - τ) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hψ0 hψ 2
      _ = (cϱ / p.w) ^ 2 / (p.tau p.d - τ) ^ 4 := by
        field_simp
  exact hbase.trans (add_le_add (add_le_add hWL hWR) hlast)

variable (Z : ZeroConfig) (T C : ℝ) (P : Params)
variable (hconj : PhiHatConj T P)

private abbrev D : ZeroBlockData (ZI Z T) (Fin (P.d T)) :=
  blockData Z T P hconj

/-- The finite core norm deficit is exactly the concrete `rho/(aL^2)`. -/
lemma finiteCoreWeight_eq_one_sub_rho_div
    (hreal : PhiHatReal T P) (hc : 0 < P.a T * P.L T ^ 2)
    (z : CoreSimpleLabel Z T C) :
    finiteCoreWeight Z T C P hconj z =
      1 - PrimeSide.rho (P.toSetting T) (P.localFun T) (z : ℂ).im /
        (P.a T * P.L T ^ 2) := by
  rw [finiteCoreWeight_eq_xsq]
  unfold ZeroSide.RankTraceMult.xsq ZeroSide.ZeroBlockData.vhat
  have hzfixed : (D Z T P hconj).σ z = z :=
    ((D Z T P hconj).mem_onLine).mp (coreOnLine Z T C P hconj z).2
  have hzre : (z : ℂ).re = 1 / 2 := by
    exact (mkData_σ_eq_iff Z T (evalVec Z T P) (evalVec_reflect hconj) z).mp hzfixed
  have hs : ∀ k : Fin (P.d T),
      ‖(D Z T P hconj).v z k / (Real.sqrt (P.a T * P.L T ^ 2) : ℂ)‖ ^ 2 =
        P.phiHatR T ((z : ℂ).im - P.tau T k) ^ 2 /
          (P.a T * P.L T ^ 2) := by
    intro k
    change ‖evalVec Z T P (z : ZI Z T) k /
        (Real.sqrt (P.a T * P.L T ^ 2) : ℂ)‖ ^ 2 =
      P.phiHatR T ((z : ℂ).im - P.tau T k) ^ 2 /
        (P.a T * P.L T ^ 2)
    rw [evalVec, gammaOf_of_re_eq_half hzre, ← Complex.ofReal_sub, hreal,
      norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.mpr hc), div_pow, Real.sq_sqrt hc.le,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hs]
  rw [← Finset.sum_div]
  unfold PrimeSide.rho
  simp only [Params.localFun_a, Params.localFun_phiHat, Params.toSetting_L,
    Params.toSetting_d, Params.toSetting_tau]
  field_simp
  ring

/-- A strict pointwise tail bound is exactly what is needed to justify unit
normalization of a core vector. -/
lemma finiteCoreWeight_pos_of_rho_lt
    (hreal : PhiHatReal T P) (hc : 0 < P.a T * P.L T ^ 2)
    (z : CoreSimpleLabel Z T C)
    (hrho : PrimeSide.rho (P.toSetting T) (P.localFun T) (z : ℂ).im <
      P.a T * P.L T ^ 2) :
    0 < finiteCoreWeight Z T C P hconj z := by
  rw [finiteCoreWeight_eq_one_sub_rho_div Z T C P hconj hreal hc z]
  exact sub_pos.mpr ((div_lt_one hc).2 hrho)

/-- Concrete uniform nonvanishing theorem.  All analytic content is now in
the single explicit scalar gate `coreTailBudget < aL^2`. -/
theorem all_finiteCoreWeight_pos_of_budget
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hl : 1 ≤ l T) (hX : 1 ≤ P.X T) (hT : 0 < T)
    (hC : 1 < C)
    (hc : 0 < P.a T * P.L T ^ 2)
    (hbudget : coreTailBudget P.crho (P.toSetting T) C <
      P.a T * P.L T ^ 2) :
    ∀ z, 0 < finiteCoreWeight Z T C P hconj z := by
  intro z
  have hz := z.2
  simp only [coreSimple, Finset.mem_filter] at hz
  have hF := PrimeSide.localHyps_concrete hP hwL hl hX
  have hrhoLe := rho_core_le_budget hF hT hC hz.2
  have hrho : PrimeSide.rho (P.toSetting T) (P.localFun T) (z : ℂ).im <
      P.a T * P.L T ^ 2 := hrhoLe.trans_lt hbudget
  exact finiteCoreWeight_pos_of_rho_lt Z T C P hconj
    (fun r => GzGp.phiHat_ofReal P T r) hc z hrho

/-! ## A completely explicit `C = 3` discharge

The next estimate deliberately sacrifices the harmless factor `1 / (2 * pi)`:
we use only `h⁻¹ ≤ L`.  This keeps the gate rational and makes it independent
of any numerical approximation to `pi`.  The coarse threshold `cϱ² < L` is
already sufficient for strict positivity of every normalized core atom. -/

/-- At `C = 3`, the scalar tail budget is bounded by a rational polynomial in
`L` and `cϱ`.  No transcendental approximation enters the right-hand side. -/
theorem coreTailBudget_three_le
    (hF : PrimeSide.LocalHypsCoreW cϱ p F) :
    coreTailBudget cϱ p 3 ≤
      cϱ ^ 2 * (2 * p.L / 81 + 113 / 1296) := by
  have hc0 : 0 ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hw0 : 0 < p.w := by linarith [hF.one_le_w]
  have hq0 : 0 ≤ cϱ / p.w := div_nonneg hc0 hw0.le
  have hqle : cϱ / p.w ≤ cϱ := by
    rw [div_le_iff₀ hw0]
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hF.one_le_w)]
  have hq2 : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by nlinarith
  have hh : p.h⁻¹ = p.L / (2 * Real.pi) := by
    unfold PrimeSide.Setting.h
    rw [inv_div]
  have hhL : p.h⁻¹ ≤ p.L := by
    rw [hh, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, hF.L_pos]
  have hq81 : (cϱ / p.w) ^ 2 / 81 ≤ cϱ ^ 2 / 81 :=
    div_le_div_of_nonneg_right hq2 (by norm_num)
  have hq16 : (cϱ / p.w) ^ 2 / 16 ≤ cϱ ^ 2 / 16 :=
    div_le_div_of_nonneg_right hq2 (by norm_num)
  have hprod : p.h⁻¹ * ((cϱ / p.w) ^ 2 / 81) ≤
      p.L * (cϱ ^ 2 / 81) := by
    exact mul_le_mul hhL hq81 (by positivity) hF.L_pos.le
  change
    2 * ((cϱ / p.w) ^ 2 / 81 +
      p.h⁻¹ * ((cϱ / p.w) ^ 2 / 81)) +
        (cϱ / p.w) ^ 2 / 16 ≤
      cϱ ^ 2 * (2 * p.L / 81 + 113 / 1296)
  calc
    2 * ((cϱ / p.w) ^ 2 / 81 +
        p.h⁻¹ * ((cϱ / p.w) ^ 2 / 81)) +
          (cϱ / p.w) ^ 2 / 16
        ≤ 2 * (cϱ ^ 2 / 81 + p.L * (cϱ ^ 2 / 81)) +
          cϱ ^ 2 / 16 :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add hq81 hprod) (by norm_num)) hq16
    _ = cϱ ^ 2 * (2 * p.L / 81 + 113 / 1296) := by ring

/-- The threshold `cϱ² < L` makes the `C = 3` budget strictly smaller than
`L²/2`. -/
theorem coreTailBudget_three_lt_half_L_sq
    (hF : PrimeSide.LocalHypsCoreW cϱ p F) (hlarge : cϱ ^ 2 < p.L) :
    coreTailBudget cϱ p 3 < p.L ^ 2 / 2 := by
  have hbase := coreTailBudget_three_le hF
  have hfac : 0 < 2 * p.L / 81 + 113 / 1296 := by positivity
  have hstrict : cϱ ^ 2 * (2 * p.L / 81 + 113 / 1296) <
      p.L * (2 * p.L / 81 + 113 / 1296) :=
    mul_lt_mul_of_pos_right hlarge hfac
  have hfac_lt : 2 * p.L / 81 + 113 / 1296 < p.L / 2 := by
    nlinarith [hF.eight_le_L]
  have hlast : p.L * (2 * p.L / 81 + 113 / 1296) < p.L ^ 2 / 2 := by
    calc
      p.L * (2 * p.L / 81 + 113 / 1296) < p.L * (p.L / 2) :=
        mul_lt_mul_of_pos_left hfac_lt hF.L_pos
      _ = p.L ^ 2 / 2 := by ring
  exact hbase.trans_lt (hstrict.trans hlast)

/-- Concrete rational discharge of the normalization gate at `C = 3`. -/
theorem concrete_coreTailBudget_three_lt
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hl : 1 ≤ l T) (hX : 1 ≤ P.X T)
    (hlarge : P.crho ^ 2 < P.L T) :
    coreTailBudget P.crho (P.toSetting T) 3 < P.a T * P.L T ^ 2 := by
  have hF := PrimeSide.localHyps_concrete hP hwL hl hX
  have hhalf := Params.half_le_a hP hwL
  have htail := coreTailBudget_three_lt_half_L_sq hF hlarge
  have hscale : P.L T ^ 2 / 2 ≤ P.a T * P.L T ^ 2 := by
    nlinarith [sq_nonneg (P.L T)]
  exact htail.trans_le hscale

/-- The explicit scalar gate holds eventually for every valid fixed taper.
This is the large-`T` wrapper for the rational threshold `crho² < L`; it adds
no asymptotic estimate beyond the already formalized fact `L(T) -> infinity`. -/
theorem eventually_concrete_coreTailBudget_three_lt
    (hP : P.Valid) :
    ∀ᶠ T in atTop,
      coreTailBudget P.crho (P.toSetting T) 3 < P.a T * P.L T ^ 2 := by
  have hlTop : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_id.atTop_div_const (by positivity))
  have hLTop : Tendsto P.L atTop atTop :=
    hlTop.const_mul_atTop hP.lam_pos
  filter_upwards [hLTop.eventually_ge_atTop (8 * P.w),
      hlTop.eventually_ge_atTop 1, hLTop.eventually_ge_atTop 0,
      hLTop.eventually_gt_atTop (P.crho ^ 2)] with T hwL hl hL0 hlarge
  have hX : 1 ≤ P.X T := by
    simpa [Params.X] using Real.one_le_exp hL0
  exact concrete_coreTailBudget_three_lt T P hP hwL hl hX hlarge

/-- Under the explicit large-bandwidth gate `crho² < L`, every finite core
vector at distance three from the endpoints is nonzero and hence can be
unit-normalized. -/
theorem all_finiteCoreWeight_pos_three
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hl : 1 ≤ l T) (hX : 1 ≤ P.X T) (hT : 0 < T)
    (hlarge : P.crho ^ 2 < P.L T) :
    ∀ z, 0 < finiteCoreWeight Z T 3 P hconj z := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hhalf := Params.half_le_a hP hwL
  have hc : 0 < P.a T * P.L T ^ 2 := by
    have ha : 0 < P.a T := by linarith
    exact mul_pos ha (sq_pos_of_pos hL)
  exact all_finiteCoreWeight_pos_of_budget Z T 3 P hconj hP hwL hl hX hT
    (by norm_num) hc (concrete_coreTailBudget_three_lt T P hP hwL hl hX hlarge)

end StrictImprovement
end Zeta23
