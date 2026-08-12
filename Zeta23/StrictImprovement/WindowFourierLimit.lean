/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.EndpointKernel
import Zeta23.ThmD.Window
import Zeta23.ThmD.WindowCore

/-!
# Uniform Fourier limit for the Montgomery--Taylor window

For fixed `0 < lam <= 1`, the squared finite window

`phiD^2 = vStar lam (u/L) * phi_flat(u)^2`

differs in `L^1` by at most `2*w` from the sharp window
`1_[−L/2,L/2] vStar lam (u/L)`.  Consequently its real Fourier
transform, after division by `L`, differs uniformly in the frequency from
the scale-free kernel by at most `2*w/L`.

This is the quantitative numerator bridge that was missing from the first
strict-improvement Lean draft.  It is a source draft until checked with the
pinned Lean toolchain in `LEAN_FORMALIZATION_PLAN.md`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace Zeta23
namespace StrictImprovement

/-- Fixed-`lam` scale-free real Fourier kernel. -/
def endpointKAt (lam x : ℝ) : ℝ :=
  ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
    ThmD.vStar lam s * Real.cos (x * s)

/-- Fixed-`lam` kernel normalized at zero. -/
def endpointRAt (lam x : ℝ) : ℝ := endpointKAt lam x / endpointKAt lam 0

@[simp] theorem endpointKAt_one (x : ℝ) : endpointKAt 1 x = endpointK x := rfl

@[simp] theorem endpointRAt_one (x : ℝ) : endpointRAt 1 x = endpointR x := rfl

/-- Real part of the paper Fourier transform is the cosine transform. -/
lemma re_paperFT_ofReal_eq_integral_mul_cos
    {f : ℝ → ℝ} (hf : Integrable f) (r : ℝ) :
    (paperFT (fun u => (f u : ℂ)) r).re =
      ∫ u, f u * Real.cos (r * u) := by
  let e : ℝ → ℂ := fun u => Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))
  have hec : Continuous e := by
    dsimp [e]
    fun_prop
  have henorm : ∀ u, ‖e u‖ = 1 := by
    intro u
    dsimp [e]
    rw [Zeta23.norm_cexp_I_mul]
    simp
  have hprod : Integrable (fun u => (f u : ℂ) * e u) := by
    have hi := (hf.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) hec.aestronglyMeasurable
      (ae_of_all _ fun u => by rw [henorm])
    have hmul : (fun u => (f u : ℂ) * e u) = fun u => e u * (f u : ℂ) := by
      funext u
      exact mul_comm _ _
    rw [hmul]
    exact hi
  rw [paperFT_def, ← Zeta23.integral_re_C hprod]
  apply MeasureTheory.integral_congr_ae
  apply ae_of_all
  intro u
  dsimp [e]
  simp only [Complex.re_ofReal_mul]
  have he : Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re]

/-- The real Fourier transform is `L^1`-Lipschitz, uniformly in frequency. -/
lemma abs_re_paperFT_sub_le_integral_abs
    {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    |(paperFT (fun u => (f u : ℂ)) r).re -
        (paperFT (fun u => (g u : ℂ)) r).re| ≤
      ∫ u, |f u - g u| := by
  rw [re_paperFT_ofReal_eq_integral_mul_cos hf,
    re_paperFT_ofReal_eq_integral_mul_cos hg]
  have hfc : Integrable (fun u => f u * Real.cos (r * u)) :=
    by
      have hi := hf.bdd_mul (c := 1)
        (by fun_prop : Continuous fun u : ℝ => Real.cos (r * u)).aestronglyMeasurable
        (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
      simpa only [Pi.mul_apply, mul_comm] using hi
  have hgc : Integrable (fun u => g u * Real.cos (r * u)) :=
    by
      have hi := hg.bdd_mul (c := 1)
        (by fun_prop : Continuous fun u : ℝ => Real.cos (r * u)).aestronglyMeasurable
        (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
      simpa only [Pi.mul_apply, mul_comm] using hi
  rw [← MeasureTheory.integral_sub hfc hgc]
  calc
    |∫ u, f u * Real.cos (r * u) - g u * Real.cos (r * u)|
        ≤ ∫ u, |f u * Real.cos (r * u) - g u * Real.cos (r * u)| :=
          MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u, |f u - g u| := by
      apply MeasureTheory.integral_mono_of_nonneg
        (ae_of_all _ fun u => abs_nonneg _)
        (hf.sub hg).abs
      apply ae_of_all
      intro u
      change |f u * Real.cos (r * u) - g u * Real.cos (r * u)| ≤ |f u - g u|
      rw [show f u * Real.cos (r * u) - g u * Real.cos (r * u) =
          (f u - g u) * Real.cos (r * u) by ring, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- The sharp window is integrable. -/
lemma integrable_sharpW (lam : ℝ) {L : ℝ} (hL : 0 < L) :
    Integrable (ThmD.sharpW lam L) := by
  unfold ThmD.sharpW
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
    (((by unfold ThmD.vStar; fun_prop :
      Continuous fun u : ℝ => ThmD.vStar lam (u / L)).continuousOn).integrableOn_compact
        isCompact_Icc)

/-- The squared smooth window is integrable. -/
lemma integrable_phiD_sq
    {rho : ℝ → ℝ} {lam L w : ℝ}
    (hrho : TaperProfile rho) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hw0 : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun u => ThmD.phiD rho lam L w u ^ 2) := by
  have hc : Continuous (fun u => ThmD.phiD rho lam L w u ^ 2) :=
    ((ThmD.phiD_contDiff hrho hlam0 hlam1 hw0 hwL).pow 2).continuous
  have hs : HasCompactSupport (fun u => ThmD.phiD rho lam L w u ^ 2) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -(L / 2)) (b := L / 2))
    intro u hu
    rw [Function.mem_support] at hu
    by_contra hmem
    apply hu
    have hout : L / 2 ≤ |u| := by
      simp only [mem_Icc, not_and_or, not_le] at hmem
      rcases hmem with hleft | hright
      · rw [abs_of_neg (by linarith : u < 0)]
        linarith
      · rw [abs_of_pos (by linarith : 0 < u)]
        linarith
    rw [ThmD.phiD_eq_zero hrho hw0 hout, zero_pow two_ne_zero]
  exact hc.integrable_of_hasCompactSupport hs

/-- The sharp Fourier transform is exactly `L * endpointKAt`. -/
lemma sharpW_paperFT_re_scaled
    {lam L : ℝ} (hL : 0 < L) (x : ℝ) :
    (paperFT (fun u => (ThmD.sharpW lam L u : ℂ)) (x / L)).re =
      L * endpointKAt lam x := by
  rw [← Complex.ofReal_div]
  rw [re_paperFT_ofReal_eq_integral_mul_cos (integrable_sharpW lam hL)]
  unfold ThmD.sharpW
  have hind :
      (fun u => (Icc (-(L / 2)) (L / 2)).indicator
          (fun u => ThmD.vStar lam (u / L)) u * Real.cos (x / L * u)) =
        (Icc (-(L / 2)) (L / 2)).indicator
          (fun u => ThmD.vStar lam (u / L) * Real.cos (x / L * u)) := by
    funext u
    by_cases hu : u ∈ Icc (-(L / 2)) (L / 2) <;> simp [hu]
  rw [hind, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
  have hscale := intervalIntegral.integral_comp_div
    (a := -(L / 2)) (b := L / 2)
    (f := fun s : ℝ => ThmD.vStar lam s * Real.cos (x * s)) hL.ne'
  rw [smul_eq_mul] at hscale
  have hleft : -(L / 2) / L = -(1 : ℝ) / 2 := by
    field_simp
    ring
  have hright : L / 2 / L = (1 : ℝ) / 2 := by
    field_simp
    ring
  rw [hleft, hright] at hscale
  rw [← hscale]
  apply intervalIntegral.integral_congr
  intro u _
  congr 2
  field_simp
  ring

/-- Uniform finite-window numerator error.  No restriction on `x` is needed. -/
theorem phiD_VPhiR_scaled_close_endpointKAt
    {rho : ℝ → ℝ} {lam L w : ℝ}
    (hrho : TaperProfile rho) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hw0 : 0 < w) (hwL : 2 * w ≤ L) (x : ℝ) :
    |L⁻¹ * AdmWindow.VPhiR (ThmD.phiD rho lam L w) (x / L) -
        endpointKAt lam x| ≤ 2 * w / L := by
  have hL : 0 < L := by linarith
  have hfourier := abs_re_paperFT_sub_le_integral_abs
    (integrable_phiD_sq hrho hlam0 hlam1 hw0 hwL)
    (integrable_sharpW lam hL) (x / L)
  have hL1 := ThmD.integral_abs_phiDsq_sub_sharp
    hrho hlam0 hlam1 hw0 hwL
  rw [Complex.ofReal_div] at hfourier
  rw [sharpW_paperFT_re_scaled hL] at hfourier
  have hraw :
      |AdmWindow.VPhiR (ThmD.phiD rho lam L w) (x / L) -
        L * endpointKAt lam x| ≤ 2 * w := hfourier.trans hL1
  have hrewrite :
      L⁻¹ * AdmWindow.VPhiR (ThmD.phiD rho lam L w) (x / L) - endpointKAt lam x =
        L⁻¹ * (AdmWindow.VPhiR (ThmD.phiD rho lam L w) (x / L) -
          L * endpointKAt lam x) := by
    field_simp
    ring
  rw [hrewrite, abs_mul, abs_of_pos (inv_pos.mpr hL)]
  calc
    L⁻¹ * |AdmWindow.VPhiR (ThmD.phiD rho lam L w) (x / L) -
        L * endpointKAt lam x| ≤ L⁻¹ * (2 * w) :=
          mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hL.le)
    _ = 2 * w / L := by field_simp; ring

/-- The zero-frequency fixed-`lam` kernel is the scale-free mass `aStar`. -/
@[simp] theorem endpointKAt_zero (lam : ℝ) :
    endpointKAt lam 0 = ThmD.aStar lam := by
  unfold endpointKAt ThmD.aStar
  apply intervalIntegral.integral_congr
  intro s _
  simp

/-- For `0 < lam <= 1`, the fixed-`lam` mass is at least `3/4`. -/
theorem three_quarters_le_endpointKAt_zero
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    3 / 4 ≤ endpointKAt lam 0 := by
  rw [endpointKAt_zero]
  unfold ThmD.aStar
  have hconst : IntervalIntegrable (fun _ : ℝ => (3 / 4 : ℝ)) volume
      (-(1 : ℝ) / 2) (1 / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hv : IntervalIntegrable (ThmD.vStar lam) volume
      (-(1 : ℝ) / 2) (1 / 2) := by
    unfold ThmD.vStar
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono := intervalIntegral.integral_mono_on (by norm_num) hconst hv
    (fun s hs => by
      have habs : |s| ≤ (1 : ℝ) / 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
      simpa using ThmD.cos_factor_ge (lam := lam) (L := (1 : ℝ))
        hlam0 hlam1 (by norm_num) (u := s) habs)
  norm_num at hmono ⊢
  exact hmono

/-- Every fixed-`lam` coefficient is bounded by its zero-frequency mass. -/
theorem endpointKAt_abs_le_zero
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (x : ℝ) :
    |endpointKAt lam x| ≤ endpointKAt lam 0 := by
  let f : ℝ → ℝ := fun s => ThmD.vStar lam s * Real.cos (x * s)
  let v : ℝ → ℝ := fun s => ThmD.vStar lam s
  have hf : IntervalIntegrable f volume (-(1 : ℝ) / 2) (1 / 2) := by
    dsimp [f]
    unfold ThmD.vStar
    apply Continuous.intervalIntegrable
    fun_prop
  have hv : IntervalIntegrable v volume (-(1 : ℝ) / 2) (1 / 2) := by
    dsimp [v]
    unfold ThmD.vStar
    apply Continuous.intervalIntegrable
    fun_prop
  have habs := intervalIntegral.abs_integral_le_integral_abs
    (μ := volume) (by norm_num : (-(1 : ℝ) / 2) ≤ 1 / 2) (f := f)
  have hmono :
      (∫ s in (-(1 : ℝ) / 2)..(1 / 2), |f s|) ≤
        ∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s := by
    refine intervalIntegral.integral_mono_on (by norm_num) hf.abs hv ?_
    intro s hs
    have hv0 : 0 ≤ v s := by
      have habs : |s| ≤ (1 : ℝ) / 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
      have hge := ThmD.cos_factor_ge (lam := lam) (L := (1 : ℝ))
        hlam0 hlam1 (by norm_num) (u := s) habs
      dsimp [v]
      simpa using hge.trans' (by norm_num : (0 : ℝ) ≤ 3 / 4)
    dsimp [f]
    rw [abs_mul, abs_of_nonneg hv0]
    exact mul_le_of_le_one_right hv0 (Real.abs_cos_le_one _)
  simpa [endpointKAt, f, v] using habs.trans hmono

/-- Pointwise profile convergence as `lam -> 1-`, with a rational Lipschitz
constant. -/
lemma vStar_close_one
    {lam s : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hs : |s| ≤ (1 : ℝ) / 2) :
    |ThmD.vStar lam s - ThmD.vStar 1 s| ≤ 1 - lam := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hcoef : Real.sqrt 2 * |s| ≤ 1 := by
    calc
      Real.sqrt 2 * |s| ≤ 2 * ((1 : ℝ) / 2) :=
        mul_le_mul hsqrt2 hs (abs_nonneg s) (by norm_num)
      _ = 1 := by norm_num
  unfold ThmD.vStar
  calc
    |Real.cos (Real.sqrt 2 * lam * s) -
        Real.cos (Real.sqrt 2 * 1 * s)|
        ≤ |Real.sqrt 2 * lam * s - Real.sqrt 2 * 1 * s| :=
          Real.abs_cos_sub_cos_le _ _
    _ = Real.sqrt 2 * |s| * (1 - lam) := by
      rw [show Real.sqrt 2 * lam * s - Real.sqrt 2 * 1 * s =
          Real.sqrt 2 * s * (lam - 1) by ring,
        abs_mul, abs_mul, abs_of_nonneg hsqrt0,
        abs_of_nonpos (sub_nonpos.mpr hlam1)]
      ring
    _ ≤ 1 * (1 - lam) :=
      mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hlam1)
    _ = 1 - lam := one_mul _

/-- The fixed-`lam` Fourier kernel converges uniformly in frequency to the
endpoint kernel. -/
theorem endpointKAt_close_one
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (x : ℝ) :
    |endpointKAt lam x - endpointK x| ≤ 1 - lam := by
  let f : ℝ → ℝ := fun s =>
    (ThmD.vStar lam s - ThmD.vStar 1 s) * Real.cos (x * s)
  have hf : IntervalIntegrable f volume (-(1 : ℝ) / 2) (1 / 2) := by
    dsimp [f]
    unfold ThmD.vStar
    apply Continuous.intervalIntegrable
    fun_prop
  have hconst : IntervalIntegrable (fun _ : ℝ => 1 - lam) volume
      (-(1 : ℝ) / 2) (1 / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have habs :
      |(∫ s in (-(1 : ℝ) / 2)..(1 / 2), f s)| ≤
        ∫ s in (-(1 : ℝ) / 2)..(1 / 2), |f s| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have hmono :
      (∫ s in (-(1 : ℝ) / 2)..(1 / 2), |f s|) ≤
        ∫ _s in (-(1 : ℝ) / 2)..(1 / 2), (1 - lam) := by
    refine intervalIntegral.integral_mono_on (by norm_num) hf.abs hconst ?_
    intro s hs
    have hsabs : |s| ≤ (1 : ℝ) / 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
    dsimp [f]
    rw [abs_mul]
    calc
      |ThmD.vStar lam s - ThmD.vStar 1 s| * |Real.cos (x * s)|
          ≤ (1 - lam) * 1 :=
            mul_le_mul (vStar_close_one hlam0 hlam1 hsabs)
              (Real.abs_cos_le_one _) (abs_nonneg _) (sub_nonneg.mpr hlam1)
      _ = 1 - lam := mul_one _
  have hrewrite : endpointKAt lam x - endpointK x =
      ∫ s in (-(1 : ℝ) / 2)..(1 / 2), f s := by
    unfold endpointKAt endpointK
    rw [← intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; unfold ThmD.vStar; fun_prop)
      (by apply Continuous.intervalIntegrable; unfold ThmD.vStar; fun_prop)]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp [f]
    ring
  rw [hrewrite]
  calc
    |∫ s in (-(1 : ℝ) / 2)..(1 / 2), f s|
        ≤ ∫ s in (-(1 : ℝ) / 2)..(1 / 2), |f s| := habs
    _ ≤ ∫ _s in (-(1 : ℝ) / 2)..(1 / 2), (1 - lam) := hmono
    _ = 1 - lam := by norm_num

/-- A reusable normalization estimate for two scalar kernels. -/
lemma normalized_quotient_close
    {A B a b eNum eDen : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hB : |B| ≤ b)
    (hNum : |A - B| ≤ eNum) (hDen : |a - b| ≤ eDen)
    (heNum : 0 ≤ eNum) (heDen : 0 ≤ eDen) :
    |A / a - B / b| ≤ (eNum + eDen) / a := by
  have hid : A / a - B / b =
      (A - B) / a + B * (b - a) / (a * b) := by
    field_simp [ha.ne', hb.ne']
    ring
  rw [hid]
  calc
    |(A - B) / a + B * (b - a) / (a * b)|
        ≤ |(A - B) / a| + |B * (b - a) / (a * b)| := abs_add_le _ _
    _ ≤ eNum / a + eDen / a := by
      apply add_le_add
      · rw [abs_div, abs_of_pos ha]
        exact div_le_div_of_nonneg_right hNum ha.le
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb,
          abs_sub_comm]
        calc
          |B| * |a - b| / (a * b) ≤ b * eDen / (a * b) := by
            gcongr
          _ = eDen / a := by field_simp [ha.ne', hb.ne']
    _ = (eNum + eDen) / a := by ring

/-- Uniform normalized fixed-`lam` to endpoint comparison. -/
theorem endpointRAt_close_endpointR
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (x : ℝ) :
    |endpointRAt lam x - endpointR x| ≤ 3 * (1 - lam) := by
  have ha34 := three_quarters_le_endpointKAt_zero hlam0 hlam1
  have ha : 0 < endpointKAt lam 0 := lt_of_lt_of_le (by norm_num) ha34
  have hb : 0 < endpointK 0 := endpointK_zero_pos
  have hNum := endpointKAt_close_one hlam0.le hlam1 x
  have hDen := endpointKAt_close_one hlam0.le hlam1 0
  have hq := normalized_quotient_close ha hb (endpointK_abs_le_zero x)
    hNum (by simpa using hDen)
    (sub_nonneg.mpr hlam1) (sub_nonneg.mpr hlam1)
  unfold endpointRAt endpointR
  have hd0 : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
  calc
    |endpointKAt lam x / endpointKAt lam 0 - endpointK x / endpointK 0|
        ≤ ((1 - lam) + (1 - lam)) / endpointKAt lam 0 := hq
    _ ≤ 3 * (1 - lam) := by
      apply (div_le_iff₀ ha).2
      have hmul : 0 ≤ (1 - lam) * (endpointKAt lam 0 - 3 / 4) :=
        mul_nonneg hd0 (sub_nonneg.mpr ha34)
      nlinarith

/-- The finite-window kernel, normalized by its actual zero-frequency mass. -/
def phiDNormalizedKernel
    (rho : ℝ → ℝ) (lam L w x : ℝ) : ℝ :=
  (L⁻¹ * AdmWindow.VPhiR (ThmD.phiD rho lam L w) (x / L)) /
    AdmWindow.av (ThmD.phiD rho lam L w) L

/-- Uniform normalization of the finite window.  The explicit `12*w/L`
comes from `2*w/L` in the numerator, `4*w/L` in the mass, and the rational
lower bound `a_D >= 1/2` once `16*w <= L`. -/
theorem phiDNormalizedKernel_close_endpointRAt
    {rho : ℝ → ℝ} {lam L w : ℝ}
    (hrho : TaperProfile rho) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 16 * w ≤ L) (x : ℝ) :
    |phiDNormalizedKernel rho lam L w x - endpointRAt lam x| ≤
      12 * w / L := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  have hL : 0 < L := by linarith
  have hwL2 : 2 * w ≤ L := by linarith
  let aD := AdmWindow.av (ThmD.phiD rho lam L w) L
  let nD := L⁻¹ * AdmWindow.VPhiR (ThmD.phiD rho lam L w) (x / L)
  have hNum : |nD - endpointKAt lam x| ≤ 2 * w / L := by
    dsimp [nD]
    exact phiD_VPhiR_scaled_close_endpointKAt
      hrho hlam0 hlam1 hw0 hwL2 x
  have hDen : |aD - endpointKAt lam 0| ≤ 4 * w / L := by
    dsimp [aD]
    simpa [AdmWindow.av] using
      (ThmD.aD_close hrho hlam0 hlam1 hw (by linarith : 8 * w ≤ L))
  have he14 : 4 * w / L ≤ 1 / 4 := by
    apply (div_le_iff₀ hL).2
    nlinarith
  have hb34 := three_quarters_le_endpointKAt_zero hlam0 hlam1
  have haHalf : 1 / 2 ≤ aD := by
    have hlo := (abs_le.mp hDen).1
    linarith
  have ha : 0 < aD := lt_of_lt_of_le (by norm_num) haHalf
  have hb : 0 < endpointKAt lam 0 :=
    lt_of_lt_of_le (by norm_num) hb34
  have hq := normalized_quotient_close ha hb
    (endpointKAt_abs_le_zero hlam0 hlam1 x) hNum hDen
    (by positivity : 0 ≤ 2 * w / L) (by positivity : 0 ≤ 4 * w / L)
  unfold phiDNormalizedKernel endpointRAt
  change |nD / aD - endpointKAt lam x / endpointKAt lam 0| ≤ 12 * w / L
  calc
    |nD / aD - endpointKAt lam x / endpointKAt lam 0|
        ≤ (2 * w / L + 4 * w / L) / aD := hq
    _ ≤ 12 * w / L := by
      apply (div_le_iff₀ ha).2
      have ht0 : 0 ≤ w / L := div_nonneg hw0.le hL.le
      have hmul : 0 ≤ (w / L) * (aD - 1 / 2) :=
        mul_nonneg ht0 (sub_nonneg.mpr haHalf)
      calc
        2 * w / L + 4 * w / L = 6 * (w / L) := by ring
        _ ≤ 12 * (w / L) * aD := by nlinarith [hmul]
        _ = 12 * w / L * aD := by ring

end StrictImprovement
end Zeta23

end
