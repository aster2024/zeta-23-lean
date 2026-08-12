/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.CorrelationNormalization
import Zeta23.StrictImprovement.CoreTailPointwise

/-!
# Pointwise finite/full correlation transfer on the zeta core

At the concrete core distance `C=3`, the finite correlation is `Kfun/(aL²)`
followed by the two vector norm factors, while the full Poisson correlation is
`Kinf/(aL²)`.  This module proves the exact uniform estimate

`|finiteNormalizedCorrelation - fullCorrelation| <= 2*budget/(aL²)`.

It uses only the frozen Poisson-tail identities, finite Cauchy--Schwarz, and
the scalar normalization lemma.  The later comparison of the full
correlation with the limiting endpoint kernel is intentionally separate.
-/

noncomputable section

open Real Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open ZeroSide PrimeSide

variable (Z : ZeroConfig) (T : ℝ) (P : Params)
variable (hconj : PhiHatConj T P)

private abbrev p : PrimeSide.Setting := P.toSetting T
private abbrev F : PrimeSide.LocalFun := P.localFun T
private abbrev mass : ℝ := P.a T * P.L T ^ 2

/-- Full-grid normalized real correlation. -/
def fullCoreCorrelation (z z' : CoreSimpleLabel Z T 3) : ℝ :=
  PrimeSide.Kinf (p T P) (F T P) (z : ℂ).im (z' : ℂ).im / mass T P

/-- Finite correlation after both finite vectors have been unit-normalized. -/
def finiteNormalizedCoreCorrelation (z z' : CoreSimpleLabel Z T 3) : ℝ :=
  (PrimeSide.Kfun (p T P) (F T P) (z : ℂ).im (z' : ℂ).im / mass T P) /
    (Real.sqrt (finiteCoreWeight Z T 3 P hconj z) *
      Real.sqrt (finiteCoreWeight Z T 3 P hconj z'))

private lemma core_mem_bounds (z : CoreSimpleLabel Z T 3) :
    T + 3 ≤ (z : ℂ).im ∧ (z : ℂ).im ≤ 2 * T - 3 := by
  have hz := z.2
  simp only [coreSimple, Finset.mem_filter] at hz
  exact hz.2

private lemma core_re_eq_half (z : CoreSimpleLabel Z T 3) :
    (z : ℂ).re = 1 / 2 := by
  have hz := z.2
  simp only [coreSimple, nearSimple, Finset.mem_filter, Finset.mem_univ,
    true_and] at hz
  exact hz.1.1

private lemma finiteCoreVec_apply_real
    (hreal : PhiHatReal T P) (z : CoreSimpleLabel Z T 3)
    (k : Fin (P.d T)) :
    finiteCoreVec Z T 3 P hconj z k =
      (P.phiHatR T ((z : ℂ).im - P.tau T k) : ℂ) /
        (Real.sqrt (mass T P) : ℂ) := by
  change P.phiHat T (gammaOf (z : ℂ) - P.tau T k) /
      (Real.sqrt (mass T P) : ℂ) = _
  rw [gammaOf_of_re_eq_half (core_re_eq_half Z T z),
    ← Complex.ofReal_sub, hreal]

/-- The abstract Gram entry of the unitized finite vectors is exactly the
real scalar `finiteNormalizedCoreCorrelation`. -/
theorem gramMatrix_normalizedCoreVec_eq_finiteCorrelation
    (hreal : PhiHatReal T P) (hc : 0 < mass T P)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 P hconj z)
    (z z' : CoreSimpleLabel Z T 3) :
    gramMatrix (normalizedCoreVec Z T 3 P hconj) z z' =
      (finiteNormalizedCoreCorrelation Z T P hconj z z' : ℂ) := by
  unfold gramMatrix normalizedCoreVec unitize
  simp only [dotProduct, Pi.star_apply]
  simp_rw [finiteCoreVec_apply_real Z T P hconj hreal]
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
  unfold finiteNormalizedCoreCorrelation
  have hK : PrimeSide.Kfun (p T P) (F T P) (z : ℂ).im (z' : ℂ).im =
      ∑ k : Fin (P.d T),
        P.phiHatR T ((z : ℂ).im - P.tau T k) *
          P.phiHatR T ((z' : ℂ).im - P.tau T k) := by
    rfl
  rw [hK]
  change (∑ k : Fin (P.d T),
      (P.phiHatR T ((z : ℂ).im - P.tau T k) : ℂ) /
          (Real.sqrt (mass T P) : ℂ) /
          (Real.sqrt (finiteCoreWeight Z T 3 P hconj z) : ℂ) *
        ((P.phiHatR T ((z' : ℂ).im - P.tau T k) : ℂ) /
          (Real.sqrt (mass T P) : ℂ) /
          (Real.sqrt (finiteCoreWeight Z T 3 P hconj z') : ℂ))) = _
  have hcroot : (Real.sqrt (P.a T * P.L T ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  have hzroot :
      (Real.sqrt (finiteCoreWeight Z T 3 P hconj z) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (hpos z)).ne'
  have hz'root :
      (Real.sqrt (finiteCoreWeight Z T 3 P hconj z') : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (hpos z')).ne'
  have hmassc : (mass T P : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hmassroot :
      ((Real.sqrt (P.a T * P.L T ^ 2) : ℂ)) ^ 2 =
        (mass T P : ℂ) := by
    change ((Real.sqrt (P.a T * P.L T ^ 2) : ℂ)) ^ 2 =
      ((P.a T * P.L T ^ 2 : ℝ) : ℂ)
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  -- Normalize each summand before summing.  A global ring pass can otherwise
  -- normalize inside the opaque `phiHatR` arguments and hide their equality.
  have hterm (k : Fin (P.d T)) :
      ((P.phiHatR T ((z : ℂ).im - P.tau T k) : ℂ) /
          (Real.sqrt (mass T P) : ℂ) /
          (Real.sqrt (finiteCoreWeight Z T 3 P hconj z) : ℂ)) *
        ((P.phiHatR T ((z' : ℂ).im - P.tau T k) : ℂ) /
          (Real.sqrt (mass T P) : ℂ) /
          (Real.sqrt (finiteCoreWeight Z T 3 P hconj z') : ℂ)) =
      ((P.phiHatR T ((z : ℂ).im - P.tau T k) *
          P.phiHatR T ((z' : ℂ).im - P.tau T k) : ℝ) : ℂ) /
        ((mass T P : ℂ) *
          (Real.sqrt (finiteCoreWeight Z T 3 P hconj z) : ℂ) *
          (Real.sqrt (finiteCoreWeight Z T 3 P hconj z') : ℂ)) := by
    field_simp [hcroot, hzroot, hz'root, hmassc]
    rw [hmassroot]
    ring
  simp_rw [hterm]
  rw [Finset.sum_div]
  push_cast
  field_simp [hmassc, hzroot, hz'root]
  ring

/-- The pointwise tail budget places every finite squared norm in
`[1-q,1]`, where `q=budget/(aL²)`. -/
theorem finiteCoreWeight_mem_budget
    {cRho : ℝ}
    (hreal : PhiHatReal T P)
    (hF : PrimeSide.LocalHypsCoreW cRho (p T P) (F T P))
    (hT : 0 < T) (hc : 0 < mass T P)
    (z : CoreSimpleLabel Z T 3) :
    1 - coreTailBudget cRho (p T P) 3 / mass T P ≤
        finiteCoreWeight Z T 3 P hconj z ∧
      finiteCoreWeight Z T 3 P hconj z ≤ 1 := by
  have hrho0 := PrimeSide.rho_nonneg hF (z : ℂ).im
  have hrhole := rho_core_le_budget hF hT (by norm_num)
    (core_mem_bounds Z T z)
  rw [finiteCoreWeight_eq_one_sub_rho_div Z T 3 P hconj hreal hc z]
  constructor
  · have hdiv := div_le_div_of_nonneg_right hrhole hc.le
    linarith
  · have hdiv0 : 0 ≤
      PrimeSide.rho (p T P) (F T P) (z : ℂ).im / mass T P :=
      div_nonneg hrho0 hc.le
    linarith

/-- Finite Cauchy--Schwarz in the exact normalized scalar variables. -/
theorem finiteKfun_div_mass_abs_le_sqrt_weights
    (hreal : PhiHatReal T P) (hc : 0 < mass T P)
    (z z' : CoreSimpleLabel Z T 3) :
    |PrimeSide.Kfun (p T P) (F T P) (z : ℂ).im (z' : ℂ).im / mass T P| ≤
      Real.sqrt (finiteCoreWeight Z T 3 P hconj z) *
        Real.sqrt (finiteCoreWeight Z T 3 P hconj z') := by
  have ha : P.a T ≠ 0 := by
    intro ha
    apply hc.ne'
    simp [mass, ha]
  have hL : P.L T ≠ 0 := by
    intro hL
    apply hc.ne'
    simp [mass, hL]
  let S₁ : ℝ := ∑ k : Fin (P.d T),
    P.phiHatR T ((z : ℂ).im - P.tau T k) ^ 2
  let S₂ : ℝ := ∑ k : Fin (P.d T),
    P.phiHatR T ((z' : ℂ).im - P.tau T k) ^ 2
  have hS₁ : S₁ = mass T P * finiteCoreWeight Z T 3 P hconj z := by
    rw [finiteCoreWeight_eq_one_sub_rho_div Z T 3 P hconj hreal hc z]
    unfold S₁ PrimeSide.rho
    simp only [Params.localFun_a, Params.localFun_phiHat, Params.toSetting_L,
      Params.toSetting_d, Params.toSetting_tau]
    change S₁ = mass T P * (1 - (mass T P - S₁) / mass T P)
    field_simp [hc.ne', ha, hL]
    ring
  have hS₂ : S₂ = mass T P * finiteCoreWeight Z T 3 P hconj z' := by
    rw [finiteCoreWeight_eq_one_sub_rho_div Z T 3 P hconj hreal hc z']
    unfold S₂ PrimeSide.rho
    simp only [Params.localFun_a, Params.localFun_phiHat, Params.toSetting_L,
      Params.toSetting_d, Params.toSetting_tau]
    change S₂ = mass T P * (1 - (mass T P - S₂) / mass T P)
    field_simp [hc.ne', ha, hL]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k : Fin (P.d T) => P.phiHatR T ((z : ℂ).im - P.tau T k))
    (fun k : Fin (P.d T) => P.phiHatR T ((z' : ℂ).im - P.tau T k))
  have hK : PrimeSide.Kfun (p T P) (F T P) (z : ℂ).im (z' : ℂ).im =
      ∑ k : Fin (P.d T),
        P.phiHatR T ((z : ℂ).im - P.tau T k) *
          P.phiHatR T ((z' : ℂ).im - P.tau T k) := by
    rfl
  rw [← hK] at hCS
  change (PrimeSide.Kfun (p T P) (F T P) (z : ℂ).im (z' : ℂ).im) ^ 2 ≤
    S₁ * S₂ at hCS
  rw [hS₁, hS₂] at hCS
  have hw₁0 := finiteCoreWeight_nonneg Z T 3 P hconj z
  have hw₂0 := finiteCoreWeight_nonneg Z T 3 P hconj z'
  have hdivsq :
      (PrimeSide.Kfun (p T P) (F T P) (z : ℂ).im (z' : ℂ).im /
        mass T P) ^ 2 ≤
        finiteCoreWeight Z T 3 P hconj z *
          finiteCoreWeight Z T 3 P hconj z' := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hc)).2
    nlinarith
  have hsqrtSq :
      (Real.sqrt (finiteCoreWeight Z T 3 P hconj z) *
        Real.sqrt (finiteCoreWeight Z T 3 P hconj z')) ^ 2 =
        finiteCoreWeight Z T 3 P hconj z *
          finiteCoreWeight Z T 3 P hconj z' := by
    rw [mul_pow, Real.sq_sqrt hw₁0, Real.sq_sqrt hw₂0]
  have hleft0 : 0 ≤
      |PrimeSide.Kfun (p T P) (F T P) (z : ℂ).im (z' : ℂ).im /
        mass T P| := abs_nonneg _
  have hright0 : 0 ≤
      Real.sqrt (finiteCoreWeight Z T 3 P hconj z) *
        Real.sqrt (finiteCoreWeight Z T 3 P hconj z') := by positivity
  nlinarith [sq_abs (PrimeSide.Kfun (p T P) (F T P)
    (z : ℂ).im (z' : ℂ).im / mass T P)]

/-- Unitized finite correlations are bounded by one. -/
theorem finiteNormalizedCoreCorrelation_abs_le_one
    (hreal : PhiHatReal T P) (hc : 0 < mass T P)
    (hpos : ∀ z, 0 < finiteCoreWeight Z T 3 P hconj z)
    (z z' : CoreSimpleLabel Z T 3) :
    |finiteNormalizedCoreCorrelation Z T P hconj z z'| ≤ 1 := by
  have hk := finiteKfun_div_mass_abs_le_sqrt_weights
    Z T P hconj hreal hc z z'
  have hu : 0 < Real.sqrt (finiteCoreWeight Z T 3 P hconj z) *
      Real.sqrt (finiteCoreWeight Z T 3 P hconj z') :=
    mul_pos (Real.sqrt_pos.mpr (hpos z)) (Real.sqrt_pos.mpr (hpos z'))
  unfold finiteNormalizedCoreCorrelation
  rw [abs_div, abs_of_pos hu, div_le_one hu]
  exact hk

/-- Exact uniform finite/full correlation error at core distance three. -/
theorem finiteNormalizedCoreCorrelation_close_full
    {cRho : ℝ}
    (hreal : PhiHatReal T P)
    (hF : PrimeSide.LocalHypsCoreW cRho (p T P) (F T P))
    (hT : 0 < T) (hc : 0 < mass T P)
    (hbudget : coreTailBudget cRho (p T P) 3 < mass T P)
    (z z' : CoreSimpleLabel Z T 3) :
    |finiteNormalizedCoreCorrelation Z T P hconj z z' -
        fullCoreCorrelation Z T P z z'| ≤
      2 * (coreTailBudget cRho (p T P) 3 / mass T P) := by
  let q := coreTailBudget cRho (p T P) 3 / mass T P
  have hb0 : 0 ≤ coreTailBudget cRho (p T P) 3 := by
    unfold coreTailBudget
    have hh : 0 ≤ (p T P).h⁻¹ := inv_nonneg.mpr (PrimeSide.h_pos hF).le
    positivity
  have hq0 : 0 ≤ q := div_nonneg hb0 hc.le
  have hq1 : q < 1 := by
    exact (div_lt_one hc).2 hbudget
  have hwz := finiteCoreWeight_mem_budget Z T P hconj hreal hF hT hc z
  have hwz' := finiteCoreWeight_mem_budget Z T P hconj hreal hF hT hc z'
  have hk := finiteKfun_div_mass_abs_le_sqrt_weights Z T P hconj hreal hc z z'
  have hrz := rho_core_le_budget hF hT (by norm_num)
    (core_mem_bounds Z T z)
  have hrz' := rho_core_le_budget hF hT (by norm_num)
    (core_mem_bounds Z T z')
  have hout := PrimeSide.abs_Kinf_sub_Kfun_le hF
    (z : ℂ).im (z' : ℂ).im (s := (1 : ℝ)) (by norm_num)
  have hout' :
      |PrimeSide.Kinf (p T P) (F T P) (z : ℂ).im (z' : ℂ).im -
        PrimeSide.Kfun (p T P) (F T P) (z : ℂ).im (z' : ℂ).im| ≤
          coreTailBudget cRho (p T P) 3 := by
    norm_num at hout
    nlinarith
  have hfk :
      |fullCoreCorrelation Z T P z z' -
        PrimeSide.Kfun (p T P) (F T P) (z : ℂ).im (z' : ℂ).im /
          mass T P| ≤ q := by
    unfold fullCoreCorrelation q
    rw [← sub_div, abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right hout' hc.le
  unfold finiteNormalizedCoreCorrelation
  exact normalized_scalar_close_of_weights hq0 hq1
    hwz.1 hwz.2 hwz'.1 hwz'.2 hk hfk

end StrictImprovement
end Zeta23
