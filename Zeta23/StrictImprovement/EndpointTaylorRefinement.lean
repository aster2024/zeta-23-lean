/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ExplicitDelta

/-!
# Higher exact Taylor refinement at the endpoint

Starting from the already proved fifth-order upper bound for sine, three
interval integrations give, on the nonnegative half-line,

* a sixth-order lower bound for cosine;
* a seventh-order lower bound for sine;
* an eighth-order upper bound for cosine.

At `theta(1)^2 = 1/2` these bounds are exact rational arithmetic and improve
the endpoint-root lower bound without numerical root finding.

This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open MeasureTheory Real intervalIntegral

namespace Zeta23
namespace StrictImprovement

def cosSextic (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720

def sinSeptic (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040

def cosOctic (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320

/-- Integrating the fifth-order sine upper bound gives the sixth-order
cosine lower bound. -/
lemma cosSextic_le_cos {x : ℝ} (hx : 0 ≤ x) :
    cosSextic x ≤ Real.cos x := by
  have hsin_int : IntervalIntegrable (fun u : ℝ => Real.sin u) volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hpoly_int : IntervalIntegrable sinQuintic volume 0 x :=
    Continuous.intervalIntegrable (by unfold sinQuintic; fun_prop) 0 x
  have hmono :
      (∫ u in (0 : ℝ)..x, Real.sin u)
        ≤ ∫ u in (0 : ℝ)..x, sinQuintic u := by
    refine intervalIntegral.integral_mono_on hx hsin_int hpoly_int ?_
    intro u hu
    exact sin_le_sinQuintic hu.1
  have hanti : ∀ u : ℝ,
      HasDerivAt (fun y : ℝ => y ^ 2 / 2 - y ^ 4 / 24 + y ^ 6 / 720)
        (sinQuintic u) u := by
    intro u
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * u ^ 3) u := by
      simpa using hasDerivAt_pow 4 u
    have h6 : HasDerivAt (fun y : ℝ => y ^ 6) (6 * u ^ 5) u := by
      simpa using hasDerivAt_pow 6 u
    unfold sinQuintic
    have h := ((h2.div_const 2).sub (h4.div_const 24)).add
      (h6.div_const 720)
    exact h.congr_deriv (by ring)
  have hsin_eval :
      (∫ u in (0 : ℝ)..x, Real.sin u) = 1 - Real.cos x := by
    rw [integral_sin]
    simp
  have hpoly_eval :
      (∫ u in (0 : ℝ)..x, sinQuintic u) =
        x ^ 2 / 2 - x ^ 4 / 24 + x ^ 6 / 720 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hanti u) hpoly_int]
    simp [sinQuintic]
  unfold cosSextic
  linarith

/-- Integrating the sixth-order cosine lower bound gives the seventh-order
sine lower bound. -/
lemma sinSeptic_le_sin {x : ℝ} (hx : 0 ≤ x) :
    sinSeptic x ≤ Real.sin x := by
  have hpoly_int : IntervalIntegrable cosSextic volume 0 x :=
    Continuous.intervalIntegrable (by unfold cosSextic; fun_prop) 0 x
  have hcos_int : IntervalIntegrable (fun u : ℝ => Real.cos u) volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hmono :
      (∫ u in (0 : ℝ)..x, cosSextic u)
        ≤ ∫ u in (0 : ℝ)..x, Real.cos u := by
    refine intervalIntegral.integral_mono_on hx hpoly_int hcos_int ?_
    intro u hu
    exact cosSextic_le_cos hu.1
  have hanti : ∀ u : ℝ, HasDerivAt sinSeptic (cosSextic u) u := by
    intro u
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * u ^ 2) u := by
      simpa using hasDerivAt_pow 3 u
    have h5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * u ^ 4) u := by
      simpa using hasDerivAt_pow 5 u
    have h7 : HasDerivAt (fun y : ℝ => y ^ 7) (7 * u ^ 6) u := by
      simpa using hasDerivAt_pow 7 u
    unfold sinSeptic cosSextic
    have h := (((hasDerivAt_id u).sub (h3.div_const 6)).add
      (h5.div_const 120)).sub (h7.div_const 5040)
    exact h.congr_deriv (by ring)
  have hpoly_eval :
      (∫ u in (0 : ℝ)..x, cosSextic u) = sinSeptic x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hanti u) hpoly_int]
    simp [sinSeptic]
  have hcos_eval :
      (∫ u in (0 : ℝ)..x, Real.cos u) = Real.sin x := by
    rw [integral_cos]
    simp
  linarith

/-- Integrating the seventh-order sine lower bound gives the eighth-order
cosine upper bound. -/
lemma cos_le_cosOctic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ cosOctic x := by
  have hpoly_int : IntervalIntegrable sinSeptic volume 0 x :=
    Continuous.intervalIntegrable (by unfold sinSeptic; fun_prop) 0 x
  have hsin_int : IntervalIntegrable (fun u : ℝ => Real.sin u) volume 0 x :=
    Continuous.intervalIntegrable (by fun_prop) 0 x
  have hmono :
      (∫ u in (0 : ℝ)..x, sinSeptic u)
        ≤ ∫ u in (0 : ℝ)..x, Real.sin u := by
    refine intervalIntegral.integral_mono_on hx hpoly_int hsin_int ?_
    intro u hu
    exact sinSeptic_le_sin hu.1
  have hanti : ∀ u : ℝ,
      HasDerivAt
        (fun y : ℝ => y ^ 2 / 2 - y ^ 4 / 24 + y ^ 6 / 720 - y ^ 8 / 40320)
        (sinSeptic u) u := by
    intro u
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * u ^ 3) u := by
      simpa using hasDerivAt_pow 4 u
    have h6 : HasDerivAt (fun y : ℝ => y ^ 6) (6 * u ^ 5) u := by
      simpa using hasDerivAt_pow 6 u
    have h8 : HasDerivAt (fun y : ℝ => y ^ 8) (8 * u ^ 7) u := by
      simpa using hasDerivAt_pow 8 u
    unfold sinSeptic
    have h := (((h2.div_const 2).sub (h4.div_const 24)).add
      (h6.div_const 720)).sub (h8.div_const 40320)
    exact h.congr_deriv (by ring)
  have hpoly_eval :
      (∫ u in (0 : ℝ)..x, sinSeptic u) =
        x ^ 2 / 2 - x ^ 4 / 24 + x ^ 6 / 720 - x ^ 8 / 40320 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hanti u) hpoly_int]
    simp [sinSeptic]
  have hsin_eval :
      (∫ u in (0 : ℝ)..x, Real.sin u) = 1 - Real.cos x := by
    rw [integral_sin]
    simp
  unfold cosOctic
  linarith

/-- Refined exact endpoint-root lower bound from the seventh/eighth-order
Taylor pair. -/
theorem endpointKappa_refined_lower :
    (592688 : ℝ) / 490449 ≤ endpointKappa := by
  let th : ℝ := ThmD.theta 1
  have hth0 : 0 ≤ th := ThmD.theta_nonneg (lam := (1 : ℝ)) (by norm_num)
  have hth_sq : th ^ 2 = (1 : ℝ) / 2 := by
    simpa [th] using endpointTheta_sq
  have hsqrt_th : Real.sqrt 2 * th = 1 := by
    simpa [th] using sqrtTwo_mul_endpointTheta
  have hsin := sinSeptic_le_sin hth0
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hnum_mul := mul_le_mul_of_nonneg_left hsin hsqrt0
  have hnum :
      (37043 : ℝ) / 40320 ≤ Real.sqrt 2 * Real.sin th := by
    calc
      (37043 : ℝ) / 40320 = Real.sqrt 2 * sinSeptic th := by
        unfold sinSeptic
        symm
        calc
          Real.sqrt 2 *
              (th - th ^ 3 / 6 + th ^ 5 / 120 - th ^ 7 / 5040)
              = (Real.sqrt 2 * th) *
                  (1 - th ^ 2 / 6 + th ^ 4 / 120 - th ^ 6 / 5040) := by ring
          _ = (37043 : ℝ) / 40320 := by
            rw [hsqrt_th, show th ^ 4 = (th ^ 2) ^ 2 by ring,
              show th ^ 6 = (th ^ 2) ^ 3 by ring, hth_sq]
            norm_num
      _ ≤ Real.sqrt 2 * Real.sin th := hnum_mul
  have hcos : Real.cos th ≤ cosOctic th := cos_le_cosOctic hth0
  have hoctic : cosOctic th = (163483 : ℝ) / 215040 := by
    unfold cosOctic
    rw [show th ^ 4 = (th ^ 2) ^ 2 by ring,
      show th ^ 6 = (th ^ 2) ^ 3 by ring,
      show th ^ 8 = (th ^ 2) ^ 4 by ring, hth_sq]
    norm_num
  have hcos_upper : Real.cos th ≤ (163483 : ℝ) / 215040 := by
    rwa [hoctic] at hcos
  have hcos_pos : 0 < Real.cos th :=
    ThmD.cos_theta_pos (lam := (1 : ℝ)) (by norm_num) (by norm_num)
  unfold endpointKappa
  rw [Real.tan_eq_sin_div_cos, ← mul_div_assoc]
  apply (le_div_iff₀ hcos_pos).2
  nlinarith

end StrictImprovement
end Zeta23

end
