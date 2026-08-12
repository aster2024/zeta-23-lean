/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.RootLocalization

/-!
# Uniform stability of the three-point kernel energy

A uniform `epsilon` perturbation of two correlation kernels bounded by one
can lower each squared correlation by at most `2*epsilon`.  Hence the endpoint
constant `4/3087049` transfers to a nearby normalized kernel with the explicit
loss `6*epsilon`.

This is the exact finite interface needed for the fixed-`lambda` and
finite/full-grid transfers.  It contains no floating-point estimate and is a
source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Real Set

namespace Zeta23
namespace StrictImprovement

/-- Local three-point squared correlation energy. -/
def threePointEnergy (R : ℝ → ℝ) (a b : ℝ) : ℝ :=
  R a ^ 2 + R b ^ 2 + R (a + b) ^ 2

/-- A uniformly close bounded real correlation loses at most `2*epsilon`
after squaring. -/
lemma sq_sub_two_eps_le_sq_of_close
    {x y eps : ℝ} (heps : 0 ≤ eps)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hclose : |y - x| ≤ eps) :
    x ^ 2 - 2 * eps ≤ y ^ 2 := by
  have hsum : |y + x| ≤ 2 := by
    calc
      |y + x| ≤ |y| + |x| := abs_add_le y x
      _ ≤ 2 := by linarith
  have hprod : |y - x| * |y + x| ≤ eps * 2 :=
    mul_le_mul hclose hsum (abs_nonneg (y + x)) heps
  have habsdiff : |y ^ 2 - x ^ 2| ≤ 2 * eps := by
    rw [show y ^ 2 - x ^ 2 = (y - x) * (y + x) by ring, abs_mul]
    nlinarith
  nlinarith [neg_abs_le (y ^ 2 - x ^ 2)]

/-- Uniform perturbation bound for a full three-point energy. -/
theorem threePointEnergy_stable
    {R S : ℝ → ℝ} {eps delta a b : ℝ}
    (heps : 0 ≤ eps) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 8 * Real.pi)
    (hR : ∀ x ∈ Set.Icc (0 : ℝ) (8 * Real.pi), |R x| ≤ 1)
    (hS : ∀ x ∈ Set.Icc (0 : ℝ) (8 * Real.pi), |S x| ≤ 1)
    (hclose : ∀ x ∈ Set.Icc (0 : ℝ) (8 * Real.pi),
      |S x - R x| ≤ eps)
    (hdelta : delta ≤ threePointEnergy R a b) :
    delta - 6 * eps ≤ threePointEnergy S a b := by
  have ha_mem : a ∈ Set.Icc (0 : ℝ) (8 * Real.pi) := ⟨ha, by linarith⟩
  have hb_mem : b ∈ Set.Icc (0 : ℝ) (8 * Real.pi) := ⟨hb, by linarith⟩
  have hab_mem : a + b ∈ Set.Icc (0 : ℝ) (8 * Real.pi) :=
    ⟨add_nonneg ha hb, hab⟩
  have hsa := sq_sub_two_eps_le_sq_of_close heps
    (hR a ha_mem) (hS a ha_mem) (hclose a ha_mem)
  have hsb := sq_sub_two_eps_le_sq_of_close heps
    (hR b hb_mem) (hS b hb_mem) (hclose b hb_mem)
  have hsab := sq_sub_two_eps_le_sq_of_close heps
    (hR (a + b) hab_mem) (hS (a + b) hab_mem) (hclose (a + b) hab_mem)
  unfold threePointEnergy at hdelta ⊢
  linarith

/-- Endpoint specialization: any bounded normalized kernel uniformly within
`epsilon` of `endpointR` inherits the exact endpoint constant with loss
`6*epsilon`. -/
theorem endpoint_threePointEnergy_stable
    {S : ℝ → ℝ} {eps a b : ℝ}
    (heps : 0 ≤ eps) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 8 * Real.pi)
    (hS : ∀ x ∈ Set.Icc (0 : ℝ) (8 * Real.pi), |S x| ≤ 1)
    (hclose : ∀ x ∈ Set.Icc (0 : ℝ) (8 * Real.pi),
      |S x - endpointR x| ≤ eps) :
    explicitDeltaLower - 6 * eps ≤ threePointEnergy S a b := by
  apply threePointEnergy_stable heps ha hb hab
    (fun x _ => endpointR_abs_le_one x) hS hclose
  simpa [threePointEnergy] using endpoint_three_point_energy_lower ha hb hab

/-- A convenient backward-compatible rational corollary: uniform error at
most `1/(12*772641)` still preserves the historical half-constant. -/
theorem endpoint_threePointEnergy_half
    {S : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 8 * Real.pi)
    (hS : ∀ x ∈ Set.Icc (0 : ℝ) (8 * Real.pi), |S x| ≤ 1)
    (hclose : ∀ x ∈ Set.Icc (0 : ℝ) (8 * Real.pi),
      |S x - endpointR x| ≤ (1 : ℝ) / (12 * 772641)) :
    (1 : ℝ) / (2 * 772641) ≤ threePointEnergy S a b := by
  have h := endpoint_threePointEnergy_stable
    (eps := (1 : ℝ) / (12 * 772641)) (by norm_num)
    ha hb hab hS hclose
  norm_num [explicitDeltaLower] at h ⊢
  nlinarith

end StrictImprovement
end Zeta23
