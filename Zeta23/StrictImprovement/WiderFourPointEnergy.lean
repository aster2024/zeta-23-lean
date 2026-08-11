/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.WiderRootLocalization
import Zeta23.StrictImprovement.WiderFourPointConstant

/-!
# Exact three-correlation energy for the width-six route

The block has four zero ordinates, but its obstruction is again the energy of
the three differences `a`, `b`, and `a+b`.  Six-root localization supplies a
root index for each difference.  A finite exact separation floor and a
weighted three-coordinate Cauchy inequality then yields the exact minimum of
the 216 frozen rational budgets.

The finite case split contains no root approximation: it uses only the strict
offset order, `epsilonTwo > 11/60`, `epsilonThree > 1/8`, and `3 < pi`.
This remains a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Real Set

namespace Zeta23
namespace StrictImprovement

/-- The exact floor used for a triple of first-six root indices.  Every
additive-index row uses `11/60`; the former `(3,3,6)` exception is removed by
the upper bound `epsilonSix < 1/15`.  Nonadditive rows use the coarser floor
`1`. -/
def widerSeparationFloor (i j k : Fin 6) : ℝ :=
  if firstSixIndex i + firstSixIndex j = firstSixIndex k then
    (11 : ℝ) / 60
  else 1

lemma widerSeparationFloor_pos (i j k : Fin 6) :
    0 < widerSeparationFloor i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [widerSeparationFloor, firstSixIndex]

/-- Exact root separation.  The exhaustive split is over 216 symbolic index
triples, not over sampled root values. -/
theorem firstSixRoot_separation_floor (i j k : Fin 6) :
    widerSeparationFloor i j k ≤
      |firstSixRoot i + firstSixRoot j - firstSixRoot k| := by
  let e0 := firstSixOffset (0 : Fin 6)
  let e1 := firstSixOffset (1 : Fin 6)
  let e2 := firstSixOffset (2 : Fin 6)
  let e3 := firstSixOffset (3 : Fin 6)
  let e4 := firstSixOffset (4 : Fin 6)
  let e5 := firstSixOffset (5 : Fin 6)
  have he0 := firstSixOffset_mem (0 : Fin 6)
  have he1 := firstSixOffset_mem (1 : Fin 6)
  have he2 := firstSixOffset_mem (2 : Fin 6)
  have he3 := firstSixOffset_mem (3 : Fin 6)
  have he4 := firstSixOffset_mem (4 : Fin 6)
  have he5 := firstSixOffset_mem (5 : Fin 6)
  have h10 : e1 < e0 := by
    simpa [e0, e1, firstSixOffset, firstSixIndex] using
      (rootOffset_strictAnti (p := 1) (q := 2) (by norm_num) (by norm_num))
  have h21 : e2 < e1 := by
    simpa [e1, e2, firstSixOffset, firstSixIndex] using
      (rootOffset_strictAnti (p := 2) (q := 3) (by norm_num) (by norm_num))
  have h32 : e3 < e2 := by
    simpa [e2, e3, firstSixOffset, firstSixIndex] using
      (rootOffset_strictAnti (p := 3) (q := 4) (by norm_num) (by norm_num))
  have h43 : e4 < e3 := by
    simpa [e3, e4, firstSixOffset, firstSixIndex] using
      (rootOffset_strictAnti (p := 4) (q := 5) (by norm_num) (by norm_num))
  have h54 : e5 < e4 := by
    simpa [e4, e5, firstSixOffset, firstSixIndex] using
      (rootOffset_strictAnti (p := 5) (q := 6) (by norm_num) (by norm_num))
  have he1Lower : (11 : ℝ) / 60 < e1 := by
    simpa [e1, firstSixOffset, firstSixIndex, epsilonTwo] using
      eleven_sixtieths_lt_epsilonTwo
  have he2Lower : (1 : ℝ) / 8 < e2 := by
    simpa [e2, firstSixOffset, firstSixIndex, epsilonThree] using
      one_eighth_lt_epsilonThree
  have he5Upper : e5 < (1 : ℝ) / 15 := by
    simpa [e5, firstSixOffset, firstSixIndex] using
      epsilonSix_lt_one_fifteenth
  have hz0 : firstSixRoot (0 : Fin 6) = 2 * Real.pi + e0 := by
    calc
      firstSixRoot (0 : Fin 6) =
          2 * Real.pi * (firstSixIndex (0 : Fin 6) : ℝ) + e0 := by
            simpa [e0] using firstSixRoot_eq (0 : Fin 6)
      _ = 2 * Real.pi + e0 := by norm_num [firstSixIndex]
  have hz1 : firstSixRoot (1 : Fin 6) = 4 * Real.pi + e1 := by
    calc
      firstSixRoot (1 : Fin 6) =
          2 * Real.pi * (firstSixIndex (1 : Fin 6) : ℝ) + e1 := by
            simpa [e1] using firstSixRoot_eq (1 : Fin 6)
      _ = 4 * Real.pi + e1 := by
        norm_num [firstSixIndex] <;> ring
  have hz2 : firstSixRoot (2 : Fin 6) = 6 * Real.pi + e2 := by
    calc
      firstSixRoot (2 : Fin 6) =
          2 * Real.pi * (firstSixIndex (2 : Fin 6) : ℝ) + e2 := by
            simpa [e2] using firstSixRoot_eq (2 : Fin 6)
      _ = 6 * Real.pi + e2 := by
        norm_num [firstSixIndex] <;> ring
  have hz3 : firstSixRoot (3 : Fin 6) = 8 * Real.pi + e3 := by
    calc
      firstSixRoot (3 : Fin 6) =
          2 * Real.pi * (firstSixIndex (3 : Fin 6) : ℝ) + e3 := by
            simpa [e3] using firstSixRoot_eq (3 : Fin 6)
      _ = 8 * Real.pi + e3 := by
        norm_num [firstSixIndex] <;> ring
  have hz4 : firstSixRoot (4 : Fin 6) = 10 * Real.pi + e4 := by
    calc
      firstSixRoot (4 : Fin 6) =
          2 * Real.pi * (firstSixIndex (4 : Fin 6) : ℝ) + e4 := by
            simpa [e4] using firstSixRoot_eq (4 : Fin 6)
      _ = 10 * Real.pi + e4 := by
        norm_num [firstSixIndex] <;> ring
  have hz5 : firstSixRoot (5 : Fin 6) = 12 * Real.pi + e5 := by
    calc
      firstSixRoot (5 : Fin 6) =
          2 * Real.pi * (firstSixIndex (5 : Fin 6) : ℝ) + e5 := by
            simpa [e5] using firstSixRoot_eq (5 : Fin 6)
      _ = 12 * Real.pi + e5 := by
        norm_num [firstSixIndex] <;> ring
  dsimp [e0, e1, e2, e3, e4, e5] at
    he0 he1 he2 he3 he4 he5 he5Upper
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [widerSeparationFloor, firstSixIndex, hz0, hz1, hz2, hz3, hz4,
      hz5] <;>
    first
    | rw [abs_of_pos (by nlinarith [Real.pi_gt_three])]
      nlinarith
    | rw [abs_of_neg (by nlinarith [Real.pi_gt_three])]
      nlinarith

set_option maxHeartbeats 2000000 in
/-- The exact minimum of the complete 216-row weighted-Cauchy budget. -/
theorem widerSeparationFloor_budget_ceiling (i j k : Fin 6) :
    widerWeightedBudgetCeiling *
        (widerSlopeDenominator i ^ 2 + widerSlopeDenominator j ^ 2 +
          widerSlopeDenominator k ^ 2) ≤
      widerSeparationFloor i j k ^ 2 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [widerSeparationFloor, firstSixIndex, widerWeightedBudgetCeiling,
      widerSlopeDenominator]

/-- The endpoint-optimized local energy constant lies below every one of the
216 weighted-Cauchy budgets. -/
theorem widerSeparationFloor_budget (i j k : Fin 6) :
    widerDeltaLower *
        (widerSlopeDenominator i ^ 2 + widerSlopeDenominator j ^ 2 +
          widerSlopeDenominator k ^ 2) ≤
      widerSeparationFloor i j k ^ 2 := by
  have hsum : 0 ≤
      widerSlopeDenominator i ^ 2 + widerSlopeDenominator j ^ 2 +
        widerSlopeDenominator k ^ 2 := by positivity
  calc
    widerDeltaLower *
          (widerSlopeDenominator i ^ 2 + widerSlopeDenominator j ^ 2 +
            widerSlopeDenominator k ^ 2)
        ≤ widerWeightedBudgetCeiling *
          (widerSlopeDenominator i ^ 2 + widerSlopeDenominator j ^ 2 +
            widerSlopeDenominator k ^ 2) :=
      mul_le_mul_of_nonneg_right
        widerDeltaLower_le_weightedBudgetCeiling hsum
    _ ≤ widerSeparationFloor i j k ^ 2 :=
      widerSeparationFloor_budget_ceiling i j k

theorem firstSixRoot_weighted_separation (i j k : Fin 6) :
    widerDeltaLower *
        (widerSlopeDenominator i ^ 2 + widerSlopeDenominator j ^ 2 +
          widerSlopeDenominator k ^ 2) ≤
      (firstSixRoot i + firstSixRoot j - firstSixRoot k) ^ 2 := by
  have hfloor := firstSixRoot_separation_floor i j k
  have hpow := pow_le_pow_left₀
    (widerSeparationFloor_pos i j k).le hfloor 2
  rw [sq_abs] at hpow
  exact (widerSeparationFloor_budget i j k).trans hpow

/-- Three-coordinate weighted Cauchy--Schwarz, written in the exact form used
by the root offsets. -/
lemma weighted_three_cauchy
    {u v w di dj dk : ℝ} (hdi : 0 < di) (hdj : 0 < dj) (hdk : 0 < dk) :
    (u + v - w) ^ 2 ≤
      (di ^ 2 + dj ^ 2 + dk ^ 2) *
        (u ^ 2 / di ^ 2 + v ^ 2 / dj ^ 2 + w ^ 2 / dk ^ 2) := by
  let p := u / di
  let q := v / dj
  let r := w / dk
  have hdi0 : di ≠ 0 := ne_of_gt hdi
  have hdj0 : dj ≠ 0 := ne_of_gt hdj
  have hdk0 : dk ≠ 0 := ne_of_gt hdk
  have hdu : di * p = u := by
    dsimp [p]
    field_simp [hdi0]
  have hdv : dj * q = v := by
    dsimp [q]
    field_simp [hdj0]
  have hdw : dk * r = w := by
    dsimp [r]
    field_simp [hdk0]
  have hsos :
      0 ≤ (di * q - dj * p) ^ 2 +
        (di * r + dk * p) ^ 2 +
        (dj * r + dk * q) ^ 2 := by positivity
  have hid :
      (di ^ 2 + dj ^ 2 + dk ^ 2) * (p ^ 2 + q ^ 2 + r ^ 2) -
          (di * p + dj * q - dk * r) ^ 2 =
        (di * q - dj * p) ^ 2 +
          (di * r + dk * p) ^ 2 +
          (dj * r + dk * q) ^ 2 := by ring
  have hcauchy :
      (di * p + dj * q - dk * r) ^ 2 ≤
        (di ^ 2 + dj ^ 2 + dk ^ 2) * (p ^ 2 + q ^ 2 + r ^ 2) := by
    nlinarith [hid]
  rw [hdu, hdv, hdw] at hcauchy
  simpa [p, q, r, div_pow] using hcauchy

/-- Exact width-six endpoint energy lower bound. -/
theorem wider_endpoint_three_point_energy_lower
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 12 * Real.pi) :
    widerDeltaLower ≤
      endpointR a ^ 2 + endpointR b ^ 2 + endpointR (a + b) ^ 2 := by
  by_contra hnot
  have henergy :
      endpointR a ^ 2 + endpointR b ^ 2 + endpointR (a + b) ^ 2 <
        widerDeltaLower := lt_of_not_ge hnot
  have haSq : endpointR a ^ 2 < widerDeltaLower := by
    nlinarith [sq_nonneg (endpointR b), sq_nonneg (endpointR (a + b))]
  have hbSq : endpointR b ^ 2 < widerDeltaLower := by
    nlinarith [sq_nonneg (endpointR a), sq_nonneg (endpointR (a + b))]
  have habSq : endpointR (a + b) ^ 2 < widerDeltaLower := by
    nlinarith [sq_nonneg (endpointR a), sq_nonneg (endpointR b)]
  have haSmall : |endpointR a| < widerCorrelationThreshold := by
    have hsquare : |endpointR a| ^ 2 < widerCorrelationThreshold ^ 2 := by
      rw [sq_abs]
      exact haSq.trans wider_delta_activates_localization
    nlinarith [abs_nonneg (endpointR a), widerCorrelationThreshold_pos]
  have hbSmall : |endpointR b| < widerCorrelationThreshold := by
    have hsquare : |endpointR b| ^ 2 < widerCorrelationThreshold ^ 2 := by
      rw [sq_abs]
      exact hbSq.trans wider_delta_activates_localization
    nlinarith [abs_nonneg (endpointR b), widerCorrelationThreshold_pos]
  have habSmall : |endpointR (a + b)| < widerCorrelationThreshold := by
    have hsquare : |endpointR (a + b)| ^ 2 < widerCorrelationThreshold ^ 2 := by
      rw [sq_abs]
      exact habSq.trans wider_delta_activates_localization
    nlinarith [abs_nonneg (endpointR (a + b)), widerCorrelationThreshold_pos]
  have haMem : a ∈ Set.Icc (0 : ℝ) (12 * Real.pi) := by
    constructor <;> linarith
  have hbMem : b ∈ Set.Icc (0 : ℝ) (12 * Real.pi) := by
    constructor <;> linarith
  have habMem : a + b ∈ Set.Icc (0 : ℝ) (12 * Real.pi) :=
    ⟨add_nonneg ha hb, hab⟩
  obtain ⟨i, hi⟩ := small_endpointR_localizes_first_six haMem haSmall
  obtain ⟨j, hj⟩ := small_endpointR_localizes_first_six hbMem hbSmall
  obtain ⟨k, hk⟩ := small_endpointR_localizes_first_six habMem habSmall
  let u := a - firstSixRoot i
  let v := b - firstSixRoot j
  let w := a + b - firstSixRoot k
  let di := widerSlopeDenominator i
  let dj := widerSlopeDenominator j
  let dk := widerSlopeDenominator k
  have hdi : 0 < di := by simpa [di] using widerSlopeDenominator_pos i
  have hdj : 0 < dj := by simpa [dj] using widerSlopeDenominator_pos j
  have hdk : 0 < dk := by simpa [dk] using widerSlopeDenominator_pos k
  have hui := wider_neighborhood_R_linear i hi.le
  have hvj := wider_neighborhood_R_linear j hj.le
  have hwk := wider_neighborhood_R_linear k hk.le
  have huNonneg : 0 ≤ |u| / di := div_nonneg (abs_nonneg _) hdi.le
  have hvNonneg : 0 ≤ |v| / dj := div_nonneg (abs_nonneg _) hdj.le
  have hwNonneg : 0 ≤ |w| / dk := div_nonneg (abs_nonneg _) hdk.le
  have huSq : u ^ 2 / di ^ 2 ≤ endpointR a ^ 2 := by
    have hpow := pow_le_pow_left₀ huNonneg (by
      simpa [u, di] using hui) 2
    simpa [div_pow, sq_abs] using hpow
  have hvSq : v ^ 2 / dj ^ 2 ≤ endpointR b ^ 2 := by
    have hpow := pow_le_pow_left₀ hvNonneg (by
      simpa [v, dj] using hvj) 2
    simpa [div_pow, sq_abs] using hpow
  have hwSq : w ^ 2 / dk ^ 2 ≤ endpointR (a + b) ^ 2 := by
    have hpow := pow_le_pow_left₀ hwNonneg (by
      simpa [w, dk] using hwk) 2
    simpa [div_pow, sq_abs] using hpow
  have hlocal :
      u ^ 2 / di ^ 2 + v ^ 2 / dj ^ 2 + w ^ 2 / dk ^ 2 ≤
        endpointR a ^ 2 + endpointR b ^ 2 + endpointR (a + b) ^ 2 := by
    linarith
  have hcauchy := weighted_three_cauchy hdi hdj hdk
  have hrootId :
      (firstSixRoot i + firstSixRoot j - firstSixRoot k) ^ 2 =
        (u + v - w) ^ 2 := by
    dsimp [u, v, w]
    ring
  have hsep := firstSixRoot_weighted_separation i j k
  have hDpos : 0 < di ^ 2 + dj ^ 2 + dk ^ 2 := by positivity
  have hfinal : widerDeltaLower ≤
      endpointR a ^ 2 + endpointR b ^ 2 + endpointR (a + b) ^ 2 := by
    apply (mul_le_mul_left hDpos).mp
    calc
      widerDeltaLower * (di ^ 2 + dj ^ 2 + dk ^ 2)
          ≤ (firstSixRoot i + firstSixRoot j - firstSixRoot k) ^ 2 := by
            simpa [di, dj, dk] using hsep
      _ = (u + v - w) ^ 2 := hrootId
      _ ≤ (di ^ 2 + dj ^ 2 + dk ^ 2) *
            (u ^ 2 / di ^ 2 + v ^ 2 / dj ^ 2 + w ^ 2 / dk ^ 2) := hcauchy
      _ ≤ (di ^ 2 + dj ^ 2 + dk ^ 2) *
            (endpointR a ^ 2 + endpointR b ^ 2 + endpointR (a + b) ^ 2) :=
        mul_le_mul_of_nonneg_left hlocal hDpos.le
  linarith

end StrictImprovement
end Zeta23

end
