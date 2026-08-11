/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.ExplicitDelta

/-!
# Exact positive-root parametrization for the endpoint kernel

For `n >= 1` the positive endpoint-kernel root in
`(2*pi*n, (2*n+1)*pi)` is written `2*pi*n + epsilon_n`.  The uniform rational
test at `epsilon = 2/5` lets us construct every offset inside `(0,2/5)` by the
intermediate value theorem, without a numerical root approximation or a limit
at the tangent pole.  Strict monotonicity gives uniqueness and decreasing
offsets.

This is a source draft until checked by the pinned Lean toolchain recorded in
`LEAN_FORMALIZATION_PLAN.md`.
-/

noncomputable section

open Real Set

namespace Zeta23
namespace StrictImprovement

/-- Continuous numerator of the `n`-th offset equation. -/
def offsetNumerator (n : ℕ) (e : ℝ) : ℝ :=
  (2 * Real.pi * (n : ℝ) + e) * Real.sin (e / 2)
    - endpointKappa * Real.cos (e / 2)

/-- Tangent form of the `n`-th offset equation. -/
def offsetEquation (n : ℕ) (e : ℝ) : ℝ :=
  (2 * Real.pi * (n : ℝ) + e) * Real.tan (e / 2)

lemma continuous_offsetNumerator (n : ℕ) : Continuous (offsetNumerator n) := by
  unfold offsetNumerator
  fun_prop

/-- The continuous numerator and tangent equations agree wherever the cosine
denominator is nonzero. -/
lemma offsetNumerator_eq_zero_iff
    {n : ℕ} {e : ℝ} (hcos : Real.cos (e / 2) ≠ 0) :
    offsetNumerator n e = 0 ↔ offsetEquation n e = endpointKappa := by
  unfold offsetNumerator offsetEquation
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  ring

lemma offsetNumerator_zero (n : ℕ) : offsetNumerator n 0 = -endpointKappa := by
  simp [offsetNumerator]

lemma offsetNumerator_zero_neg (n : ℕ) : offsetNumerator n 0 < 0 := by
  rw [offsetNumerator_zero]
  exact neg_neg_of_pos endpointKappa_pos

/-- Tangent is strictly increasing on the small interval needed by the root
certificate.  The proof is the exact tangent subtraction identity. -/
lemma tan_half_strictMonoOn :
    StrictMonoOn (fun e : ℝ => Real.tan (e / 2)) (Set.Icc 0 ((2 : ℝ) / 5)) := by
  intro a ha b hb hab
  have hca_pos : 0 < Real.cos (a / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_gt_three]
    · nlinarith [Real.pi_gt_three]
  have hcb_pos : 0 < Real.cos (b / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_gt_three]
    · nlinarith [Real.pi_gt_three]
  have hdiff_pos : 0 < b / 2 - a / 2 := by linarith
  have hdiff_lt_pi : b / 2 - a / 2 < Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin_pos : 0 < Real.sin (b / 2 - a / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hdiff_pos hdiff_lt_pi
  have hid :
      Real.tan (b / 2) - Real.tan (a / 2) =
        Real.sin (b / 2 - a / 2) /
          (Real.cos (b / 2) * Real.cos (a / 2)) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
      Real.sin_sub]
    field_simp [ne_of_gt hca_pos, ne_of_gt hcb_pos]
    ring
  rw [hid]
  positivity

/-- The full offset equation is strictly increasing on `[0,2/5]`. -/
lemma offsetEquation_strictMonoOn (n : ℕ) (hn : 1 ≤ n) :
    StrictMonoOn (offsetEquation n) (Set.Icc 0 ((2 : ℝ) / 5)) := by
  intro a ha b hb hab
  have htan_lt := tan_half_strictMonoOn ha hb hab
  have htan_a_nonneg : 0 ≤ Real.tan (a / 2) := by
    have h := Real.le_tan (x := a / 2) (by linarith)
      (by nlinarith [Real.pi_gt_three])
    linarith
  have hcoef :
      2 * Real.pi * (n : ℝ) + a < 2 * Real.pi * (n : ℝ) + b := by
    linarith
  have hcoef_b_pos : 0 < 2 * Real.pi * (n : ℝ) + b := by
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  unfold offsetEquation
  calc
    (2 * Real.pi * (n : ℝ) + a) * Real.tan (a / 2)
        ≤ (2 * Real.pi * (n : ℝ) + b) * Real.tan (a / 2) :=
          mul_le_mul_of_nonneg_right hcoef.le htan_a_nonneg
    _ < (2 * Real.pi * (n : ℝ) + b) * Real.tan (b / 2) :=
          mul_lt_mul_of_pos_left htan_lt hcoef_b_pos

/-- The uniform right endpoint has positive numerator for every `n >= 1`. -/
lemma offsetNumerator_two_fifths_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < offsetNumerator n ((2 : ℝ) / 5) := by
  have htan_pos : 0 < Real.tan ((1 : ℝ) / 5) := by
    nlinarith [tan_one_fifth_gt]
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcoef :
      2 * Real.pi + (2 : ℝ) / 5
        ≤ 2 * Real.pi * (n : ℝ) + 2 / 5 := by
    have hpi0 : 0 < Real.pi := Real.pi_pos
    nlinarith
  have hroot :
      endpointKappa <
        (2 * Real.pi * (n : ℝ) + 2 / 5) * Real.tan ((1 : ℝ) / 5) := by
    exact endpointKappa_lt_first_root_test.trans_le
      (mul_le_mul_of_nonneg_right hcoef htan_pos.le)
  have hcos_pos : 0 < Real.cos ((1 : ℝ) / 5) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  have hid :
      offsetNumerator n ((2 : ℝ) / 5) =
        Real.cos ((1 : ℝ) / 5) *
          ((2 * Real.pi * (n : ℝ) + 2 / 5) * Real.tan ((1 : ℝ) / 5)
            - endpointKappa) := by
    unfold offsetNumerator
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos_pos]
    ring
  rw [hid]
  positivity

/-- Existence of the unique offset root is obtained on a fixed compact
interval; no tangent-pole limit is used. -/
theorem exists_offset_root (n : ℕ) (hn : 1 ≤ n) :
    ∃ e ∈ Set.Ioo (0 : ℝ) (2 / 5), offsetNumerator n e = 0 := by
  have hleft := offsetNumerator_zero_neg n
  have hright := offsetNumerator_two_fifths_pos n hn
  have hmem :
      (0 : ℝ) ∈ Set.uIcc (offsetNumerator n 0)
        (offsetNumerator n ((2 : ℝ) / 5)) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hleft.le, hright.le⟩)
  obtain ⟨e, he, he0⟩ := intermediate_value_uIcc
    (continuous_offsetNumerator n).continuousOn hmem
  have heIcc : e ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2 / 5)] using he
  have he_pos : 0 < e := by
    rcases heIcc with ⟨he0le, heupper⟩
    exact lt_of_le_of_ne he0le fun heq => by
      subst e
      linarith
  have he_lt : e < (2 : ℝ) / 5 := by
    rcases heIcc with ⟨helower, hele⟩
    exact lt_of_le_of_ne hele fun heq => by
      subst e
      linarith
  exact ⟨e, ⟨he_pos, he_lt⟩, he0⟩

/-- Unique existence of the offset root in the uniform rational interval. -/
theorem existsUnique_offset_root (n : ℕ) (hn : 1 ≤ n) :
    ∃! e : ℝ, e ∈ Set.Ioo (0 : ℝ) (2 / 5) ∧ offsetNumerator n e = 0 := by
  obtain ⟨e, he, he0⟩ := exists_offset_root n hn
  refine ⟨e, ⟨he, he0⟩, ?_⟩
  intro y hy
  have hcos_e : Real.cos (e / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  have hcos_y : Real.cos (y / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  have heq_e := (offsetNumerator_eq_zero_iff hcos_e).mp he0
  have heq_y := (offsetNumerator_eq_zero_iff hcos_y).mp hy.2
  apply (offsetEquation_strictMonoOn n hn).injOn
    (Set.mem_Icc.mpr ⟨he.1.le, he.2.le⟩)
    (Set.mem_Icc.mpr ⟨hy.1.1.le, hy.1.2.le⟩)
  rw [heq_e, heq_y]

/-- The exact, noncomputably selected offset.  Its specification below is
proof-independent by unique existence. -/
noncomputable def rootOffset (n : ℕ) (hn : 1 ≤ n) : ℝ :=
  Classical.choose (existsUnique_offset_root n hn)

theorem rootOffset_mem (n : ℕ) (hn : 1 ≤ n) :
    rootOffset n hn ∈ Set.Ioo (0 : ℝ) (2 / 5) :=
  (Classical.choose_spec (existsUnique_offset_root n hn)).1

theorem rootOffset_numerator_zero (n : ℕ) (hn : 1 ≤ n) :
    offsetNumerator n (rootOffset n hn) = 0 :=
  (Classical.choose_spec (existsUnique_offset_root n hn)).2

theorem rootOffset_equation (n : ℕ) (hn : 1 ≤ n) :
    offsetEquation n (rootOffset n hn) = endpointKappa := by
  apply (offsetNumerator_eq_zero_iff ?_).mp (rootOffset_numerator_zero n hn)
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  have hmem := rootOffset_mem n hn
  constructor <;> nlinarith [Real.pi_gt_three]

/-- Offset roots decrease strictly with the interval index. -/
theorem rootOffset_strictAnti
    {p q : ℕ} (hp : 1 ≤ p) (hpq : p < q) :
    rootOffset q (hp.trans hpq.le) < rootOffset p hp := by
  let ep := rootOffset p hp
  let eq := rootOffset q (hp.trans hpq.le)
  have hep := rootOffset_mem p hp
  have heq := rootOffset_mem q (hp.trans hpq.le)
  have hpEq := rootOffset_equation p hp
  have hqEq := rootOffset_equation q (hp.trans hpq.le)
  have hpqreal : (p : ℝ) < q := by exact_mod_cast hpq
  have htan_ep_pos : 0 < Real.tan (ep / 2) := by
    have h := Real.le_tan (x := ep / 2) (by simpa [ep] using hep.1.le)
      (by have := hep.2; nlinarith [Real.pi_gt_three])
    have : 0 < ep := by simpa [ep] using hep.1
    nlinarith
  have hcompare : offsetEquation p ep < offsetEquation q ep := by
    unfold offsetEquation
    apply mul_lt_mul_of_pos_right _ htan_ep_pos
    nlinarith [Real.pi_pos]
  by_contra hnot
  have hle : ep ≤ eq := not_lt.mp hnot
  rcases eq_or_lt_of_le hle with heqeq | hlt
  · subst eq
    linarith
  · have hmono := offsetEquation_strictMonoOn q (hp.trans hpq.le)
        (Set.mem_Icc.mpr ⟨(by simpa [ep] using hep.1.le),
          (by simpa [ep] using hep.2.le)⟩)
        (Set.mem_Icc.mpr ⟨(by simpa [eq] using heq.1.le),
          (by simpa [eq] using heq.2.le)⟩) hlt
    dsimp [ep, eq] at hpEq hqEq hcompare hmono
    linarith

/-! ## The first three certified offsets -/

noncomputable def epsilonOne : ℝ := rootOffset 1 (by norm_num)
noncomputable def epsilonTwo : ℝ := rootOffset 2 (by norm_num)
noncomputable def epsilonThree : ℝ := rootOffset 3 (by norm_num)

theorem epsilonOne_mem : epsilonOne ∈ Set.Ioo (0 : ℝ) (2 / 5) := by
  simpa [epsilonOne] using rootOffset_mem 1 (by norm_num)

theorem epsilonTwo_mem : epsilonTwo ∈ Set.Ioo (0 : ℝ) (2 / 5) := by
  simpa [epsilonTwo] using rootOffset_mem 2 (by norm_num)

theorem epsilonThree_mem : epsilonThree ∈ Set.Ioo (0 : ℝ) (2 / 5) := by
  simpa [epsilonThree] using rootOffset_mem 3 (by norm_num)

theorem epsilonTwo_lt_epsilonOne : epsilonTwo < epsilonOne := by
  simpa [epsilonOne, epsilonTwo] using
    (rootOffset_strictAnti (p := 1) (q := 2) (by norm_num) (by norm_num))

theorem epsilonThree_lt_epsilonTwo : epsilonThree < epsilonTwo := by
  simpa [epsilonTwo, epsilonThree] using
    (rootOffset_strictAnti (p := 2) (q := 3) (by norm_num) (by norm_num))

/-- The third offset lies to the right of the exact test point `1/8`. -/
theorem one_eighth_lt_epsilonThree : (1 : ℝ) / 8 < epsilonThree := by
  have htest : offsetEquation 3 ((1 : ℝ) / 8) < endpointKappa := by
    simpa [offsetEquation] using third_root_test_lt_endpointKappa
  have hroot : offsetEquation 3 epsilonThree = endpointKappa := by
    simpa [epsilonThree] using rootOffset_equation 3 (by norm_num)
  have htest_mem : (1 : ℝ) / 8 ∈ Set.Icc (0 : ℝ) (2 / 5) := by norm_num
  have heps_mem : epsilonThree ∈ Set.Icc (0 : ℝ) (2 / 5) :=
    Set.mem_Icc.mpr ⟨epsilonThree_mem.1.le, epsilonThree_mem.2.le⟩
  by_contra hnot
  have hle : epsilonThree ≤ (1 : ℝ) / 8 := not_lt.mp hnot
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq] at hroot
    linarith
  · have hmono := offsetEquation_strictMonoOn 3 (by norm_num)
        heps_mem htest_mem hlt
    linarith

/-- Complete exact order information used by the three-root separation
argument. -/
theorem first_three_offset_chain :
    (1 : ℝ) / 8 < epsilonThree ∧
      epsilonThree < epsilonTwo ∧
      epsilonTwo < epsilonOne ∧
      epsilonOne < 2 / 5 := by
  exact ⟨one_eighth_lt_epsilonThree, epsilonThree_lt_epsilonTwo,
    epsilonTwo_lt_epsilonOne, epsilonOne_mem.2⟩

/-! ## Certified kernel roots and their additive separation -/

/-- The positive kernel root belonging to interval index `n`. -/
noncomputable def certifiedRoot (n : ℕ) (hn : 1 ≤ n) : ℝ :=
  2 * Real.pi * (n : ℝ) + rootOffset n hn

theorem certifiedRoot_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < certifiedRoot n hn := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he := (rootOffset_mem n hn).1
  unfold certifiedRoot
  nlinarith [Real.pi_pos]

theorem certifiedRoot_rootEquation (n : ℕ) (hn : 1 ≤ n) :
    endpointRootEquation (certifiedRoot n hn) = endpointKappa := by
  have harg :
      certifiedRoot n hn / 2 = rootOffset n hn / 2 + (n : ℝ) * Real.pi := by
    unfold certifiedRoot
    ring
  unfold endpointRootEquation
  rw [harg, Real.tan_add_nat_mul_pi]
  simpa [certifiedRoot, offsetEquation, mul_comm, mul_left_comm, mul_assoc] using
    rootOffset_equation n hn

theorem certifiedRoot_cos_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    Real.cos (certifiedRoot n hn / 2) ≠ 0 := by
  intro hcos
  have htan : Real.tan (certifiedRoot n hn / 2) = 0 := by
    rw [Real.tan_eq_sin_div_cos, hcos, div_zero]
  have hroot := certifiedRoot_rootEquation n hn
  unfold endpointRootEquation at hroot
  rw [htan, mul_zero] at hroot
  linarith [endpointKappa_pos]

theorem certifiedRoot_endpointG_zero (n : ℕ) (hn : 1 ≤ n) :
    endpointG (certifiedRoot n hn) = 0 := by
  apply (endpointG_eq_zero_iff_rootEquation
    (certifiedRoot_cos_ne_zero n hn)).2
  exact certifiedRoot_rootEquation n hn

theorem certifiedRoot_sq_ne_two (n : ℕ) (hn : 1 ≤ n) :
    certifiedRoot n hn ^ 2 ≠ 2 := by
  have hz := certifiedRoot_pos n hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he := (rootOffset_mem n hn).1
  have hzlarge : 6 < certifiedRoot n hn := by
    unfold certifiedRoot
    nlinarith [Real.pi_gt_three]
  intro hsq
  nlinarith

theorem certifiedRoot_endpointK_zero (n : ℕ) (hn : 1 ≤ n) :
    endpointK (certifiedRoot n hn) = 0 := by
  apply (endpointK_eq_zero_iff_endpointG_eq_zero
    (certifiedRoot_sq_ne_two n hn)).2
  exact certifiedRoot_endpointG_zero n hn

noncomputable def zOne : ℝ := certifiedRoot 1 (by norm_num)
noncomputable def zTwo : ℝ := certifiedRoot 2 (by norm_num)
noncomputable def zThree : ℝ := certifiedRoot 3 (by norm_num)

theorem endpointK_zOne : endpointK zOne = 0 := by
  simpa [zOne] using certifiedRoot_endpointK_zero 1 (by norm_num)

theorem endpointK_zTwo : endpointK zTwo = 0 := by
  simpa [zTwo] using certifiedRoot_endpointK_zero 2 (by norm_num)

theorem endpointK_zThree : endpointK zThree = 0 := by
  simpa [zThree] using certifiedRoot_endpointK_zero 3 (by norm_num)

/-- The first three certified roots, indexed by `Fin 3`. -/
noncomputable def firstThreeRoot : Fin 3 → ℝ := ![zOne, zTwo, zThree]

/-- Signed form of the `1/8` additive separation.  It is more convenient for
the later triangle-inequality argument than an opaque numerical root bound. -/
theorem firstThreeRoot_signed_additive_separation (i j k : Fin 3) :
    firstThreeRoot i + firstThreeRoot j - firstThreeRoot k < -(1 : ℝ) / 8 ∨
      (1 : ℝ) / 8 < firstThreeRoot i + firstThreeRoot j - firstThreeRoot k := by
  have h3 : (1 : ℝ) / 8 < epsilonThree := one_eighth_lt_epsilonThree
  have h32 : epsilonThree < epsilonTwo := epsilonThree_lt_epsilonTwo
  have h21 : epsilonTwo < epsilonOne := epsilonTwo_lt_epsilonOne
  have h1u : epsilonOne < (2 : ℝ) / 5 := epsilonOne_mem.2
  have h2p : 0 < epsilonTwo := epsilonTwo_mem.1
  have h3p : 0 < epsilonThree := epsilonThree_mem.1
  have hz1 : zOne = 2 * Real.pi + epsilonOne := by
    unfold zOne certifiedRoot epsilonOne
    ring
  have hz2 : zTwo = 4 * Real.pi + epsilonTwo := by
    unfold zTwo certifiedRoot epsilonTwo
    ring
  have hz3 : zThree = 6 * Real.pi + epsilonThree := by
    unfold zThree certifiedRoot epsilonThree
    ring
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [firstThreeRoot, hz1, hz2, hz3] <;>
    first
    | left; nlinarith [Real.pi_gt_three]
    | right; nlinarith [Real.pi_gt_three]

/-- Absolute-value form of the same additive separation. -/
theorem firstThreeRoot_additive_separation (i j k : Fin 3) :
    (1 : ℝ) / 8 <
      |firstThreeRoot i + firstThreeRoot j - firstThreeRoot k| := by
  rcases firstThreeRoot_signed_additive_separation i j k with hneg | hpos
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    exact hpos

end StrictImprovement
end Zeta23
