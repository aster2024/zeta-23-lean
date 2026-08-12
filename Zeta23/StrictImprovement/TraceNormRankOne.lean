/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Tail.RankOne

/-!
# A two-vector rank-one majorant for the Hermitian trace norm

`Tail.traceNorm_le_of_hasSum_vecMulVec` treats the project-specific symmetric
rank-one terms `u uᵀ`.  Pinching a general complex Hermitian spectral
decomposition instead produces terms `u vᵀ`, with `v` the conjugate of a
possibly truncated eigenvector.  The proof below is the same eigenbasis and
Parseval argument, with the two vectors kept separate.

This is a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23
namespace StrictImprovement

open RHLinalg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If a Hermitian matrix is a convergent sum of two-vector rank-one terms
`c • u vᵀ`, with `c ≥ 0`, then its trace norm is at most the sum of
`c (‖u‖² + ‖v‖²) / 2`. -/
theorem traceNorm_le_of_hasSum_vecMulVec_two
    {ι : Type*} {E : Matrix n n ℂ}
    (hE : E.IsHermitian) (c : ι → ℝ) (hc : ∀ ρ, 0 ≤ c ρ)
    (u v : ι → n → ℂ) {S : ℝ}
    (hS : HasSum (fun ρ => c ρ *
      ((∑ k, ‖u ρ k‖ ^ 2) + ∑ k, ‖v ρ k‖ ^ 2) / 2) S)
    (hEsum : HasSum (fun ρ => ((c ρ : ℝ) : ℂ) • vecMulVec (u ρ) (v ρ)) E) :
    Tail.traceNorm hE ≤ S := by
  set U : Matrix n n ℂ := (hE.eigenvectorUnitary : Matrix n n ℂ) with hU
  set α : n → ι → ℂ := fun i ρ => (star U *ᵥ u ρ) i with hα
  set β : n → ι → ℂ := fun i ρ => (star U *ᵥ star (v ρ)) i with hβ
  have hEkl : ∀ k l, HasSum
      (fun ρ => ((c ρ : ℝ) : ℂ) * (u ρ k * v ρ l)) (E k l) := by
    intro k l
    have h := (Pi.hasSum.mp (Pi.hasSum.mp hEsum k)) l
    simpa only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] using h
  have hlam : ∀ i, HasSum
      (fun ρ => ((c ρ : ℝ) : ℂ) * (α i ρ * star (β i ρ)))
      ((hE.eigenvalues i : ℝ) : ℂ) := by
    intro i
    have hv : (fun k => U k i) = (hE.eigenvectorBasis i).ofLp := by
      funext k
      exact hE.eigenvectorUnitary_apply k i
    have hEv : E *ᵥ (fun k => U k i) =
        ((hE.eigenvalues i : ℝ) : ℂ) • (fun k => U k i) := by
      have h := hE.mulVec_eigenvectorBasis i
      rw [← hv] at h
      rw [h]
      funext k
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    have hvv : star (fun k => U k i) ⬝ᵥ (fun k => U k i) = 1 := by
      have h1 := Matrix.UnitaryGroup.star_mul_self hE.eigenvectorUnitary
      have h := congrFun (congrFun h1 i) i
      simpa [hU, Matrix.mul_apply, Matrix.star_apply, dotProduct] using h
    have hquad : star (fun k => U k i) ⬝ᵥ (E *ᵥ fun k => U k i) =
        ((hE.eigenvalues i : ℝ) : ℂ) := by
      rw [hEv, dotProduct_smul, hvv, smul_eq_mul, mul_one]
    have hexp : star (fun k => U k i) ⬝ᵥ (E *ᵥ fun k => U k i) =
        ∑ k, star (U k i) * ∑ l, E k l * U l i := by
      simp only [dotProduct, mulVec, Pi.star_apply]
    have h2 : HasSum (fun ρ => ∑ k, star (U k i) *
        ∑ l, (((c ρ : ℝ) : ℂ) * (u ρ k * v ρ l)) * U l i)
        (∑ k, star (U k i) * ∑ l, E k l * U l i) := by
      apply hasSum_sum
      intro k _
      apply HasSum.mul_left
      apply hasSum_sum
      intro l _
      exact (hEkl k l).mul_right _
    rw [← hexp, hquad] at h2
    convert h2 using 1
    funext ρ
    simp only [hα, hβ, mulVec, dotProduct, Matrix.star_apply,
      Pi.star_apply, star_sum, star_mul', star_star]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  set F : n → ι → ℝ := fun i ρ => c ρ *
    ((‖α i ρ‖ ^ 2 + ‖β i ρ‖ ^ 2) / 2) with hF
  have hF_sum : ∀ ρ, ∑ i, F i ρ = c ρ *
      ((∑ k, ‖u ρ k‖ ^ 2) + ∑ k, ‖v ρ k‖ ^ 2) / 2 := by
    intro ρ
    simp only [hF, hα, hβ]
    rw [← mul_sum, ← sum_div, sum_add_distrib,
      sum_normSq_unitary_mulVec hE (u ρ),
      sum_normSq_unitary_mulVec hE (star (v ρ))]
    simp only [Pi.star_apply, norm_star]
    ring
  have hF_nonneg : ∀ i ρ, 0 ≤ F i ρ := fun i ρ => by
    have := hc ρ
    simp only [hF]
    positivity
  have hF_summable : ∀ i, Summable (F i) := by
    intro i
    refine Summable.of_nonneg_of_le (hF_nonneg i) (fun ρ => ?_) hS.summable
    rw [← hF_sum ρ]
    exact single_le_sum (f := fun j => F j ρ)
      (fun j _ => hF_nonneg j ρ) (mem_univ i)
  have hbound : ∀ i, |hE.eigenvalues i| ≤ ∑' ρ, F i ρ := by
    intro i
    have hterm : ∀ ρ,
        ‖((c ρ : ℝ) : ℂ) * (α i ρ * star (β i ρ))‖ ≤ F i ρ := by
      intro ρ
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
        Real.norm_of_nonneg (hc ρ)]
      simp only [hF]
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (‖α i ρ‖ - ‖β i ρ‖)]) (hc ρ)
    have h := HasSum.norm_le_of_bounded (hlam i) (hF_summable i).hasSum hterm
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  calc
    Tail.traceNorm hE = ∑ i, |hE.eigenvalues i| := rfl
    _ ≤ ∑ i, ∑' ρ, F i ρ := sum_le_sum fun i _ => hbound i
    _ = ∑' ρ, ∑ i, F i ρ :=
      (Summable.tsum_finsetSum (fun i _ => hF_summable i)).symm
    _ = ∑' ρ, c ρ *
        ((∑ k, ‖u ρ k‖ ^ 2) + ∑ k, ‖v ρ k‖ ^ 2) / 2 :=
      tsum_congr hF_sum
    _ = S := hS.tsum_eq

/-- Finite-index specialization of
`traceNorm_le_of_hasSum_vecMulVec_two`. -/
theorem traceNorm_le_sum_vecMulVec_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Matrix n n ℂ} (hE : E.IsHermitian)
    (c : ι → ℝ) (hc : ∀ ρ, 0 ≤ c ρ) (u v : ι → n → ℂ)
    (hEsum : ∑ ρ, ((c ρ : ℝ) : ℂ) • vecMulVec (u ρ) (v ρ) = E) :
    Tail.traceNorm hE ≤ ∑ ρ, c ρ *
      ((∑ k, ‖u ρ k‖ ^ 2) + ∑ k, ‖v ρ k‖ ^ 2) / 2 := by
  apply traceNorm_le_of_hasSum_vecMulVec_two hE c hc u v
  · exact hasSum_fintype _
  · rw [← hEsum]
    exact hasSum_fintype _

end StrictImprovement
end Zeta23
