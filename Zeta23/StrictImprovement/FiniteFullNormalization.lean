/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.StrictImprovement.TriplePackingCount
import Zeta23.ZeroSide

/-!
# Finite/full normalization bridge

This module isolates the finite-dimensional step in which finite vectors of
squared norms `w i <= 1` are replaced by unit vectors.  The replacement adds
a positive-semidefinite matrix.  Consequently the positive index of the
remaining Hermitian complement cannot increase.

The statements are independent of the zeta-zero application.  A later caller
must still prove that its finite vectors are nonzero, that their normalized
vectors have the required local Gram energy, and that their weights lie in
`[0,1]`.

This is a source draft until checked by the pinned Lean toolchain.
-/

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace StrictImprovement

open RHLinalg
open ZeroSide

variable {d s B : Type*} [Fintype d] [DecidableEq d]
variable [Fintype s] [DecidableEq s]

/-- Squared Euclidean norm of a finite complex vector. -/
def vectorWeight (v : d -> ℂ) : ℝ :=
  ∑ k, ‖v k‖ ^ 2

lemma vectorWeight_nonneg (v : d -> ℂ) : 0 ≤ vectorWeight v := by
  unfold vectorWeight
  positivity

/-- Unit normalization of a nonzero finite vector.  The definition is total;
the useful theorems below assume positive squared norm. -/
def unitize (v : d -> ℂ) : d -> ℂ :=
  fun k => v k / (Real.sqrt (vectorWeight v) : ℂ)

lemma unitize_isUnit (v : d -> ℂ) (hv : 0 < vectorWeight v) :
    ∑ k, ‖unitize v k‖ ^ 2 = 1 := by
  unfold unitize
  have hs : ∀ k,
      ‖v k / (Real.sqrt (vectorWeight v) : ℂ)‖ ^ 2 =
        ‖v k‖ ^ 2 / vectorWeight v := by
    intro k
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.mpr hv), div_pow, Real.sq_sqrt hv.le]
  simp_rw [hs]
  rw [← Finset.sum_div]
  change vectorWeight v / vectorWeight v = 1
  exact div_self hv.ne'

/-- The Hermitian rank-one projector `x x^*`. -/
def rankOneProjector (x : d -> ℂ) : Matrix d d ℂ :=
  vecMulVec x (star x)

/-- Sum of the unit projectors belonging to a finite family. -/
def projectorSum (x : s -> d -> ℂ) : Matrix d d ℂ :=
  ∑ i, rankOneProjector (x i)

/-- The real trace of one Hermitian rank-one projector is the squared
Euclidean norm of its defining vector. -/
lemma rtrace_rankOneProjector (x : d -> ℂ) :
    rtrace (rankOneProjector x) = vectorWeight x := by
  unfold rtrace rankOneProjector vectorWeight
  rw [trace_vecMulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.conj_mul', ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- A finite sum of unit projectors has real trace equal to the family
cardinality. -/
lemma rtrace_projectorSum_of_unit
    (x : s -> d -> ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1) :
    rtrace (projectorSum x) = Fintype.card s := by
  unfold projectorSum rtrace
  rw [trace_sum, map_sum]
  simp_rw [show ∀ i, RCLike.re (Matrix.trace (rankOneProjector (x i))) = 1 by
    intro i
    have h := rtrace_rankOneProjector (x i)
    simpa [rtrace, vectorWeight, hunit i] using h]
  simp

/-- The same projector sum with real weights. -/
def weightedProjectorSum (x : s -> d -> ℂ) (w : s -> ℝ) : Matrix d d ℂ :=
  ∑ i, ((w i : ℝ) : ℂ) • rankOneProjector (x i)

/-- Matrix added when weights at most one are replaced by unit weights. -/
def normalizationGap (x : s -> d -> ℂ) (w : s -> ℝ) : Matrix d d ℂ :=
  projectorSum x - weightedProjectorSum x w

/-- A positive squared norm times the projector of the unitized vector is
exactly the original rank-one projector. -/
lemma vectorWeight_smul_unitize_projector
    (v : d -> ℂ) (hv : 0 < vectorWeight v) :
    (((vectorWeight v : ℝ) : ℂ) • rankOneProjector (unitize v)) =
      rankOneProjector v := by
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, rankOneProjector,
    vecMulVec_apply, unitize, Pi.star_apply, RCLike.star_def, map_div₀,
    Complex.conj_ofReal]
  have hsq :
      ((Real.sqrt (vectorWeight v) : ℂ)) ^ 2 = (vectorWeight v : ℂ) := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hv.le]
  have hw : (vectorWeight v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [div_mul_div_comm, ← sq, hsq]
  field_simp

/-- Family form of the preceding exact projector identity. -/
lemma weightedProjectorSum_unitize
    (v : s -> d -> ℂ) (hv : ∀ i, 0 < vectorWeight (v i)) :
    weightedProjectorSum (fun i => unitize (v i))
      (fun i => vectorWeight (v i)) =
        ∑ i, rankOneProjector (v i) := by
  unfold weightedProjectorSum
  exact Finset.sum_congr rfl fun i _ =>
    vectorWeight_smul_unitize_projector (v i) (hv i)

lemma rankOneProjector_posSemidef (x : d -> ℂ) :
    (rankOneProjector x).PosSemidef := by
  exact posSemidef_vecMulVec_self_star x

lemma projectorSum_posSemidef (x : s -> d -> ℂ) :
    (projectorSum x).PosSemidef := by
  unfold projectorSum
  exact posSemidef_sum _ fun i _ => rankOneProjector_posSemidef (x i)

lemma weightedProjectorSum_posSemidef
    (x : s -> d -> ℂ) (w : s -> ℝ) (hw : ∀ i, 0 ≤ w i) :
    (weightedProjectorSum x w).PosSemidef := by
  unfold weightedProjectorSum
  refine posSemidef_sum _ fun i _ => ?_
  exact (rankOneProjector_posSemidef (x i)).smul
    (Complex.zero_le_real.mpr (hw i))

lemma normalizationGap_eq_sum (x : s -> d -> ℂ) (w : s -> ℝ) :
    normalizationGap x w =
      ∑ i, (((1 - w i : ℝ) : ℂ) • rankOneProjector (x i)) := by
  ext a b
  simp only [normalizationGap, projectorSum, weightedProjectorSum,
    Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma normalizationGap_posSemidef
    (x : s -> d -> ℂ) (w : s -> ℝ) (hw : ∀ i, w i ≤ 1) :
    (normalizationGap x w).PosSemidef := by
  rw [normalizationGap_eq_sum]
  refine posSemidef_sum _ fun i _ => ?_
  exact (rankOneProjector_posSemidef (x i)).smul
    (Complex.zero_le_real.mpr (sub_nonneg.mpr (hw i)))

/-- The projector sum is exactly the column-matrix product used by the Gram
rank--trace theorem. -/
lemma projectorSum_eq_columnMatrix_mul_conjTranspose (x : s -> d -> ℂ) :
    projectorSum x = columnMatrix x * (columnMatrix x)ᴴ := by
  ext a b
  simp only [projectorSum, rankOneProjector, Matrix.sum_apply,
    vecMulVec_apply, Pi.star_apply, RCLike.star_def, Matrix.mul_apply,
    Matrix.conjTranspose_apply, columnMatrix]

/-- Subtracting a positive-semidefinite matrix cannot increase positive
index.  No commutation hypothesis is used. -/
theorem posIndex_sub_posSemidef_le
    {A N : Matrix d d ℂ} (hA : A.IsHermitian) (hN : N.PosSemidef) :
    posIndex (hA.sub hN.isHermitian) ≤ posIndex hA := by
  have h := posIndex_add_le hA hN.isHermitian.neg
  rw [posIndex_neg_eq_zero_of_posSemidef hN, add_zero] at h
  convert h using 2
  exact sub_eq_add_neg A N

/-- Replacing a nonnegative weighted family by unit weights cannot increase
the positive index of the Hermitian complement. -/
theorem posIndex_unit_complement_le_weighted_complement
    (x : s -> d -> ℂ) (w : s -> ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    posIndex (hA.sub (projectorSum_posSemidef x).isHermitian) ≤
      posIndex (hA.sub (weightedProjectorSum_posSemidef x w hw0).isHermitian) := by
  have hgap := normalizationGap_posSemidef x w hw1
  have hweighted := weightedProjectorSum_posSemidef x w hw0
  have hEq :
      A - projectorSum x =
        (A - weightedProjectorSum x w) - normalizationGap x w := by
    unfold normalizationGap
    abel
  calc
    posIndex (hA.sub (projectorSum_posSemidef x).isHermitian) =
        posIndex ((hA.sub hweighted.isHermitian).sub hgap.isHermitian) :=
      posIndex_congr _ _ hEq
    _ ≤ posIndex (hA.sub hweighted.isHermitian) :=
      posIndex_sub_posSemidef_le (hA.sub hweighted.isHermitian) hgap

/-- The complete finite-dimensional synthesis: after the PSD normalization
step, the canonical binned triples give the explicit quadratic gain directly
for the ambient matrix `A`. -/
theorem rank_trace_two_with_normalized_binned_family
    [Nonempty s] [Fintype B] [DecidableEq B]
    (E : BinnedEnumeration s B)
    (hcover : ∑ b, E.occupancy b = Fintype.card s)
    (D : ℝ) (hbins : (Fintype.card B : ℝ) ≤ D / 4 + 1)
    (x : s -> d -> ℂ) (hunit : ∀ i, ∑ k, ‖x i k‖ ^ 2 = 1)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocal : ∀ q : PackedTriple E,
      delta ≤ tripleCorrelationEnergy x (packedTripleIndex E) q)
    (w : s -> ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    {A : Matrix d d ℂ} (hA : A.IsHermitian)
    {b : ℕ}
    (hb : posIndex
      (hA.sub (weightedProjectorSum_posSemidef x w hw0).isHermitian) ≤ b) :
    2 * rtrace (projectorSum x)
        - (Fintype.card s : ℝ)
        + 4 * rtrace (A - projectorSum x) - 4 * (b : ℝ)
        + delta / (9 * (Fintype.card s : ℝ)) *
          max 0 ((Fintype.card s : ℝ) - D / 2 - 2) ^ 2
      ≤ frobSq A := by
  have hb' :
      posIndex (hA.sub (projectorSum_posSemidef x).isHermitian) ≤ b :=
    (posIndex_unit_complement_le_weighted_complement x w hw0 hw1 hA).trans hb
  have hmain := rank_trace_two_with_binned_gram_triples
    E hcover D hbins x hunit hdelta hlocal
    (hA.sub (projectorSum_posSemidef x).isHermitian) hb'
  rw [← projectorSum_eq_columnMatrix_mul_conjTranspose x] at hmain
  have hsum : projectorSum x + (A - projectorSum x) = A := by abel
  rw [hsum] at hmain
  exact hmain

end StrictImprovement
end Zeta23
