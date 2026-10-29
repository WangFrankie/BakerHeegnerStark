/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Tactic.Linarith

/-!
# Unique Fixed-Determinant Representatives

For positive determinant, the upper-triangular representatives in
`FixedDetMatrices.reps` meet every left `SL(2, ℤ)`-orbit exactly once.
Moreover, an element carrying one representative to another is the identity.
The existence proof uses mathlib's fixed-determinant induction principle.
-/

open Matrix
open scoped MatrixGroups

namespace BakerHeegnerStark

/-- A positive-determinant representative has positive lower-right entry. -/
theorem fixedDetMatrix_reps_lowerRight_pos {m : ℤ} (hm : 0 < m)
    {A : FixedDetMatrix (Fin 2) ℤ m} (hA : A ∈ FixedDetMatrices.reps m) :
    0 < A.1 1 1 := by
  have hdet : A.1 0 0 * A.1 1 1 = m := by
    simpa only [Matrix.det_fin_two, hA.1, mul_zero, sub_zero] using A.2
  exact pos_of_mul_pos_right (hdet.symm ▸ hm) hA.2.1.le

/-- Distinct positive-determinant representatives are not related by the left
`SL(2, ℤ)`-action, and the stabilizer of each representative is trivial. -/
theorem fixedDetMatrix_reps_smul_eq {m : ℤ} (hm : 0 < m)
    {A B : FixedDetMatrix (Fin 2) ℤ m}
    (hA : A ∈ FixedDetMatrices.reps m) (hB : B ∈ FixedDetMatrices.reps m)
    {g : SL(2, ℤ)} (h : g • A = B) : g = 1 ∧ A = B := by
  have ha11 := fixedDetMatrix_reps_lowerRight_pos hm hA
  have hb11 := fixedDetMatrix_reps_lowerRight_pos hm hB
  obtain ⟨ha10, ha00, ha01, ha01abs⟩ := hA
  obtain ⟨hb10, hb00, hb01, hb01abs⟩ := hB
  have ha01lt : A.1 0 1 < A.1 1 1 := by
    simpa only [abs_of_nonneg ha01, abs_of_pos ha11] using ha01abs
  have hb01lt : B.1 0 1 < B.1 1 1 := by
    simpa only [abs_of_nonneg hb01, abs_of_pos hb11] using hb01abs
  have hmat := congrArg Subtype.val h
  rw [FixedDetMatrices.smul_coe] at hmat
  have h10 := congrFun₂ hmat 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ha10, hb10, mul_zero, add_zero] at h10
  have hg10 : g 1 0 = 0 := (mul_eq_zero.mp h10).resolve_right ha00.ne'
  have h00 := congrFun₂ hmat 0 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ha10, mul_zero, add_zero] at h00
  have hg00pos : 0 < g 0 0 := pos_of_mul_pos_left (h00.symm ▸ hb00) ha00.le
  have hgdet : g 0 0 * g 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hg10, mul_zero, sub_zero] using g.2
  have hgdiag : g 0 0 = 1 ∧ g 1 1 = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hgdet with hpos | hneg
    · exact hpos
    · omega
  have h11 := congrFun₂ hmat 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hg10, hgdiag.2,
    zero_mul, one_mul, zero_add] at h11
  have h01 := congrFun₂ hmat 0 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hgdiag.1, one_mul] at h01
  have hg01 : g 0 1 = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hg_le : g 0 1 ≤ -1 := by omega
      nlinarith
    · have hg_ge : 1 ≤ g 0 1 := by omega
      nlinarith
  have hg : g = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change g i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j
    fin_cases i <;> fin_cases j <;> simp [hgdiag.1, hg01, hg10, hgdiag.2]
  exact ⟨hg, by simpa only [hg, one_smul] using h⟩

/-- Every positive-determinant matrix can be carried to a representative by
left multiplication with an integral special-linear matrix. -/
theorem exists_smul_mem_fixedDetMatrix_reps {m : ℤ} (hm : 0 < m)
    (A : FixedDetMatrix (Fin 2) ℤ m) :
    ∃ g : SL(2, ℤ), g • A ∈ FixedDetMatrices.reps m := by
  refine FixedDetMatrices.induction_on
    (C := fun B => ∃ g : SL(2, ℤ), g • B ∈ FixedDetMatrices.reps m)
    (A := A) (ne_of_gt hm) ?_ ?_ ?_
  · intro B h10 h00 h01 hbound
    refine ⟨1, ?_⟩
    simpa only [one_smul] using
      (show B ∈ FixedDetMatrices.reps m from ⟨h10, h00, h01, hbound⟩)
  · intro B hB
    obtain ⟨g, hg⟩ := hB
    exact ⟨g * ModularGroup.S⁻¹, by simpa only [mul_smul, inv_smul_smul] using hg⟩
  · intro B hB
    obtain ⟨g, hg⟩ := hB
    exact ⟨g * ModularGroup.T⁻¹, by simpa only [mul_smul, inv_smul_smul] using hg⟩

/-- Each left `SL(2, ℤ)`-orbit of positive-determinant integral matrices has a
unique upper-triangular representative in `FixedDetMatrices.reps`. -/
theorem existsUnique_fixedDetMatrix_rep {m : ℤ} (hm : 0 < m)
    (A : FixedDetMatrix (Fin 2) ℤ m) :
    ∃! B : FixedDetMatrix (Fin 2) ℤ m,
      B ∈ FixedDetMatrices.reps m ∧ ∃ g : SL(2, ℤ), g • A = B := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fixedDetMatrix_reps hm A
  refine ⟨g • A, ⟨hg, g, rfl⟩, ?_⟩
  rintro B ⟨hB, k, hk⟩
  have h : (k * g⁻¹) • (g • A) = B := by
    simpa only [mul_smul, inv_smul_smul] using hk
  exact (fixedDetMatrix_reps_smul_eq hm hg hB h).2.symm

end BakerHeegnerStark
