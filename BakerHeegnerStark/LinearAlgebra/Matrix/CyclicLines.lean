/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FinCases

/-!
# Scalar kernels of actions on cyclic lines

The coordinate vectors and their sum give three cyclic lines whose common
matrix stabilizer consists of scalars. Invertibility forces that scalar to
be a unit. Applied to a relative action, this identifies two invertible
actions up to a unit scalar without any field or reduced-ring hypothesis.
In particular it applies to the actual residue rings at levels three and
eight, not just prime levels.
-/

open scoped MatrixGroups

namespace BakerHeegnerStark

/-- A two-by-two matrix preserving the two coordinate cyclic lines and their
sum line is scalar, over an arbitrary commutative ring. -/
theorem matrix_eq_scalar_of_preserves_three_lines {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R)
    (h₁ : A.mulVec ![1, 0] ∈ Submodule.span R {![1, 0]})
    (h₂ : A.mulVec ![0, 1] ∈ Submodule.span R {![0, 1]})
    (h₃ : A.mulVec ![1, 1] ∈ Submodule.span R {![1, 1]}) :
    ∃ a : R, A = a • (1 : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h₁
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h₂
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h₃
  have h₁₀ := congrFun ha 1
  have h₂₀ := congrFun hb 0
  have h₃₀ := congrFun hc 0
  have h₃₁ := congrFun hc 1
  simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    mul_zero, mul_one, add_zero, zero_add] at h₁₀ h₂₀ h₃₀ h₃₁
  have hdiag : A 1 1 = A 0 0 := by
    simp only [← h₂₀, ← h₁₀, add_zero, zero_add] at h₃₀ h₃₁
    exact h₃₁.symm.trans h₃₀
  refine ⟨A 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← h₁₀, ← h₂₀, hdiag, smul_eq_mul]

/-- For an invertible matrix, the scalar supplied by the three cyclic lines
is a genuine unit, including over composite residue rings. -/
theorem generalLinearGroup_eq_unit_scalar_of_preserves_three_lines
    {R : Type*} [CommRing R] (A : GL (Fin 2) R)
    (h₁ : (A : Matrix (Fin 2) (Fin 2) R).mulVec ![1, 0] ∈
      Submodule.span R {![1, 0]})
    (h₂ : (A : Matrix (Fin 2) (Fin 2) R).mulVec ![0, 1] ∈
      Submodule.span R {![0, 1]})
    (h₃ : (A : Matrix (Fin 2) (Fin 2) R).mulVec ![1, 1] ∈
      Submodule.span R {![1, 1]}) :
    ∃ u : Rˣ, (A : Matrix (Fin 2) (Fin 2) R) =
      (u : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨a, ha⟩ := matrix_eq_scalar_of_preserves_three_lines (R := R)
    (A : Matrix (Fin 2) (Fin 2) R) h₁ h₂ h₃
  have hi := congrArg (fun B : GL (Fin 2) R => (B : Matrix (Fin 2) (Fin 2) R))
    (mul_inv_cancel A)
  change (A : Matrix (Fin 2) (Fin 2) R) *
    ((A⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = 1 at hi
  have h00 := congrFun₂ hi 0 0
  rw [ha] at h00
  have hunit : a * (A⁻¹) 0 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
  exact ⟨⟨a, (A⁻¹) 0 0, hunit, by simpa only [mul_comm] using hunit⟩, ha⟩

/-- Two invertible actions with a three-line-preserving relative action
agree up to a unit scalar. -/
theorem generalLinearGroup_eq_unit_smul_of_inv_mul_preserves_three_lines
    {R : Type*} [CommRing R] (A B : GL (Fin 2) R)
    (h₁ : ((B⁻¹ * A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).mulVec ![1, 0] ∈
      Submodule.span R {![1, 0]})
    (h₂ : ((B⁻¹ * A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).mulVec ![0, 1] ∈
      Submodule.span R {![0, 1]})
    (h₃ : ((B⁻¹ * A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).mulVec ![1, 1] ∈
      Submodule.span R {![1, 1]}) :
    ∃ u : Rˣ, (A : Matrix (Fin 2) (Fin 2) R) =
      (u : R) • (B : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨u, hu⟩ :=
    generalLinearGroup_eq_unit_scalar_of_preserves_three_lines (B⁻¹ * A) h₁ h₂ h₃
  have hi := congrArg (fun C : GL (Fin 2) R => (C : Matrix (Fin 2) (Fin 2) R))
    (show B * (B⁻¹ * A) = A by simp only [← mul_assoc, mul_inv_cancel, one_mul])
  change (B : Matrix (Fin 2) (Fin 2) R) *
    ((B⁻¹ * A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = A at hi
  rw [hu] at hi
  refine ⟨u, hi.symm.trans ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end BakerHeegnerStark
