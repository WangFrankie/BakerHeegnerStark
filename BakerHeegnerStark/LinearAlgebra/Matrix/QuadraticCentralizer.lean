/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Quadratic CM matrices and their special-linear part

Over any commutative ring, commuting with `[[0, -m], [1, 0]]` forces a matrix
to have the CM multiplication shape `[[a, -m*b], [b, a]]`. Its determinant is
`a² + m*b²`. For an invertible matrix this norm is a unit.
The full commutant is commutative, also over rings with zero divisors.

`GeneralLinearGroup.specialLinearPart` right-normalizes a two-by-two unit
matrix by its unit inverse determinant. It scales the second column directly
and uses the inverse already supplied by the unit, not division in the base
ring. The exact factorization by `diag(1, det A)` is proved. This function is
not asserted to be a group homomorphism.

No field or nontriviality hypothesis is needed, so these statements apply to
composite-level residue rings, including rings with nilpotents. The algebra
does not assert the remaining arithmetic compatibility of CM values with
Galois actions.
-/

open scoped MatrixGroups
namespace Matrix
variable {R : Type*} [CommRing R]

/-- The full coordinate characterization of the quadratic generator's commutant. -/
theorem commute_quadratic_generator_iff (m : R) (A : Matrix (Fin 2) (Fin 2) R) :
    Commute A !![0, -m; 1, 0] ↔ A 0 1 = -m * A 1 0 ∧ A 1 1 = A 0 0 := by
  constructor
  · intro h
    change A * !![0, -m; 1, 0] = !![0, -m; 1, 0] * A at h
    constructor
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun₂ h 0 0
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun₂ h 1 0
  · rintro ⟨h01, h11⟩
    change A * !![0, -m; 1, 0] = !![0, -m; 1, 0] * A
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h11, mul_comm]

/-- Matrices commuting with the quadratic generator commute with each other. -/
theorem commute_of_commute_quadratic_generator (m : R)
    {A B : Matrix (Fin 2) (Fin 2) R}
    (hA : Commute A !![0, -m; 1, 0]) (hB : Commute B !![0, -m; 1, 0]) :
    Commute A B := by
  obtain ⟨hA01, hA11⟩ := (commute_quadratic_generator_iff m A).mp hA
  obtain ⟨hB01, hB11⟩ := (commute_quadratic_generator_iff m B).mp hB
  change A * B = B * A
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, hA01, hA11, hB01, hB11]
  all_goals ring

/-- The determinant of a commuting matrix is the quadratic norm of its first column. -/
theorem det_of_commute_quadratic_generator (m : R) (A : Matrix (Fin 2) (Fin 2) R)
    (h : Commute A !![0, -m; 1, 0]) :
    A.det = (A 0 0) ^ 2 + m * (A 1 0) ^ 2 := by
  obtain ⟨h01, h11⟩ := (commute_quadratic_generator_iff m A).mp h
  rw [Matrix.det_fin_two, h01, h11]
  ring


namespace GeneralLinearGroup

/-- Right-normalization of a two-by-two unit matrix to determinant one. -/
def specialLinearPart (A : GL (Fin 2) R) : SL(2, R) :=
  let r : R := A.det.inv
  ⟨!![A 0 0, A 0 1 * r; A 1 0, A 1 1 * r], by
    have hdet : (A 0 0 * A 1 1 - A 0 1 * A 1 0) * r = 1 := by
      simpa only [r, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] using A.det.val_inv
    simp only [Matrix.det_fin_two]
    dsimp
    calc
      _ = (A 0 0 * A 1 1 - A 0 1 * A 1 0) * r := by ring
      _ = 1 := hdet⟩

/-- The right-normalized part recovers the original matrix with its determinant diagonal. -/
theorem specialLinearPart_mul_diagonal_det (A : GL (Fin 2) R) :
    (A.specialLinearPart : Matrix (Fin 2) (Fin 2) R) * !![1, 0; 0, (A.det : R)] =
      (A : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [specialLinearPart, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals dsimp
  all_goals simp only [mul_zero, add_zero, zero_add, mul_one, mul_assoc, Units.inv_mul]

/-- A commuting unit matrix has its quadratic norm as unit determinant. -/
theorem det_val_of_commute_quadratic_generator (m : R) (A : GL (Fin 2) R)
    (h : Commute (A : Matrix (Fin 2) (Fin 2) R) !![0, -m; 1, 0]) :
    (A.det : R) = (A 0 0) ^ 2 + m * (A 1 0) ^ 2 := by
  simpa only [GeneralLinearGroup.val_det_apply] using
    Matrix.det_of_commute_quadratic_generator m (A : Matrix (Fin 2) (Fin 2) R) h

/-- The supplied inverse determinant is an inverse of the actual quadratic norm. -/
theorem norm_mul_inv_det_eq_one_of_commute (m : R) (A : GL (Fin 2) R)
    (h : Commute (A : Matrix (Fin 2) (Fin 2) R) !![0, -m; 1, 0]) :
    ((A 0 0) ^ 2 + m * (A 1 0) ^ 2) * (A.det.inv : R) = 1 := by
  rw [← det_val_of_commute_quadratic_generator m A h]
  exact A.det.val_inv

end GeneralLinearGroup

end Matrix
