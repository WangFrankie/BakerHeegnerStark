/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Nat.GCD.Basic

/-!
# Common Divisors of Cyclic-Sublattice Matrix Entries

Integral special-linear changes of basis preserve the common divisors of all
matrix entries. For an upper-triangular matrix with natural entries, absence
of nontrivial natural common divisors is exactly the usual three-entry gcd
condition. These statements do not require a nonzero determinant.
-/

open Matrix
open scoped MatrixGroups

namespace BakerHeegnerStark

private theorem dvd_entries_matrix_mul_of_left
    (A B : Matrix (Fin 2) (Fin 2) ℤ) {c : ℤ} (h : ∀ i j, c ∣ A i j) :
    ∀ i j, c ∣ (A * B) i j := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (h i k) (B k j)

private theorem dvd_entries_matrix_mul_of_right
    (A B : Matrix (Fin 2) (Fin 2) ℤ) {c : ℤ} (h : ∀ i j, c ∣ B i j) :
    ∀ i j, c ∣ (A * B) i j := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k j) (A i k)

/-- Left multiplication by an integral special-linear matrix preserves every
common divisor of the matrix entries. -/
theorem dvd_entries_specialLinearGroup_mul_iff
    (A : Matrix (Fin 2) (Fin 2) ℤ) (g : SL(2, ℤ)) (c : ℤ) :
    (∀ i j, c ∣ ((g : Matrix (Fin 2) (Fin 2) ℤ) * A) i j) ↔
      (∀ i j, c ∣ A i j) := by
  constructor
  · intro h
    have hi := dvd_entries_matrix_mul_of_right
      ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      ((g : Matrix (Fin 2) (Fin 2) ℤ) * A) h
    simpa only [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] using hi
  · exact dvd_entries_matrix_mul_of_right _ _

/-- Right multiplication by an integral special-linear matrix preserves every
common divisor of the matrix entries. -/
theorem dvd_entries_mul_specialLinearGroup_iff
    (A : Matrix (Fin 2) (Fin 2) ℤ) (g : SL(2, ℤ)) (c : ℤ) :
    (∀ i j, c ∣ (A * (g : Matrix (Fin 2) (Fin 2) ℤ)) i j) ↔
      (∀ i j, c ∣ A i j) := by
  constructor
  · intro h
    have hi := dvd_entries_matrix_mul_of_left
      (A * (g : Matrix (Fin 2) (Fin 2) ℤ))
      ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) h
    simpa only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one] using hi
  · exact dvd_entries_matrix_mul_of_left _ _

/-- The three-entry gcd condition for an upper-triangular natural matrix is
exactly the assertion that every natural divisor of all its integral entries
is one. This also applies when some or all of the entries vanish. -/
theorem gcd_eq_one_iff_dvd_triangular_entries (a b d : ℕ) :
    Nat.gcd (Nat.gcd a b) d = 1 ↔
      (∀ c : ℕ,
        (∀ i j : Fin 2,
          (c : ℤ) ∣ (!![(a : ℤ), (b : ℤ); 0, (d : ℤ)] :
            Matrix (Fin 2) (Fin 2) ℤ) i j) → c = 1) := by
  have hentries (c : ℕ) :
      (∀ i j : Fin 2,
        (c : ℤ) ∣ (!![(a : ℤ), (b : ℤ); 0, (d : ℤ)] :
          Matrix (Fin 2) (Fin 2) ℤ) i j) ↔ c ∣ Nat.gcd (Nat.gcd a b) d := by
    simp [Fin.forall_fin_two, Int.natCast_dvd_natCast, Nat.dvd_gcd_iff, and_assoc]
  constructor
  · intro h c hc
    apply Nat.dvd_one.mp
    rw [← h]
    exact (hentries c).mp hc
  · intro h
    exact h _ ((hentries _).mpr dvd_rfl)

end BakerHeegnerStark
