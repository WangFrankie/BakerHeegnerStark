/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.FixedMatrices
import BakerHeegnerStark.ComplexMultiplication.SingularModuli.Basic
import BakerHeegnerStark.ModularForms.ModularPolynomial.FixedPoints
import Mathlib.Data.ZMod.Basic

/-!
# Primitive fixed matrices at levels congruent to two modulo three

For the actual shifted CM point `(3 + √-m)/2`, the quadratic norm is
`x² - 3xk + Ck²`, where `C = (m + 1)/4 + 2`. If `3 ∤ m`, then `C` is
nonzero modulo three. Taking `k = 1` and `x = 0` or `x = 1` therefore
produces a primitive fixed matrix whose determinant is congruent to two
modulo three. The same matrices have equal diagonal entries modulo three.

Only positivity, `m ≡ 3 (mod 4)`, and `3 ∤ m` are used; neither squarefreeness
nor a class-number hypothesis is needed.
-/

namespace BakerHeegnerStark

/-- The shifted CM norm represents a level greater than one and congruent to
`2` modulo `3`, already with quadratic coordinate `k = 1` and `x ∈ {0, 1}`.
For `C = (m + 1)/4 + 2`, the two choices of level are `C` and `C - 2`. -/
theorem exists_quadraticNorm_cmPointShift_mod_three {m : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) (hm3 : ¬ 3 ∣ m) :
    ∃ (N : ℕ) (x : ℤ), 1 < N ∧ N % 3 = 2 ∧ (x = 0 ∨ x = 1) ∧
      x ^ 2 - 3 * x + (((m + 1) / 4 + 2 : ℕ) : ℤ) = (N : ℤ) := by
  have hm_ne_three : m ≠ 3 := by
    rintro rfl
    exact hm3 dvd_rfl
  have hm_seven : 7 ≤ m := by omega
  have hm3' : m % 3 ≠ 0 := by
    intro h
    exact hm3 (Nat.dvd_of_mod_eq_zero h)
  have hquot : (m + 1) / 4 * 4 = m + 1 :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (by omega))
  have hquot_two : 2 ≤ (m + 1) / 4 := by omega
  have hC : ((m + 1) / 4 + 2) % 3 = 2 ∨
      ((m + 1) / 4 + 2) % 3 = 1 := by omega
  rcases hC with hC | hC
  · refine ⟨(m + 1) / 4 + 2, 0, by omega, hC, Or.inl rfl, ?_⟩
    simp
  · refine ⟨(m + 1) / 4, 1, by omega, by omega, Or.inr rfl, ?_⟩
    push_cast
    ring

/-- The actual shifted CM point has a primitive integral fixed matrix at a
nontrivial level congruent to `2` modulo `3`, with equal diagonal entries in
`ZMod 3`. The matrix is constructed from the shifted point's quadratic
relation, not from a list of discriminants or a reciprocity hypothesis. -/
theorem exists_primitive_fixedMatrix_cmPointShift_mod_three {m : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) (hm3 : ¬ 3 ∣ m) :
    ∃ (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ),
      1 < N ∧ N % 3 = 2 ∧ A.det = (N : ℤ) ∧
      (∀ d : ℕ, (∀ i j, (d : ℤ) ∣ A i j) → d = 1) ∧
      (A 0 0 : ℂ) * (cmPointShift m : ℂ) + A 0 1 =
        (cmPointShift m : ℂ) * ((A 1 0 : ℂ) * (cmPointShift m : ℂ) + A 1 1) ∧
      (A 0 0 : ZMod 3) = (A 1 1 : ZMod 3) := by
  obtain ⟨N, x, hN, hN3, _, hnorm⟩ :=
    exists_quadraticNorm_cmPointShift_mod_three hm hm4 hm3
  have hτ : (cmPointShift m : ℂ) ^ 2 + ((-3 : ℤ) : ℂ) *
      (cmPointShift m : ℂ) + ((((m + 1) / 4 + 2 : ℕ) : ℤ) : ℂ) = 0 := by
    simpa only [Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, neg_mul,
      sub_eq_add_neg] using cmPointShift_quadratic hm hm4
  refine ⟨N, quadraticFixedMatrix (-3) (((m + 1) / 4 + 2 : ℕ) : ℤ) x 1,
    hN, hN3, ?_, ?_, ?_, ?_⟩
  · calc
      (quadraticFixedMatrix (-3) (((m + 1) / 4 + 2 : ℕ) : ℤ) x 1).det =
          x ^ 2 - 3 * x + (((m + 1) / 4 + 2 : ℕ) : ℤ) := by
        rw [quadraticFixedMatrix_det]
        ring
      _ = (N : ℤ) := hnorm
  · apply (quadraticFixedMatrix_primitive_iff (-3)
      (((m + 1) / 4 + 2 : ℕ) : ℤ) x 1).mpr
    simp
  · exact quadraticFixedMatrix_fixed (cmPointShift m) (-3)
      (((m + 1) / 4 + 2 : ℕ) : ℤ) hτ x 1
  · simp [quadraticFixedMatrix, show (3 : ZMod 3) = 0 by decide]

/-- The actual diagonal modular polynomial has a self-root at some nontrivial
level congruent to two modulo three, without CM reciprocity or class number one. -/
theorem exists_level_mod_three_rootMultiplicity_cmPointShift_pos {m : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) (hm3 : ¬ 3 ∣ m) :
    ∃ N : ℕ, 1 < N ∧ N % 3 = 2 ∧
      0 < Polynomial.rootMultiplicity (ModularForm.jInvariant (cmPointShift m))
        (cyclicSublatticePolynomial N (cmPointShift m)) := by
  obtain ⟨N, A, hN, hN3, hdet, hprim, hfix, _⟩ :=
    exists_primitive_fixedMatrix_cmPointShift_mod_three hm hm4 hm3
  refine ⟨N, hN, hN3, ?_⟩
  exact (rootMultiplicity_cyclicSublatticePolynomial_pos_iff_exists_primitive_fixed_matrix
    (by omega) (cmPointShift m)).mpr ⟨A, hdet, hprim, hfix⟩

end BakerHeegnerStark
