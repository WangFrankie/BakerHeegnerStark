/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.PeriodLattice.Homothety
import Mathlib.Tactic.IntervalCases

/-!
# Distinct Period Lattices in the Inert Family

The three transformed period lattices in the nonexceptional inert family are
pairwise nonhomothetic. The proof uses integral changes of basis and elementary
positive-definite norm equations. It does not use injectivity of `j` or an
ideal-class counting theorem.
-/

open scoped Pointwise

namespace BakerHeegnerStark

private theorem norm_sixteen_im_eq_zero (p : ℕ) (hp8 : p % 8 = 3) (hp3 : 3 < p)
    (A b : ℤ) (hnorm : A ^ 2 + (p : ℤ) * b ^ 2 = 16) : b = 0 := by
  have hp11 : (11 : ℤ) ≤ p := by omega
  have hb4 : b ^ 2 < 4 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) (Nat.cast_nonneg p : (0 : ℤ) ≤ p)
    nlinarith [sq_nonneg A]
  have hbmin : -1 ≤ b := by
    by_contra h
    have : b ≤ -2 := by omega
    nlinarith [sq_nonneg (b + 2)]
  have hbmax : b ≤ 1 := by
    by_contra h
    have : 2 ≤ b := by omega
    nlinarith [sq_nonneg (b - 2)]
  interval_cases b <;> norm_num at hnorm ⊢
  all_goals
    have hple : p ≤ 16 := by have := sq_nonneg A; omega
    have hpeq : p = 11 := by omega
    subst p
    norm_num at hnorm
    have hAmin : -2 ≤ A := by
      by_contra h
      have : A ≤ -3 := by omega
      nlinarith [sq_nonneg (A + 3)]
    have hAmax : A ≤ 2 := by
      by_contra h
      have : 3 ≤ A := by omega
      nlinarith [sq_nonneg (A - 3)]
    interval_cases A <;> norm_num at hnorm

/-- For `p > 4`, the square-root lattice cannot be homothetic to any of its
quarter-period lattices with an integral real shift. -/
theorem sqrt_periodModule_not_homothetic_quarter (p : ℕ) (hp : 4 < p) (k : ℤ) :
    let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
    ¬ ∃ α : ℂ, α • periodModule s = periodModule (((k : ℂ) + s) / 4) := by
  dsimp only
  let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
  have hspos : 0 < s.im := by
    simpa [s] using Real.sqrt_pos.mpr (show (0 : ℝ) < p by exact_mod_cast (by omega : 0 < p))
  have hs : s ^ 2 = -(p : ℂ) := by
    dsimp [s]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    push_cast
    ring
  have hquarter : 0 < (((k : ℂ) + s) / 4).im := by
    simpa using div_pos hspos (by norm_num : (0 : ℝ) < 4)
  rintro ⟨α, heq⟩
  obtain ⟨a, b, c, d, hd, ha, hc⟩ :=
    (smul_periodModule_eq_iff_of_im_pos s _ α hspos hquarter).mp heq
  have hco : -(p : ℤ) * b = 4 * c + k * d ∧ 4 * a + k * b = d :=
    periodModule_coordinates_eq s (ne_of_gt hspos)
      (a := -(p : ℤ) * b) (b := 4 * a + k * b) (c := 4 * c + k * d) (d := d) (by
        push_cast
        linear_combination -(4 * s) * ha + 4 * hc - (b : ℂ) * hs)
  have hnorm : (4 * a + k * b) ^ 2 + (p : ℤ) * b ^ 2 = 4 := by
    linear_combination 4 * hd - b * hco.1 + (4 * a + k * b) * hco.2
  have hb : b = 0 := by
    by_contra hb
    have hb1 : 1 ≤ b ^ 2 := by have := sq_pos_of_ne_zero hb; omega
    have hm := mul_le_mul_of_nonneg_left hb1 (Nat.cast_nonneg p : (0 : ℤ) ≤ p)
    nlinarith [sq_nonneg (4 * a + k * b)]
  subst b
  have : (4 : ℤ) * a ^ 2 = 1 := by nlinarith [hnorm]
  omega

/-- The two quarter-period lattices in the nonexceptional inert family are
not homothetic. The residue condition handles the boundary prime `11` as well. -/
theorem inert_quarter_periodModules_not_homothetic (p : ℕ) (hp8 : p % 8 = 3)
    (hp3 : 3 < p) :
    let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
    ¬ ∃ α : ℂ, α • periodModule ((1 + s) / 4) = periodModule ((3 + s) / 4) := by
  dsimp only
  let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
  have hspos : 0 < s.im := by
    simpa [s] using Real.sqrt_pos.mpr (show (0 : ℝ) < p by exact_mod_cast (by omega : 0 < p))
  have hs : s ^ 2 = -(p : ℂ) := by
    dsimp [s]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    push_cast
    ring
  have hτ : 0 < ((1 + s) / 4).im := by
    simpa using div_pos hspos (by norm_num : (0 : ℝ) < 4)
  have hσ : 0 < ((3 + s) / 4).im := by
    simpa using div_pos hspos (by norm_num : (0 : ℝ) < 4)
  rintro ⟨α, heq⟩
  obtain ⟨a, b, c, d, hd, ha, hc⟩ :=
    (smul_periodModule_eq_iff_of_im_pos _ _ α hτ hσ).mp heq
  have hco : 4 * a + 3 * b - (p : ℤ) * b = 16 * c + 12 * d ∧
      4 * a + 4 * b = 4 * d :=
    periodModule_coordinates_eq s (ne_of_gt hspos)
      (a := 4 * a + 3 * b - (p : ℤ) * b) (b := 4 * a + 4 * b)
      (c := 16 * c + 12 * d) (d := 4 * d) (by
        push_cast
        linear_combination 16 * hc - 4 * (1 + s) * ha - (b : ℂ) * hs)
  have hnorm : (4 * a + 3 * b) ^ 2 + (p : ℤ) * b ^ 2 = 16 := by
    linear_combination 16 * hd - b * hco.1 + (4 * a + 3 * b) * hco.2
  have hb := norm_sixteen_im_eq_zero p hp8 hp3 _ _ hnorm
  subst b
  have hda : d = a := by omega
  subst d
  have ha2 : a ^ 2 = 1 := by nlinarith [hd]
  have hac : a = -2 * c := by omega
  rw [hac] at ha2
  have : (4 : ℤ) * c ^ 2 = 1 := by nlinarith [ha2]
  omega

end BakerHeegnerStark
