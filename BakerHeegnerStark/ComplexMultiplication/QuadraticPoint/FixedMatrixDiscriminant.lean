/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

/-!
# Negative Discriminants from Integral Fixed Matrices

A primitive integer matrix fixing an upper-half-plane point is nonscalar
unless its determinant is one. Its fixed-point equation therefore supplies
an actual integral quadratic of negative discriminant. No CM correspondence
or classification of quadratic forms is used.
-/

open Matrix

namespace BakerHeegnerStark

/-- A genuine real quadratic with an upper-half-plane root has negative
integer discriminant. -/
theorem quadratic_discriminant_neg_of_upperHalfPlane_root (τ : UpperHalfPlane)
    {a b c : ℤ} (ha : a ≠ 0)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0) :
    b ^ 2 - 4 * a * c < 0 := by
  let z : ℂ := 2 * (a : ℂ) * (τ : ℂ) + b
  have hs : ((b ^ 2 - 4 * a * c : ℤ) : ℂ) = z ^ 2 := by
    have h := discrim_eq_sq_of_quadratic_eq_zero
      (a := (a : ℂ)) (b := (b : ℂ)) (c := (c : ℂ))
      (x := (τ : ℂ)) (by simpa only [pow_two] using hτ)
    simpa only [discrim, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using h
  have hzIm : z.im = 2 * (a : ℝ) * τ.im := by
    simp [z, Complex.mul_im]
  have hzIm_ne : z.im ≠ 0 := by
    rw [hzIm]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast ha)) τ.im_ne_zero
  have hzRe : z.re = 0 := by
    have hi := congrArg Complex.im hs
    simp only [Complex.intCast_im, pow_two, Complex.mul_im] at hi
    have hprod : z.re * z.im = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_right hzIm_ne
  have hr := congrArg Complex.re hs
  simp only [Complex.intCast_re, pow_two, Complex.mul_re, hzRe, zero_mul, zero_sub] at hr
  have hpos : 0 < z.im * z.im := mul_self_pos.mpr hzIm_ne
  have hneg : (((b ^ 2 - 4 * a * c : ℤ) : ℝ)) < 0 := by
    simp only [pow_two]
    rw [hr]
    linarith
  exact_mod_cast hneg

/-- A primitive fixed matrix of determinant other than one has nonzero
lower-left entry; the scalar case can only be `±1`. -/
theorem lowerLeft_ne_zero_of_primitive_fixedMatrix (τ : UpperHalfPlane)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hprim : ∀ d : ℕ, (∀ i j, (d : ℤ) ∣ A i j) → d = 1)
    (hfix : (A 0 0 : ℂ) * (τ : ℂ) + A 0 1 =
      (τ : ℂ) * ((A 1 0 : ℂ) * (τ : ℂ) + A 1 1))
    (hdet : A.det ≠ 1) : A 1 0 ≠ 0 := by
  intro hc
  have hi := congrArg Complex.im hfix
  simp only [hc, Int.cast_zero, zero_mul, zero_add, Complex.add_im,
    Complex.intCast_im, Complex.mul_im, Complex.intCast_re, mul_zero, add_zero] at hi
  have had : A 0 0 = A 1 1 := by
    exact_mod_cast mul_right_cancel₀ τ.im_ne_zero (hi.trans (mul_comm _ _))
  have hbC : (A 0 1 : ℂ) = 0 := by
    rw [hc, had] at hfix
    simp only [Int.cast_zero, zero_mul, zero_add] at hfix
    linear_combination hfix
  have hb : A 0 1 = 0 := by exact_mod_cast hbC
  have habs : (A 0 0).natAbs = 1 := by
    apply hprim (A 0 0).natAbs
    have hself : ((A 0 0).natAbs : ℤ) ∣ A 0 0 := Int.natCast_dvd.mpr dvd_rfl
    intro i j
    fin_cases i <;> fin_cases j
    · exact hself
    · change ((A 0 0).natAbs : ℤ) ∣ A 0 1
      rw [hb]
      exact dvd_zero _
    · change ((A 0 0).natAbs : ℤ) ∣ A 1 0
      rw [hc]
      exact dvd_zero _
    · change ((A 0 0).natAbs : ℤ) ∣ A 1 1
      rw [← had]
      exact hself
  have hsq : A 0 0 ^ 2 = 1 := Int.isUnit_sq (Int.isUnit_iff_natAbs_eq.mpr habs)
  apply hdet
  rw [Matrix.det_fin_two, hc, hb, ← had]
  simpa only [pow_two, zero_mul, sub_zero] using hsq

/-- The actual trace of a primitive nonscalar fixed matrix satisfies the
elliptic trace bound. -/
theorem trace_sq_lt_four_det_of_primitive_fixedMatrix (τ : UpperHalfPlane)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hprim : ∀ d : ℕ, (∀ i j, (d : ℤ) ∣ A i j) → d = 1)
    (hfix : (A 0 0 : ℂ) * (τ : ℂ) + A 0 1 =
      (τ : ℂ) * ((A 1 0 : ℂ) * (τ : ℂ) + A 1 1))
    (hdet : A.det ≠ 1) : (A 0 0 + A 1 1) ^ 2 < 4 * A.det := by
  have hc := lowerLeft_ne_zero_of_primitive_fixedMatrix τ A hprim hfix hdet
  have hquad : (A 1 0 : ℂ) * (τ : ℂ) ^ 2 +
      ((A 1 1 - A 0 0 : ℤ) : ℂ) * (τ : ℂ) + (-A 0 1 : ℤ) = 0 := by
    push_cast
    linear_combination -hfix
  have hd := quadratic_discriminant_neg_of_upperHalfPlane_root τ hc hquad
  have heq : (A 0 0 + A 1 1) ^ 2 - 4 * A.det =
      (A 1 1 - A 0 0) ^ 2 - 4 * A 1 0 * (-A 0 1) := by
    rw [Matrix.det_fin_two]
    ring
  have hneg : (A 0 0 + A 1 1) ^ 2 - 4 * A.det < 0 := by rw [heq]; exact hd
  exact sub_neg.mp hneg

/-- A nontrivial primitive fixed matrix certifies that the actual parameter
is imaginary quadratic, with a positive leading coefficient. -/
theorem exists_integer_quadratic_of_primitive_fixedMatrix (τ : UpperHalfPlane)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hprim : ∀ d : ℕ, (∀ i j, (d : ℤ) ∣ A i j) → d = 1)
    (hfix : (A 0 0 : ℂ) * (τ : ℂ) + A 0 1 =
      (τ : ℂ) * ((A 1 0 : ℂ) * (τ : ℂ) + A 1 1))
    (hdet : A.det ≠ 1) :
    ∃ a b c : ℤ, 0 < a ∧ b ^ 2 - 4 * a * c < 0 ∧
      (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0 := by
  have hc := lowerLeft_ne_zero_of_primitive_fixedMatrix τ A hprim hfix hdet
  have hquad : (A 1 0 : ℂ) * (τ : ℂ) ^ 2 +
      ((A 1 1 - A 0 0 : ℤ) : ℂ) * (τ : ℂ) + (-A 0 1 : ℤ) = 0 := by
    push_cast
    linear_combination -hfix
  have hd := quadratic_discriminant_neg_of_upperHalfPlane_root τ hc hquad
  rcases lt_or_gt_of_ne hc with hc | hc
  · refine ⟨-A 1 0, -(A 1 1 - A 0 0), A 0 1, by omega, ?_, ?_⟩
    · nlinarith [hd]
    · push_cast at hquad ⊢
      linear_combination -hquad
  · exact ⟨A 1 0, A 1 1 - A 0 0, -A 0 1, hc, hd, hquad⟩

end BakerHeegnerStark
