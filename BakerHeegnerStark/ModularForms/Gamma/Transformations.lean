/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.Basic

/-!
# Transformations of Normalized Gamma

The normalized Weber identities determine the actual multipliers of `gamma₂`,
not just their cubes. Translation by one has the inverse cubic-root multiplier,
inversion fixes `gamma₂`, and translation by three is a genuine period.
-/

open Complex
open scoped Real

namespace ModularForm

/-- Translation by one multiplies normalized gamma by `exp(2πi/3)⁻¹`. -/
theorem gamma₂_add_one (τ : UpperHalfPlane) :
    gamma₂ ((1 : ℝ) +ᵥ τ) = (Complex.exp (2 * Real.pi * Complex.I / 3))⁻¹ * gamma₂ τ := by
  have h24 : Complex.exp (2 * π * I / 24) ^ 24 = 1 := by
    rw [← Complex.exp_nat_mul,
      show ((24 : ℕ) : ℂ) * (2 * π * I / 24) = 2 * π * I by push_cast; ring,
      Complex.exp_two_pi_mul_I]
  have h8 : Complex.exp (2 * π * I / 24) ^ 8 = Complex.exp (2 * π * I / 3) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [gamma₂_eq_weberF₂, gamma₂_eq_weberF₂]
  simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_one]
  rw [add_comm (1 : ℂ), weberF₂_add_one]
  change ((Complex.exp (2 * π * I / 24) * weberF₂ (τ : ℂ)) ^ 24 + 16) /
      (Complex.exp (2 * π * I / 24) * weberF₂ (τ : ℂ)) ^ 8 =
    (Complex.exp (2 * π * I / 3))⁻¹ *
      ((weberF₂ (τ : ℂ) ^ 24 + 16) / weberF₂ (τ : ℂ) ^ 8)
  rw [mul_pow, mul_pow, h24, h8, one_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Modular inversion fixes normalized gamma, with no cube-root ambiguity. -/
theorem gamma₂_smul_S (τ : UpperHalfPlane) :
    gamma₂ (ModularGroup.S • τ) = gamma₂ τ := by
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ)
    simp only [inv_neg, neg_div, one_div]
  rw [gamma₂_eq_weberF₂, gamma₂_eq_weberF₁, hS, weberF₂_neg_inv τ.im_pos]

/-- Translation by three is a genuine period of normalized gamma. -/
theorem gamma₂_add_three (τ : UpperHalfPlane) :
    gamma₂ ((3 : ℝ) +ᵥ τ) = gamma₂ τ := by
  have h3 : Complex.exp (2 * π * I / 3) ^ 3 = 1 := by
    rw [← Complex.exp_nat_mul,
      show ((3 : ℕ) : ℂ) * (2 * π * I / 3) = 2 * π * I by push_cast; ring,
      Complex.exp_two_pi_mul_I]
  have hτ : (3 : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ)) := by
    rw [← add_vadd, ← add_vadd]
    norm_num
  calc
    gamma₂ ((3 : ℝ) +ᵥ τ) =
        (Complex.exp (2 * π * I / 3))⁻¹ ^ 3 * gamma₂ τ := by
      rw [hτ, gamma₂_add_one, gamma₂_add_one, gamma₂_add_one]
      ring
    _ = gamma₂ τ := by rw [inv_pow, h3, inv_one, one_mul]

end ModularForm
