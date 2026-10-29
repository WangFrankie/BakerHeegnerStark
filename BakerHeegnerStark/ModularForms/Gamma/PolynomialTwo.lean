/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.Transformations
import BakerHeegnerStark.ModularForms.ModularPolynomial.LevelTwo

/-!
# The Level-Two Modular Equation for Normalized Gamma

The actual normalized gamma values satisfy
`G₂(X,Y) = X³ + Y³ - X²Y² + 495XY - 54000 = 0` at `τ` and `2τ`.
The proof uses the normalized Weber identities and the actual eta-quotient
product, rather than selecting a factor from a relation between their cubes.
Taking the three cubic-root conjugates of `G₂` recovers `Φ₂(X³,Y³)`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace ModularForm

noncomputable section

/-- The symmetric level-two modular polynomial for the normalized cube root of j. -/
def gammaModularPolynomialTwo : ℤ[X][Y] :=
  C X ^ 3 + Y ^ 3 - C X ^ 2 * Y ^ 2 + 495 * C X * Y - 54000

theorem gammaModularPolynomialTwo_eval {R : Type*} [CommRing R] (x y : R) :
    aevalAeval x y gammaModularPolynomialTwo =
      x ^ 3 + y ^ 3 - x ^ 2 * y ^ 2 + 495 * x * y - 54000 := by
  simp only [gammaModularPolynomialTwo, map_add, map_sub, map_mul, map_pow, map_ofNat,
    aevalAeval_X, aevalAeval_Y]

/-- The normalized gamma equation is symmetric in its two variables. -/
theorem gammaModularPolynomialTwo_swap :
    Bivariate.swap gammaModularPolynomialTwo = gammaModularPolynomialTwo := by
  simp only [gammaModularPolynomialTwo, map_add, map_sub, map_mul, map_pow, map_ofNat,
    Bivariate.swap_X, Bivariate.swap_Y]
  ring

theorem gammaModularPolynomialTwo_eval_comm {R : Type*} [CommRing R] (x y : R) :
    aevalAeval x y gammaModularPolynomialTwo = aevalAeval y x gammaModularPolynomialTwo := by
  rw [gammaModularPolynomialTwo_eval, gammaModularPolynomialTwo_eval]
  ring

theorem gammaModularPolynomialTwo_monic : gammaModularPolynomialTwo.Monic := by
  unfold gammaModularPolynomialTwo
  monicity!

theorem gammaModularPolynomialTwo_natDegree : gammaModularPolynomialTwo.natDegree = 3 := by
  unfold gammaModularPolynomialTwo
  compute_degree!

/-- The gamma equation has the actual Weber eighth-power parametrization. -/
theorem gammaModularPolynomialTwo_param {K : Type*} [Field K] {t : K} (ht : t ≠ 0) :
    aevalAeval ((t ^ 3 + 16) / t) ((t ^ 3 + 256) / t ^ 2)
      gammaModularPolynomialTwo = 0 := by
  rw [gammaModularPolynomialTwo_eval]
  field_simp
  ring

/-- Doubling the argument gives this actual normalized gamma value. -/
theorem gamma₂_two_mul_eq_weberF₂ (τ : UpperHalfPlane) :
    gamma₂ (UpperHalfPlane.ofComplex (2 * (τ : ℂ))) =
      (weberF₂ (τ : ℂ) ^ 24 + 256) / weberF₂ (τ : ℂ) ^ 16 := by
  have hpos : 0 < (2 * (τ : ℂ)).im := by simpa using mul_pos two_pos τ.im_pos
  have hcoe : ((UpperHalfPlane.ofComplex (2 * (τ : ℂ)) : UpperHalfPlane) : ℂ) =
      2 * (τ : ℂ) :=
    congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos hpos)
  have h8 : weberF₁ (2 * (τ : ℂ)) ^ 8 * weberF₂ (τ : ℂ) ^ 8 = 16 := by
    rw [← mul_pow, weberF₁_two_mul_mul_weberF₂ τ.im_pos]
    calc
      (Real.sqrt 2 : ℂ) ^ 8 = ((Real.sqrt 2 : ℂ) ^ 2) ^ 4 := by ring
      _ = 16 := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
        norm_num
  have hf : weberF₂ (τ : ℂ) ≠ 0 := weberF₂_ne_zero τ.im_pos
  have h1 : weberF₁ (2 * (τ : ℂ)) ^ 8 = 16 / weberF₂ (τ : ℂ) ^ 8 :=
    (eq_div_iff (pow_ne_zero _ hf)).mpr h8
  rw [gamma₂_eq_weberF₁, hcoe,
    show weberF₁ (2 * (τ : ℂ)) ^ 24 = (weberF₁ (2 * (τ : ℂ)) ^ 8) ^ 3 by ring, h1]
  field_simp
  ring

/-- The level-two equation holds for the actual normalized values, not merely
for some choice of cube roots of the two j-values. -/
theorem gammaModularPolynomialTwo_gamma₂ (τ : UpperHalfPlane) :
    aevalAeval (gamma₂ τ) (gamma₂ (UpperHalfPlane.ofComplex (2 * (τ : ℂ))))
      gammaModularPolynomialTwo = 0 := by
  rw [gamma₂_eq_weberF₂ τ, gamma₂_two_mul_eq_weberF₂]
  simpa only [← pow_mul] using
    (gammaModularPolynomialTwo_param (pow_ne_zero 8 (weberF₂_ne_zero τ.im_pos)))

/-- Halving also satisfies the normalized gamma equation. -/
theorem gammaModularPolynomialTwo_gamma₂_half (τ : UpperHalfPlane) :
    aevalAeval (gamma₂ τ) (gamma₂ (UpperHalfPlane.ofComplex ((τ : ℂ) / 2)))
      gammaModularPolynomialTwo = 0 := by
  have hpos : 0 < ((τ : ℂ) / 2).im := by simpa using half_pos τ.im_pos
  have hdouble : UpperHalfPlane.ofComplex
      (2 * (UpperHalfPlane.ofComplex ((τ : ℂ) / 2) : ℂ)) = τ := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos,
      show 2 * ((τ : ℂ) / 2) = (τ : ℂ) by ring, UpperHalfPlane.ofComplex_apply]
  have h := gammaModularPolynomialTwo_gamma₂ (UpperHalfPlane.ofComplex ((τ : ℂ) / 2))
  rw [hdouble] at h
  rw [gammaModularPolynomialTwo_eval_comm]
  exact h

/-- The cubic-root multiplier can be moved from one variable to the other. -/
theorem gammaModularPolynomialTwo_eval_mul_cubeRoot {R : Type*} [CommRing R]
    (a x y : R) (ha : a ^ 3 = 1) :
    aevalAeval (a * x) y gammaModularPolynomialTwo =
      aevalAeval x (a * y) gammaModularPolynomialTwo := by
  rw [gammaModularPolynomialTwo_eval, gammaModularPolynomialTwo_eval]
  simp only [mul_pow, ha, one_mul]
  ring

/-- The third transform requires the inverse cubic-root phase; omitting it
would confuse the normalized equation with its equation in cubes. -/
theorem gammaModularPolynomialTwo_gamma₂_half_add_one (τ : UpperHalfPlane) :
    aevalAeval (gamma₂ τ)
      ((Complex.exp (2 * Real.pi * Complex.I / 3))⁻¹ *
        gamma₂ (UpperHalfPlane.ofComplex (((τ : ℂ) + 1) / 2)))
      gammaModularPolynomialTwo = 0 := by
  have h3 : Complex.exp (2 * Real.pi * Complex.I / 3) ^ 3 = 1 := by
    rw [← Complex.exp_nat_mul,
      show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3) =
        2 * Real.pi * Complex.I by push_cast; ring, Complex.exp_two_pi_mul_I]
  have hinv : ((Complex.exp (2 * Real.pi * Complex.I / 3))⁻¹) ^ 3 = 1 := by
    rw [inv_pow, h3, inv_one]
  have h := gammaModularPolynomialTwo_gamma₂_half ((1 : ℝ) +ᵥ τ)
  simp only [gamma₂_add_one, UpperHalfPlane.coe_vadd, Complex.ofReal_one,
    add_comm (1 : ℂ)] at h
  rw [gammaModularPolynomialTwo_eval_mul_cubeRoot _ _ _ hinv] at h
  exact h

private theorem cubic_phase_norm {R : Type*} [CommRing R]
    (w A B C : R) (hw : w ^ 2 + w + 1 = 0) :
    (A + B + C) * (A + w * B + w ^ 2 * C) * (A + w ^ 2 * B + w * C) =
      A ^ 3 + B ^ 3 + C ^ 3 - 3 * A * B * C := by
  have h3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  have h4 : w ^ 4 = w := by rw [pow_succ, h3, one_mul]
  have hinner : (A + w * B + w ^ 2 * C) * (A + w ^ 2 * B + w * C) =
      A ^ 2 - A * (B + C) + B ^ 2 + C ^ 2 - B * C := by
    calc
      _ = A ^ 2 + (w + w ^ 2) * A * (B + C) +
          w ^ 3 * (B ^ 2 + C ^ 2) + (w ^ 2 + w ^ 4) * B * C := by ring
      _ = _ := by
        rw [h3, h4, one_mul]
        linear_combination (A * (B + C) + B * C) * hw
  calc
    _ = (A + B + C) * ((A + w * B + w ^ 2 * C) * (A + w ^ 2 * B + w * C)) := by ring
    _ = _ := by rw [hinner]; ring

/-- The cubic-root norm of the normalized equation is the classical equation
in cubes. This identity is valid in every commutative ring. -/
theorem gammaModularPolynomialTwo_cube_factorization {R : Type*} [CommRing R]
    (w x y : R) (hw : w ^ 2 + w + 1 = 0) :
    aevalAeval x y gammaModularPolynomialTwo *
      aevalAeval x (w * y) gammaModularPolynomialTwo *
      aevalAeval x (w ^ 2 * y) gammaModularPolynomialTwo =
        aevalAeval (x ^ 3) (y ^ 3) modularPolynomialTwo := by
  have h3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  have h4 : w ^ 4 = w := by rw [pow_succ, h3, one_mul]
  have h6 : w ^ 6 = 1 := by
    calc
      w ^ 6 = (w ^ 3) ^ 2 := by ring
      _ = 1 := by rw [h3, one_pow]
  let A := x ^ 3 + y ^ 3 - 54000
  let B := 495 * x * y
  let C := -x ^ 2 * y ^ 2
  have h0 : aevalAeval x y gammaModularPolynomialTwo = A + B + C := by
    rw [gammaModularPolynomialTwo_eval]
    dsimp only [A, B, C]
    ring
  have h1 : aevalAeval x (w * y) gammaModularPolynomialTwo = A + w * B + w ^ 2 * C := by
    rw [gammaModularPolynomialTwo_eval]
    simp only [mul_pow, h3, one_mul]
    dsimp only [A, B, C]
    ring
  have h2 : aevalAeval x (w ^ 2 * y) gammaModularPolynomialTwo = A + w ^ 2 * B + w * C := by
    rw [gammaModularPolynomialTwo_eval]
    simp only [mul_pow, ← pow_mul, h4, h6, one_mul]
    dsimp only [A, B, C]
    ring
  rw [h0, h1, h2, cubic_phase_norm w A B C hw, modularPolynomialTwo_eval]
  dsimp only [A, B, C]
  ring

end

end ModularForm
