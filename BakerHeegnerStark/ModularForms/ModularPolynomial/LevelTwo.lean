/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic.ComputeDegree
import BakerHeegnerStark.ModularForms.Weber.Polynomial

/-!
# The Classical Modular Polynomial of Level Two

Extracted from `QNFMathlib/NumberTheory/ModularForms/ModularPolynomialTwo.lean` in
QuadraticNumberFields at commit
`196dd48b3439cc731397fd2cf9b8ac48da211a22`. The original proof and authorship
are preserved.

Material destined for mathlib.

We define `Φ₂ ∈ ℤ[X,Y]` and prove `Φ₂(j(τ), j(2τ)) = 0`. The proof eliminates
`t = 𝔣₂(τ)²⁴` from `j(τ) = (t + 16)³/t` and `j(2τ) = (t + 256)³/t²`.
The elimination is a polynomial identity verified by the Lean kernel.

## References

* Andrew V. Sutherland, [Classical modular polynomials]
  (https://math.mit.edu/~drew/ClassicalModPolys.html).
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace ModularForm

noncomputable section

/-- The classical symmetric modular polynomial `Φ₂`, with integer coefficients. -/
def modularPolynomialTwo : ℤ[X][Y] :=
  C X ^ 3 + Y ^ 3 - C X ^ 2 * Y ^ 2 + 1488 * C X * Y * (C X + Y) -
    162000 * (C X ^ 2 + Y ^ 2) + 40773375 * C X * Y +
    8748000000 * (C X + Y) - 157464000000000

theorem modularPolynomialTwo_eval {R : Type*} [CommRing R] (x y : R) :
    aevalAeval x y modularPolynomialTwo =
      x ^ 3 + y ^ 3 - x ^ 2 * y ^ 2 + 1488 * x * y * (x + y) -
        162000 * (x ^ 2 + y ^ 2) + 40773375 * x * y +
        8748000000 * (x + y) - 157464000000000 := by
  simp only [modularPolynomialTwo, map_add, map_sub, map_mul, map_pow, map_ofNat,
    aevalAeval_X, aevalAeval_Y]

/-- Symmetry of `Φ₂` under interchange of its variables. -/
theorem modularPolynomialTwo_swap : Bivariate.swap modularPolynomialTwo = modularPolynomialTwo := by
  simp only [modularPolynomialTwo, map_add, map_sub, map_mul, map_pow, map_ofNat,
    Bivariate.swap_X, Bivariate.swap_Y]
  ring

theorem modularPolynomialTwo_eval_comm {R : Type*} [CommRing R] (x y : R) :
    aevalAeval x y modularPolynomialTwo = aevalAeval y x modularPolynomialTwo := by
  rw [modularPolynomialTwo_eval, modularPolynomialTwo_eval]
  ring

theorem modularPolynomialTwo_monic : modularPolynomialTwo.Monic := by
  unfold modularPolynomialTwo
  monicity!

theorem modularPolynomialTwo_natDegree : modularPolynomialTwo.natDegree = 3 := by
  unfold modularPolynomialTwo
  compute_degree!

/-- The rational parametrization of `Φ₂ = 0`, valid over any field. -/
theorem modularPolynomialTwo_param {K : Type*} [Field K] {t : K} (ht : t ≠ 0) :
    aevalAeval ((t + 16) ^ 3 / t) ((t + 256) ^ 3 / t ^ 2) modularPolynomialTwo = 0 := by
  rw [modularPolynomialTwo_eval]
  field_simp
  ring

/-- The modular equation relating `j(τ)` and `j(2τ)`. -/
theorem modularPolynomialTwo_jInvariant (τ : UpperHalfPlane) :
    aevalAeval (jInvariant τ) (jInvariant (UpperHalfPlane.ofComplex (2 * (τ : ℂ))))
      modularPolynomialTwo = 0 := by
  rw [jInvariant_eq_weberF₂ τ, jInvariant_two_mul_eq_weberF₂]
  exact modularPolynomialTwo_param (pow_ne_zero _ (weberF₂_ne_zero τ.im_pos))

/-- The `j`-value at `τ/2` also satisfies the level-two modular equation. -/
theorem modularPolynomialTwo_jInvariant_half (τ : UpperHalfPlane) :
    aevalAeval (jInvariant τ) (jInvariant (UpperHalfPlane.ofComplex ((τ : ℂ) / 2)))
      modularPolynomialTwo = 0 := by
  have hpos : 0 < ((τ : ℂ) / 2).im := by simpa using half_pos τ.im_pos
  have hdouble : UpperHalfPlane.ofComplex
      (2 * (UpperHalfPlane.ofComplex ((τ : ℂ) / 2) : ℂ)) = τ := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos,
      show 2 * ((τ : ℂ) / 2) = (τ : ℂ) by ring, UpperHalfPlane.ofComplex_apply]
  have h := modularPolynomialTwo_jInvariant (UpperHalfPlane.ofComplex ((τ : ℂ) / 2))
  rw [hdouble] at h
  rw [modularPolynomialTwo_eval_comm]
  exact h

/-- The `j`-value at `(τ+1)/2` satisfies the same level-two modular equation. -/
theorem modularPolynomialTwo_jInvariant_half_add_one (τ : UpperHalfPlane) :
    aevalAeval (jInvariant τ) (jInvariant (UpperHalfPlane.ofComplex (((τ : ℂ) + 1) / 2)))
      modularPolynomialTwo = 0 := by
  have h := modularPolynomialTwo_jInvariant_half ((1 : ℝ) +ᵥ τ)
  simpa only [jInvariant_add_one, UpperHalfPlane.coe_vadd, Complex.ofReal_one,
    add_comm (1 : ℂ)] using h

private theorem cubic_weber_transform (x y z j t : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hs : x + y + z = 48) (hp : x * y + x * z + y * z = 768 - j)
    (hq : x * y * z = 4096) :
    aevalAeval j t modularPolynomialTwo =
      (t - (256 - x) ^ 3 / x ^ 2) * (t - (256 - y) ^ 3 / y ^ 2) *
        (t - (256 - z) ^ 3 / z ^ 2) := by
  let s₁ := x + y + z
  let s₂ := x * y + x * z + y * z
  let s₃ := x * y * z
  let k : ℂ := 256
  have hclear :
      (t * x ^ 2 - (256 - x) ^ 3) * (t * y ^ 2 - (256 - y) ^ 3) *
          (t * z ^ 2 - (256 - z) ^ 3) =
        t ^ 3 * s₃ ^ 2 +
        t ^ 2 * (k ^ 3 * (2 * s₁ * s₃ - s₂ ^ 2) + 3 * k ^ 2 * s₂ * s₃ -
          9 * k * s₃ ^ 2 + s₁ * s₃ ^ 2) +
        t * (k ^ 6 * (s₁ ^ 2 - 2 * s₂) + k ^ 5 * (-3 * s₁ * s₂ + 9 * s₃) +
          k ^ 4 * (-3 * s₁ * s₃ + 6 * s₂ ^ 2) +
          k ^ 3 * (2 * s₁ ^ 2 * s₃ - s₁ * s₂ ^ 2 - 17 * s₂ * s₃) +
          k ^ 2 * (3 * s₁ * s₂ * s₃ + 18 * s₃ ^ 2) - 6 * k * s₁ * s₃ ^ 2 +
          s₂ * s₃ ^ 2) + (s₃ - k * s₂ + k ^ 2 * s₁ - k ^ 3) ^ 3 := by
    dsimp [s₁, s₂, s₃, k]
    ring
  dsimp [s₁, s₂, s₃, k] at hclear
  rw [hs, hp, hq] at hclear
  have hnum :
      (t * x ^ 2 - (256 - x) ^ 3) * (t * y ^ 2 - (256 - y) ^ 3) *
          (t * z ^ 2 - (256 - z) ^ 3) =
        16777216 * aevalAeval j t modularPolynomialTwo := by
    rw [modularPolynomialTwo_eval]
    linear_combination hclear
  have hden : x ^ 2 * y ^ 2 * z ^ 2 = 16777216 := by
    rw [← mul_pow, ← mul_pow, hq]
    norm_num
  calc
    aevalAeval j t modularPolynomialTwo =
        ((t * x ^ 2 - (256 - x) ^ 3) * (t * y ^ 2 - (256 - y) ^ 3) *
          (t * z ^ 2 - (256 - z) ^ 3)) / (x ^ 2 * y ^ 2 * z ^ 2) := by
      rw [hnum, hden]
      ring
    _ = _ := by
      field_simp

/-- The three analytic `j`-values factor the level-two modular polynomial,
including multiplicities. No distinctness of the values is assumed. -/
theorem modularPolynomialTwo_jInvariant_factorization (τ : UpperHalfPlane) (t : ℂ) :
    aevalAeval (jInvariant τ) t modularPolynomialTwo =
      (t - jInvariant (UpperHalfPlane.ofComplex (2 * (τ : ℂ)))) *
      (t - jInvariant (UpperHalfPlane.ofComplex ((τ : ℂ) / 2))) *
      (t - jInvariant (UpperHalfPlane.ofComplex (((τ : ℂ) + 1) / 2))) := by
  have hs : weberF τ ^ 24 + -(weberF₁ τ ^ 24) + -(weberF₂ τ ^ 24) = 48 := by
    linear_combination weberF_pow_24_sub_weberF₁_pow_24_sub_weberF₂_pow_24 τ.im_pos
  have hp :
      weberF τ ^ 24 * -(weberF₁ τ ^ 24) +
        weberF τ ^ 24 * -(weberF₂ τ ^ 24) +
        -(weberF₁ τ ^ 24) * -(weberF₂ τ ^ 24) = 768 - jInvariant τ := by
    linear_combination weber_second_symmetric τ
  have hq : weberF τ ^ 24 * -(weberF₁ τ ^ 24) * -(weberF₂ τ ^ 24) = 4096 := by
    simpa only [mul_neg, neg_mul, neg_neg] using weber_product_pow_24 τ.im_pos
  have h := cubic_weber_transform (weberF τ ^ 24) (-(weberF₁ τ ^ 24))
    (-(weberF₂ τ ^ 24)) (jInvariant τ) t
    (pow_ne_zero _ (weberF_ne_zero τ.im_pos))
    (neg_ne_zero.mpr (pow_ne_zero _ (weberF₁_ne_zero τ.im_pos)))
    (neg_ne_zero.mpr (pow_ne_zero _ (weberF₂_ne_zero τ.im_pos))) hs hp hq
  rw [jInvariant_two_mul_eq_weberF₂, jInvariant_half_eq_weberF₁,
    jInvariant_half_add_one_eq_weberF]
  convert h using 1
  ring

/-- Polynomial factorization with the three analytic roots listed with multiplicity. -/
theorem modularPolynomialTwo_jInvariant_factorization_polynomial (τ : UpperHalfPlane) :
    aevalAeval (C (jInvariant τ)) X modularPolynomialTwo =
      (X - C (jInvariant (UpperHalfPlane.ofComplex (2 * (τ : ℂ))))) *
      (X - C (jInvariant (UpperHalfPlane.ofComplex ((τ : ℂ) / 2)))) *
      (X - C (jInvariant (UpperHalfPlane.ofComplex (((τ : ℂ) + 1) / 2)))) := by
  simp only [modularPolynomialTwo, map_add, map_sub, map_mul, map_pow, map_ofNat,
    aevalAeval_X, aevalAeval_Y]
  apply Polynomial.funext
  intro t
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
  simpa only [modularPolynomialTwo_eval] using
    modularPolynomialTwo_jInvariant_factorization τ t

/-- These three analytic values exhaust the roots, even when some coincide. -/
theorem modularPolynomialTwo_jInvariant_eq_zero_iff (τ : UpperHalfPlane) (t : ℂ) :
    aevalAeval (jInvariant τ) t modularPolynomialTwo = 0 ↔
      t = jInvariant (UpperHalfPlane.ofComplex (2 * (τ : ℂ))) ∨
      t = jInvariant (UpperHalfPlane.ofComplex ((τ : ℂ) / 2)) ∨
      t = jInvariant (UpperHalfPlane.ofComplex (((τ : ℂ) + 1) / 2)) := by
  rw [modularPolynomialTwo_jInvariant_factorization τ t]
  simp only [mul_eq_zero, sub_eq_zero, or_assoc]

end

end ModularForm
