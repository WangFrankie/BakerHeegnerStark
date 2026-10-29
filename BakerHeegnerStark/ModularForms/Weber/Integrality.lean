/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.Polynomial
import BakerHeegnerStark.ModularForms.Weber.Bounds
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integrality of Weber Values

When `j(τ)` is an algebraic integer, Weber's actual cubic makes `𝔣(τ)²⁴`
integral over the integral closure of `ℤ` in `ℂ`. Transitivity and taking a
positive integral power then give integrality of `𝔣(τ)²` over `ℤ`. The normalized
gamma cubic likewise proves integrality of Heegner's `2/𝔣(z)²` whenever its
actual gamma coefficient is integral.

This uses no complex multiplication or rationality hypothesis and does not
assert the class-field membership supplied by Weber reciprocity.
-/

open Polynomial

namespace ModularForm

/-- Weber's twenty-fourth power is integral whenever the actual `j`-value is integral. -/
theorem isIntegral_weberF_pow_24_of_isIntegral_jInvariant (τ : UpperHalfPlane)
    (hj : IsIntegral ℤ (jInvariant τ)) : IsIntegral ℤ (weberF (τ : ℂ) ^ 24) := by
  let j : integralClosure ℤ ℂ := ⟨jInvariant τ, hj⟩
  have h24 : IsIntegral (integralClosure ℤ ℂ) (weberF (τ : ℂ) ^ 24) := by
    refine ⟨(X - C (16 : integralClosure ℤ ℂ)) ^ 3 - C j * X, ?_, ?_⟩
    · apply ((monic_X_sub_C (16 : integralClosure ℤ ℂ)).pow 3).sub_of_left
      apply degree_lt_degree
      calc
        (C j * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
        _ < ((X - C (16 : integralClosure ℤ ℂ)) ^ 3).natDegree := by
          rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C]
          norm_num
    · simp only [eval₂_sub, eval₂_pow, eval₂_mul, eval₂_C, eval₂_X, eval₂_ofNat, map_ofNat]
      change (weberF (τ : ℂ) ^ 24 - 16) ^ 3 -
        jInvariant τ * weberF (τ : ℂ) ^ 24 = 0
      exact sub_eq_zero.mpr (weberF_cubic τ)
  exact isIntegral_trans (weberF (τ : ℂ) ^ 24) h24

/-- The square of a Weber value is integral whenever its actual `j`-value is integral. -/
theorem isIntegral_weberF_sq_of_isIntegral_jInvariant (τ : UpperHalfPlane)
    (hj : IsIntegral ℤ (jInvariant τ)) : IsIntegral ℤ (weberF (τ : ℂ) ^ 2) := by
  have hpow : IsIntegral ℤ ((weberF (τ : ℂ) ^ 2) ^ 12) := by
    rw [← pow_mul]
    exact isIntegral_weberF_pow_24_of_isIntegral_jInvariant τ hj
  exact IsIntegral.of_pow (by norm_num : 0 < (12 : ℕ)) hpow

/-- Heegner's actual Weber quantity is integral whenever its normalized gamma
coefficient is integral; rationality of that coefficient is unnecessary. -/
theorem isIntegral_two_div_weberF_sq_of_isIntegral_gamma₂ {z : ℂ} (hz : 0 < z.im)
    (hγ : IsIntegral ℤ (gamma₂ (UpperHalfPlane.ofComplex ((z + 3) / 2)))) :
    IsIntegral ℤ (2 / weberF z ^ 2) := by
  let γ : integralClosure ℤ ℂ := ⟨gamma₂ (UpperHalfPlane.ofComplex ((z + 3) / 2)), hγ⟩
  have h4 : IsIntegral (integralClosure ℤ ℂ) ((2 / weberF z ^ 2) ^ 4) := by
    refine ⟨X ^ 3 - C γ * X - C 16, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_mul, eval₂_C, eval₂_X, eval₂_ofNat, map_ofNat]
    change ((2 / weberF z ^ 2) ^ 4) ^ 3 -
      gamma₂ (UpperHalfPlane.ofComplex ((z + 3) / 2)) * (2 / weberF z ^ 2) ^ 4 - 16 = 0
    exact weberF_fourthPower_cubic hz
  exact IsIntegral.of_pow (by norm_num : 0 < (4 : ℕ)) (isIntegral_trans _ h4)

end ModularForm
