/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.NormMinimum
import Mathlib.Data.Int.GCD

/-!
# Canonical Quadratic Norms Determined by the Discriminant

An integral change of the norm coordinate removes the even part of `B` in
`x²+B*x*k+C*k²`. It preserves coprimality and identifies its primitive value
spectrum with the even or odd canonical norm. The resulting constant is
positive when the original discriminant is negative.
-/

namespace BakerHeegnerStark

/-- The positive canonical constant after removing the even part of the trace. -/
def quadraticNormConstant (B C : ℤ) : ℤ :=
  C - (B / 2) ^ 2 - (B / 2) * (B % 2)

/-- The canonical constant recovers the actual discriminant and trace parity. -/
theorem quadraticNormConstant_discriminant (B C : ℤ) :
    4 * quadraticNormConstant B C = (B % 2) ^ 2 - (B ^ 2 - 4 * C) := by
  let q := B / 2
  let r := B % 2
  have hB : B = 2 * q + r := by dsimp [q, r]; omega
  change 4 * (C - q ^ 2 - q * r) = r ^ 2 - (B ^ 2 - 4 * C)
  rw [hB]
  ring

/-- Negative discriminant makes the normalized constant positive. -/
theorem quadraticNormConstant_pos {B C : ℤ} (hD : B ^ 2 - 4 * C < 0) :
    0 < quadraticNormConstant B C := by
  have h := quadraticNormConstant_discriminant B C
  nlinarith [sq_nonneg (B % 2)]

/-- An integral triangular change of norm coordinates preserves primitivity. -/
theorem coprime_natAbs_add_mul_iff (x k q : ℤ) :
    Nat.Coprime (x + q * k).natAbs k.natAbs ↔ Nat.Coprime x.natAbs k.natAbs := by
  change Int.gcd (x + q * k) k = 1 ↔ Int.gcd x k = 1
  rw [mul_comm q k, Int.gcd_add_mul_left_left]

/-- Even trace gives the even canonical norm after an actual integral shift. -/
theorem quadraticNorm_eq_even {B C : ℤ} (hB : B % 2 = 0) (x k : ℤ) :
    x ^ 2 + B * x * k + C * k ^ 2 =
      evenQuadraticNorm (quadraticNormConstant B C) (x + (B / 2) * k) k := by
  let q := B / 2
  have htrace : B = 2 * q := by dsimp [q]; omega
  have hc : quadraticNormConstant B C = C - q ^ 2 := by
    simp only [quadraticNormConstant, hB, mul_zero, sub_zero]
    rfl
  change x ^ 2 + B * x * k + C * k ^ 2 =
    (x + q * k) ^ 2 + quadraticNormConstant B C * k ^ 2
  rw [hc, htrace]
  ring

/-- Odd trace gives the odd canonical norm, with its minus-sign convention. -/
theorem quadraticNorm_eq_odd {B C : ℤ} (hB : B % 2 = 1) (x k : ℤ) :
    x ^ 2 + B * x * k + C * k ^ 2 =
      oddQuadraticNorm (quadraticNormConstant B C) (-(x + (B / 2) * k)) k := by
  let q := B / 2
  have htrace : B = 2 * q + 1 := by dsimp [q]; omega
  have hc : quadraticNormConstant B C = C - q ^ 2 - q := by
    simp only [quadraticNormConstant, hB, mul_one]
    rfl
  change x ^ 2 + B * x * k + C * k ^ 2 =
    (-(x + q * k)) ^ 2 - (-(x + q * k)) * k + quadraticNormConstant B C * k ^ 2
  rw [hc, htrace]
  ring

/-- The even-trace primitive norm spectrum is exactly the canonical even spectrum. -/
theorem primitiveQuadraticNorm_iff_even {B C : ℤ} (hB : B % 2 = 0) (n : ℤ) :
    (∃ x k : ℤ, Nat.Coprime x.natAbs k.natAbs ∧
      x ^ 2 + B * x * k + C * k ^ 2 = n) ↔
      PrimitiveEvenNormValue (quadraticNormConstant B C) n := by
  let q := B / 2
  constructor
  · rintro ⟨x, k, hcop, hnorm⟩
    refine ⟨x + q * k, k, (coprime_natAbs_add_mul_iff x k q).mpr hcop, ?_⟩
    exact (quadraticNorm_eq_even hB x k).symm.trans hnorm
  · rintro ⟨y, k, hcop, hnorm⟩
    refine ⟨y + (-q) * k, k, (coprime_natAbs_add_mul_iff y k (-q)).mpr hcop, ?_⟩
    rw [quadraticNorm_eq_even hB]
    change evenQuadraticNorm (quadraticNormConstant B C)
      (y + (-q) * k + q * k) k = n
    have hy : y + (-q) * k + q * k = y := by ring
    rw [hy]
    exact hnorm

/-- The odd-trace primitive norm spectrum is exactly the canonical odd spectrum. -/
theorem primitiveQuadraticNorm_iff_odd {B C : ℤ} (hB : B % 2 = 1) (n : ℤ) :
    (∃ x k : ℤ, Nat.Coprime x.natAbs k.natAbs ∧
      x ^ 2 + B * x * k + C * k ^ 2 = n) ↔
      PrimitiveOddNormValue (quadraticNormConstant B C) n := by
  let q := B / 2
  constructor
  · rintro ⟨x, k, hcop, hnorm⟩
    refine ⟨-(x + q * k), k, ?_, ?_⟩
    · simpa only [Int.natAbs_neg] using (coprime_natAbs_add_mul_iff x k q).mpr hcop
    · exact (quadraticNorm_eq_odd hB x k).symm.trans hnorm
  · rintro ⟨y, k, hcop, hnorm⟩
    refine ⟨-(y + q * k), k, ?_, ?_⟩
    · simpa only [Int.natAbs_neg] using (coprime_natAbs_add_mul_iff y k q).mpr hcop
    · rw [quadraticNorm_eq_odd hB]
      change oddQuadraticNorm (quadraticNormConstant B C)
        (-(-(y + q * k) + q * k)) k = n
      have hy : -(-(y + q * k) + q * k) = y := by ring
      rw [hy]
      exact hnorm

end BakerHeegnerStark
