/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Small norms in the imaginary quadratic CM order

For the actual order `ℤ[√-m]`, these elementary norm bounds rule out
nonconstant endomorphisms of norms nine and sixty-four. They are the
small-norm obstructions needed to separate cyclic neighbours at levels
three and eight; they do not themselves assert that separation or any CM
reciprocity theorem.

The norm-sixty-four argument uses the square residues modulo eight, proved
by kernel reduction in `ZMod 8`, and two parity descents. No primality,
squarefreeness, or class-number hypothesis is used.
-/

namespace BakerHeegnerStark

private theorem quadraticNorm_coefficient_eq_zero {m n : ℕ} (hm : n < m)
    (a b : ℤ) (h : a ^ 2 + (m : ℤ) * b ^ 2 = n) : b = 0 := by
  have hm' : (n : ℤ) < m := by exact_mod_cast hm
  by_contra hb
  have hb' : 1 ≤ b ^ 2 := by
    have hb_cases : b ≤ -1 ∨ 1 ≤ b := by omega
    rcases hb_cases with hb_cases | hb_cases <;> nlinarith
  have hmb : (m : ℤ) ≤ (m : ℤ) * b ^ 2 := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hb' (by omega : (0 : ℤ) ≤ m)
  nlinarith [sq_nonneg a]

private theorem two_dvd_of_quadraticNorm_dvd_eight {m : ℕ} (hm : m % 8 = 3)
    (a b : ℤ) (h : (8 : ℤ) ∣ a ^ 2 + (m : ℤ) * b ^ 2) :
    (2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b := by
  have hm' : (m : ZMod 8) = 3 := by
    rw [← ZMod.natCast_mod m 8, hm]
    rfl
  have hmod : (a : ZMod 8) ^ 2 + 3 * (b : ZMod 8) ^ 2 = 0 := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_natCast, hm'] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + (m : ℤ) * b ^ 2) 8).mpr h
  let π : ZMod 8 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)
  have hparity : ∀ x y : ZMod 8, x ^ 2 + 3 * y ^ 2 = 0 → π x = 0 ∧ π y = 0 := by
    decide +kernel
  have hp := hparity (a : ZMod 8) (b : ZMod 8) hmod
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp
    simpa only [map_intCast] using hp.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp
    simpa only [map_intCast] using hp.2

/-- In the CM order `ℤ[√-m]`, a norm-nine element is `±3` if `m > 9`. -/
theorem quadraticNorm_eq_nine_iff {m : ℕ} (hm : 9 < m) (a b : ℤ) :
    a ^ 2 + (m : ℤ) * b ^ 2 = 9 ↔ b = 0 ∧ (a = 3 ∨ a = -3) := by
  constructor
  · intro h
    have hb := quadraticNorm_coefficient_eq_zero (n := 9) hm a b h
    refine ⟨hb, ?_⟩
    subst b
    have hp : (a - 3) * (a + 3) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hp with hp | hp
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num

/-- For `m ≡ 3 (mod 8)` and `m > 4`, a norm-sixty-four element of
`ℤ[√-m]` is `±8`. Two parity descents reduce the nonconstant norm to four. -/
theorem quadraticNorm_eq_sixty_four_iff {m : ℕ} (hm : 4 < m) (hm8 : m % 8 = 3)
    (a b : ℤ) :
    a ^ 2 + (m : ℤ) * b ^ 2 = 64 ↔ b = 0 ∧ (a = 8 ∨ a = -8) := by
  constructor
  · intro h
    have hdiv : (8 : ℤ) ∣ a ^ 2 + (m : ℤ) * b ^ 2 := by rw [h]; norm_num
    obtain ⟨⟨a₁, rfl⟩, ⟨b₁, rfl⟩⟩ :=
      two_dvd_of_quadraticNorm_dvd_eight hm8 a b hdiv
    have h₁ : a₁ ^ 2 + (m : ℤ) * b₁ ^ 2 = 16 := by nlinarith [h]
    have hdiv₁ : (8 : ℤ) ∣ a₁ ^ 2 + (m : ℤ) * b₁ ^ 2 := by rw [h₁]; norm_num
    obtain ⟨⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩⟩ :=
      two_dvd_of_quadraticNorm_dvd_eight hm8 a₁ b₁ hdiv₁
    have h₂ : a₂ ^ 2 + (m : ℤ) * b₂ ^ 2 = 4 := by rw [ha₂, hb₂] at h₁; nlinarith [h₁]
    have hb₂zero := quadraticNorm_coefficient_eq_zero (n := 4) hm a₂ b₂ h₂
    have hb₁zero : b₁ = 0 := by rw [hb₂, hb₂zero]; ring
    refine ⟨by rw [hb₁zero]; ring, ?_⟩
    have hp : (2 * a₁ - 8) * (2 * a₁ + 8) = 0 := by
      rw [hb₁zero] at h
      nlinarith [h]
    rcases mul_eq_zero.mp hp with hp | hp
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num

end BakerHeegnerStark
