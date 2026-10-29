/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ClassNumberOne.Heegner.IntegralPoints
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Heegner's Algebraic Step

Let `v` be a root of a monic integer cubic whose fourth power `w = v⁴` is a
root of `W³ - γW - 16` for an integer `γ < -15`. The latter cubic is then
irreducible over `ℚ`, so it is the minimal polynomial of `w`. It must equal the
monic cubic whose roots are the fourth powers of the roots of the cubic of `v`.
Comparing coefficients gives an integral point on `Y² = 2X(X³ + 1)` and expresses
`γ` by `heegnerGammaValue`.

This is the algebraic core of Heegner's argument, following Cox, *Primes of the
form x² + ny²*, §12.C. No modular function or class-number input is used here.
-/

open Polynomial

namespace BakerHeegnerStark

/-- The cubic `W³ - γW - 16` has no rational root when `γ < -15`. -/
theorem heegnerGammaCubic_ne_zero_of_rat (γ : ℤ) (hγ : γ < -15) (x : ℚ) :
    x ^ 3 - (γ : ℚ) * x - 16 ≠ 0 := by
  intro hx
  have hmonic : (X ^ 3 - C γ * X - C 16 : ℤ[X]).Monic := by monicity!
  obtain ⟨k, hk⟩ := isInteger_of_is_root_of_monic hmonic (r := x)
    (by simpa [map_ofNat] using hx)
  rw [← hk] at hx
  simp only [algebraMap_int_eq, eq_intCast] at hx
  have hk' : k ^ 3 - γ * k - 16 = 0 := by exact_mod_cast hx
  rcases lt_trichotomy k 0 with hneg | hzero | hpos
  · have hγk : 0 < k * γ := mul_pos_of_neg_of_neg hneg (by linarith)
    have hk3 : k ^ 3 ≤ 0 := by
      have := mul_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg k)
      nlinarith
    nlinarith
  · subst hzero
    norm_num at hk'
  · have hγk : 0 ≤ (-16 - γ) * k := mul_nonneg (by linarith) hpos.le
    have hk3 : 0 < k ^ 3 := pow_pos hpos 3
    nlinarith

/-- For `γ < -15`, the cubic `W³ - γW - 16` is irreducible over `ℚ`. -/
theorem irreducible_heegnerGammaCubic (γ : ℤ) (hγ : γ < -15) :
    Irreducible (X ^ 3 - C (γ : ℚ) * X - C 16 : ℚ[X]) := by
  have hdeg : (X ^ 3 - C (γ : ℚ) * X - C 16 : ℚ[X]).natDegree = 3 := by
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [hdeg]
    simp
  · intro x hx
    apply heegnerGammaCubic_ne_zero_of_rat γ hγ x
    simpa [IsRoot] using hx

/-- Integer coefficient equations of Heegner's argument give an integral point
on `Y² = 2X(X³ + 1)` whose associated gamma value is `γ`. -/
theorem heegner_point_of_coefficient_equations {a b γ : ℤ}
    (h₁ : (a ^ 2 - 2 * b) ^ 2 - 2 * (b ^ 2 - 4 * a) = 0)
    (h₂ : (b ^ 2 - 4 * a) ^ 2 - 8 * (a ^ 2 - 2 * b) = -γ) :
    ∃ X Y : ℤ, HeegnerXYEquation X Y ∧ γ = heegnerGammaValue X Y := by
  have ha : (2 : ℤ) ∣ a := by
    have hsq : (2 : ℤ) ∣ (a ^ 2 - 2 * b) ^ 2 := ⟨b ^ 2 - 4 * a, by linear_combination h₁⟩
    have hbase := Int.prime_two.dvd_of_dvd_pow hsq
    have ha2 : (2 : ℤ) ∣ a ^ 2 := by
      have := dvd_add hbase (dvd_mul_right 2 b)
      simpa using this
    exact Int.prime_two.dvd_of_dvd_pow ha2
  obtain ⟨k, rfl⟩ := ha
  have hb : (2 : ℤ) ∣ b := by
    have hsq : (2 : ℤ) ∣ b ^ 2 :=
      ⟨4 * k ^ 2 * b - 4 * k ^ 4 - 4 * k, by linarith⟩
    exact Int.prime_two.dvd_of_dvd_pow hsq
  obtain ⟨l, rfl⟩ := hb
  refine ⟨-k, l - 2 * k ^ 2, ?_, ?_⟩
  · have h8 : 8 * ((l - 2 * k ^ 2) ^ 2 - 2 * -k * ((-k) ^ 3 + 1)) = 0 := by
      linear_combination h₁
    unfold HeegnerXYEquation
    have := (mul_eq_zero.mp h8).resolve_left (by norm_num)
    linear_combination this
  · simp only [heegnerGammaValue]
    linear_combination h₂

/-- If `v` is a root of `X³ + aX² + bX + c`, then `v⁴` is a root of the monic
cubic whose roots are the fourth powers of the roots of that cubic. -/
theorem fourthPowerCubic_eval_eq_zero {R : Type*} [CommRing R] {v a b c : R}
    (hv : v ^ 3 + a * v ^ 2 + b * v + c = 0) :
    (v ^ 4) ^ 3 - ((a ^ 2 - 2 * b) ^ 2 - 2 * (b ^ 2 - 2 * a * c)) * (v ^ 4) ^ 2 +
      ((b ^ 2 - 2 * a * c) ^ 2 - 2 * (a ^ 2 - 2 * b) * c ^ 2) * v ^ 4 - c ^ 4 = 0 := by
  linear_combination ((v ^ 3 - a * v ^ 2 + b * v - c) *
    ((a * v ^ 2 - c) ^ 2 + (v ^ 3 - b * v) ^ 2)) * hv

/-- **Heegner's algebraic step.** A root of a monic integer cubic whose fourth
power satisfies `W³ - γW - 16 = 0`, with `γ < -15`, yields an integral point
on `Y² = 2X(X³ + 1)` whose gamma value is `γ`. -/
theorem heegner_point_of_monic_cubic {v : ℂ} {a b c γ : ℤ}
    (hv : v ^ 3 + a * v ^ 2 + b * v + c = 0)
    (hw : (v ^ 4) ^ 3 - γ * v ^ 4 - 16 = 0) (hγ : γ < -15) :
    ∃ X Y : ℤ, HeegnerXYEquation X Y ∧ γ = heegnerGammaValue X Y := by
  let s₁ : ℤ := (a ^ 2 - 2 * b) ^ 2 - 2 * (b ^ 2 - 2 * a * c)
  let s₂ : ℤ := (b ^ 2 - 2 * a * c) ^ 2 - 2 * (a ^ 2 - 2 * b) * c ^ 2
  let R₀ : ℚ[X] := X ^ 3 - C (γ : ℚ) * X - C 16
  let Rp : ℚ[X] := X ^ 3 - C (s₁ : ℚ) * X ^ 2 + C (s₂ : ℚ) * X - C ((c : ℚ) ^ 4)
  have hR₀ : aeval (v ^ 4) R₀ = 0 := by
    simpa [R₀] using hw
  have hRp : aeval (v ^ 4) Rp = 0 := by
    have h := fourthPowerCubic_eval_eq_zero hv
    simp only [Rp, s₁, s₂, map_sub, map_add, map_mul, aeval_X_pow, aeval_X, aeval_C,
      eq_ratCast, Rat.cast_intCast, Rat.cast_pow]
    push_cast
    exact h
  have hR₀monic : R₀.Monic := by
    simp only [R₀]
    monicity!
  have hRpmonic : Rp.Monic := by
    simp only [Rp]
    monicity!
  have hmin : R₀ = minpoly ℚ (v ^ 4) :=
    minpoly.eq_of_irreducible_of_monic (irreducible_heegnerGammaCubic γ hγ) hR₀ hR₀monic
  have hdvd : R₀ ∣ Rp := hmin ▸ minpoly.dvd ℚ (v ^ 4) hRp
  have hRpdeg : Rp.natDegree ≤ R₀.natDegree := by
    have h₁ : Rp.natDegree = 3 := by
      simp only [Rp]
      compute_degree!
    have h₂ : R₀.natDegree = 3 := by
      simp only [R₀]
      compute_degree!
    omega
  have heq : Rp = R₀ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hR₀monic hRpmonic hdvd hRpdeg
  have hc₂ := congrArg (fun P : ℚ[X] => P.coeff 2) heq
  have hc₁ := congrArg (fun P : ℚ[X] => P.coeff 1) heq
  have hc₀ := congrArg (fun P : ℚ[X] => P.coeff 0) heq
  simp only [Rp, R₀, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
    at hc₂ hc₁ hc₀
  norm_num at hc₂ hc₁ hc₀
  have hs₁ : s₁ = 0 := by exact_mod_cast hc₂
  have hs₂ : s₂ = -γ := by exact_mod_cast hc₁
  have hc4 : c ^ 4 = 16 := by exact_mod_cast hc₀
  have hc : c = 2 ∨ c = -2 := by
    have hfactor : (c - 2) * (c + 2) * (c ^ 2 + 4) = 0 := by linear_combination hc4
    rcases mul_eq_zero.mp hfactor with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · nlinarith [sq_nonneg c]
  rcases hc with rfl | rfl
  · apply heegner_point_of_coefficient_equations (a := a) (b := b)
    · linear_combination hs₁
    · linear_combination hs₂
  · apply heegner_point_of_coefficient_equations (a := -a) (b := b)
    · linear_combination hs₁
    · linear_combination hs₂

end BakerHeegnerStark
