/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Integral matrices fixing a monic quadratic point

If an upper-half-plane point satisfies `τ² + Bτ + C = 0`, its integral
fixed-point matrices are exactly `!![x, -k*C; k, x+k*B]`. Their determinants
are the norms `x² + B*x*k + C*k²`, and their entries are primitive exactly
when `x.natAbs` and `k.natAbs` are coprime. Thus primitive fixed matrices
of any prescribed integral determinant are equivalent to primitive norm
representations. At natural levels greater than one, the coefficient `k`
cannot vanish.

Only the stated monic quadratic equation and nonreality of the point are
used; no classification of quadratic points or binary quadratic forms is
needed.
-/

open Matrix

namespace BakerHeegnerStark

/-- The integral fixed-point matrix attached to a pair of norm coordinates. -/
def quadraticFixedMatrix (B C x k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![x, -k * C; k, x + k * B]

private theorem int_linear_eq_zero_of_upperHalfPlane
    (τ : UpperHalfPlane) (u v : ℤ)
    (h : (u : ℂ) * (τ : ℂ) + v = 0) : u = 0 ∧ v = 0 := by
  have him : (u : ℝ) * τ.im = 0 := by
    simpa [Complex.mul_im] using congrArg Complex.im h
  have hu : u = 0 :=
    Int.cast_eq_zero.mp ((mul_eq_zero.mp him).resolve_right τ.im_ne_zero)
  have hvC : (v : ℂ) = 0 := by simpa [hu] using h
  have hv : v = 0 := Int.cast_eq_zero.mp hvC
  exact ⟨hu, hv⟩

/-- Every norm-coordinate matrix satisfies the raw fixed-point equation. -/
theorem quadraticFixedMatrix_fixed (τ : UpperHalfPlane) (B C : ℤ)
    (hτ : (τ : ℂ) ^ 2 + (B : ℂ) * (τ : ℂ) + C = 0) (x k : ℤ) :
    ((quadraticFixedMatrix B C x k) 0 0 : ℂ) * (τ : ℂ) +
        (quadraticFixedMatrix B C x k) 0 1 =
      (τ : ℂ) * (((quadraticFixedMatrix B C x k) 1 0 : ℂ) * (τ : ℂ) +
        (quadraticFixedMatrix B C x k) 1 1) := by
  change (x : ℂ) * (τ : ℂ) + ((-k * C : ℤ) : ℂ) =
    (τ : ℂ) * ((k : ℂ) * (τ : ℂ) + ((x + k * B : ℤ) : ℂ))
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_add]
  linear_combination -(k : ℂ) * hτ

/-- Nonreality makes the two integral coefficients left after quadratic
substitution vanish separately, giving the complete fixed-matrix description. -/
theorem fixed_iff_eq_quadraticFixedMatrix (τ : UpperHalfPlane) (B C : ℤ)
    (hτ : (τ : ℂ) ^ 2 + (B : ℂ) * (τ : ℂ) + C = 0)
    (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ((A 0 0 : ℂ) * (τ : ℂ) + A 0 1 =
        (τ : ℂ) * ((A 1 0 : ℂ) * (τ : ℂ) + A 1 1)) ↔
      ∃ x k : ℤ, A = quadraticFixedMatrix B C x k := by
  constructor
  · intro hfix
    have hlin : ((A 0 0 - A 1 1 + A 1 0 * B : ℤ) : ℂ) * (τ : ℂ) +
        ((A 0 1 + A 1 0 * C : ℤ) : ℂ) = 0 := by
      simp only [Int.cast_add, Int.cast_sub, Int.cast_mul]
      linear_combination hfix + (A 1 0 : ℂ) * hτ
    obtain ⟨hu, hv⟩ := int_linear_eq_zero_of_upperHalfPlane τ _ _ hlin
    have hb : A 0 1 = -(A 1 0) * C := by
      linear_combination hv
    have hd : A 1 1 = A 0 0 + A 1 0 * B := by
      linear_combination -hu
    refine ⟨A 0 0, A 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadraticFixedMatrix, hb, hd]
  · rintro ⟨x, k, rfl⟩
    exact quadraticFixedMatrix_fixed τ B C hτ x k

/-- The determinant is the monic quadratic norm, with the same sign of `B`
as in the equation of the point. -/
theorem quadraticFixedMatrix_det (B C x k : ℤ) :
    (quadraticFixedMatrix B C x k).det = x ^ 2 + B * x * k + C * k ^ 2 := by
  rw [Matrix.det_fin_two]
  change x * (x + k * B) - (-k * C) * k = x ^ 2 + B * x * k + C * k ^ 2
  ring

/-- Common divisors of all four entries are precisely common divisors of
`x` and `k`; this holds for every integer divisor, including zero. -/
theorem dvd_entries_quadraticFixedMatrix_iff (B C x k d : ℤ) :
    (∀ i j, d ∣ (quadraticFixedMatrix B C x k) i j) ↔ d ∣ x ∧ d ∣ k := by
  constructor
  · intro h
    exact ⟨h 0 0, h 1 0⟩
  · rintro ⟨hx, hk⟩ i j
    fin_cases i <;> fin_cases j
    · exact hx
    · change d ∣ -k * C
      exact dvd_mul_of_dvd_left (dvd_neg.mpr hk) C
    · exact hk
    · change d ∣ x + k * B
      exact dvd_add hx (dvd_mul_of_dvd_left hk B)

/-- Primitivity uses exactly the natural common-divisor convention for
integral cyclic-sublattice matrices. -/
theorem quadraticFixedMatrix_primitive_iff (B C x k : ℤ) :
    (∀ d : ℕ, (∀ i j, (d : ℤ) ∣ (quadraticFixedMatrix B C x k) i j) → d = 1) ↔
      Nat.Coprime x.natAbs k.natAbs := by
  have hentries (d : ℕ) :
      (∀ i j, (d : ℤ) ∣ (quadraticFixedMatrix B C x k) i j) ↔
        d ∣ Nat.gcd x.natAbs k.natAbs := by
    rw [dvd_entries_quadraticFixedMatrix_iff]
    simp only [Int.natCast_dvd, Nat.dvd_gcd_iff]
  constructor
  · intro h
    change Nat.gcd x.natAbs k.natAbs = 1
    exact h _ ((hentries _).mpr dvd_rfl)
  · intro h d hd
    have hg : Nat.gcd x.natAbs k.natAbs = 1 := h
    apply Nat.dvd_one.mp
    rw [← hg]
    exact (hentries d).mp hd

/-- A primitive scalar norm-coordinate matrix has determinant one. -/
theorem quadraticFixedMatrix_det_eq_one_of_k_eq_zero (B C x k : ℤ)
    (hprim : ∀ d : ℕ,
      (∀ i j, (d : ℤ) ∣ (quadraticFixedMatrix B C x k) i j) → d = 1)
    (hk : k = 0) : (quadraticFixedMatrix B C x k).det = 1 := by
  have hcop := (quadraticFixedMatrix_primitive_iff B C x k).mp hprim
  have hx : x.natAbs = 1 := by simpa [hk] using hcop
  obtain hx | hx := Int.natAbs_eq_iff.mp hx
  · simp [quadraticFixedMatrix_det, hk, hx]
  · simp [quadraticFixedMatrix_det, hk, hx]

/-- A primitive norm representation of a determinant other than one is
necessarily nonscalar. The determinant need not be positive. -/
theorem quadraticNorm_k_ne_zero (B C x k n : ℤ)
    (hcop : Nat.Coprime x.natAbs k.natAbs)
    (hnorm : x ^ 2 + B * x * k + C * k ^ 2 = n) (hn : n ≠ 1) : k ≠ 0 := by
  intro hk
  apply hn
  calc
    n = (quadraticFixedMatrix B C x k).det :=
      ((quadraticFixedMatrix_det B C x k).trans hnorm).symm
    _ = 1 := quadraticFixedMatrix_det_eq_one_of_k_eq_zero B C x k
      ((quadraticFixedMatrix_primitive_iff B C x k).mpr hcop) hk

/-- Primitive integral fixed matrices of an arbitrary specified integer
determinant are equivalent to primitive quadratic norm representations. -/
theorem exists_primitive_fixedMatrix_iff_quadraticNorm
    (τ : UpperHalfPlane) (B C : ℤ)
    (hτ : (τ : ℂ) ^ 2 + (B : ℂ) * (τ : ℂ) + C = 0) (n : ℤ) :
    (∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      A.det = n ∧
      (∀ d : ℕ, (∀ i j, (d : ℤ) ∣ A i j) → d = 1) ∧
      (A 0 0 : ℂ) * (τ : ℂ) + A 0 1 =
        (τ : ℂ) * ((A 1 0 : ℂ) * (τ : ℂ) + A 1 1)) ↔
      ∃ x k : ℤ, Nat.Coprime x.natAbs k.natAbs ∧
        x ^ 2 + B * x * k + C * k ^ 2 = n := by
  constructor
  · rintro ⟨A, hdet, hprim, hfix⟩
    obtain ⟨x, k, rfl⟩ := (fixed_iff_eq_quadraticFixedMatrix τ B C hτ A).mp hfix
    refine ⟨x, k, (quadraticFixedMatrix_primitive_iff B C x k).mp hprim, ?_⟩
    simpa only [quadraticFixedMatrix_det] using hdet
  · rintro ⟨x, k, hcop, hnorm⟩
    exact ⟨quadraticFixedMatrix B C x k,
      (quadraticFixedMatrix_det B C x k).trans hnorm,
      (quadraticFixedMatrix_primitive_iff B C x k).mpr hcop,
      quadraticFixedMatrix_fixed τ B C hτ x k⟩

/-- At a natural level greater than one, primitive fixed matrices are
exactly primitive norm representations with a nonzero quadratic coordinate. -/
theorem exists_primitive_fixedMatrix_nat_iff_quadraticNorm
    (τ : UpperHalfPlane) (B C : ℤ)
    (hτ : (τ : ℂ) ^ 2 + (B : ℂ) * (τ : ℂ) + C = 0)
    (N : ℕ) (hN : 1 < N) :
    (∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      A.det = (N : ℤ) ∧
      (∀ d : ℕ, (∀ i j, (d : ℤ) ∣ A i j) → d = 1) ∧
      (A 0 0 : ℂ) * (τ : ℂ) + A 0 1 =
        (τ : ℂ) * ((A 1 0 : ℂ) * (τ : ℂ) + A 1 1)) ↔
      ∃ x k : ℤ, Nat.Coprime x.natAbs k.natAbs ∧ k ≠ 0 ∧
        x ^ 2 + B * x * k + C * k ^ 2 = (N : ℤ) := by
  rw [exists_primitive_fixedMatrix_iff_quadraticNorm τ B C hτ (N : ℤ)]
  constructor
  · rintro ⟨x, k, hcop, hnorm⟩
    have hN' : (N : ℤ) ≠ 1 := by
      intro heq
      have heq' : N = 1 := Int.natCast_inj.mp heq
      exact (ne_of_gt hN) heq'
    exact ⟨x, k, hcop, quadraticNorm_k_ne_zero B C x k N hcop hnorm hN', hnorm⟩
  · rintro ⟨x, k, hcop, _, hnorm⟩
    exact ⟨x, k, hcop, hnorm⟩

end BakerHeegnerStark
