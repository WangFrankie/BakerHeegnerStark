/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.FixedMatrices
import Mathlib.Data.Int.GCD

/-!
# Integral matrices fixing a primitive quadratic point

For a primitive integral relation `aτ² + bτ + c = 0` with `a ≠ 0`, the integral
matrices fixing `τ` are exactly `!![x, -k*c; k*a, x+k*b]`. Their determinants
are `x² + b*x*k + a*c*k²`, and their entries are primitive exactly when
`x.natAbs` and `k.natAbs` are coprime. This gives primitive norm
representations for every prescribed integer determinant.

Primitivity means `gcd (gcd |a| |b|) |c| = 1`, not pairwise coprimality.
Two integer extended-gcd identities supply the needed cancellation of all
three coefficients, with no sign restrictions. The monic API in
`QuadraticFixedMatrices` is unchanged.
-/

open Matrix

namespace BakerHeegnerStark

/-- The integral fixed-point matrix for a primitive, not necessarily monic,
quadratic relation. -/
def primitiveQuadraticFixedMatrix (a b c x k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![x, -k * c; k * a, x + k * b]

/-- Multiplying all three primitive coefficients cannot introduce a new
common divisor. The proof uses the actual integer Bézout identities twice. -/
private theorem dvd_of_dvd_mul_primitive_coefficients (a b c m d : ℤ)
    (hprim : Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1)
    (ha : d ∣ m * a) (hb : d ∣ m * b) (hc : d ∣ m * c) : d ∣ m := by
  let g : ℤ := Int.gcd a b
  have hg : Int.gcd g c = 1 := by
    simpa only [g, Int.gcd_def, Int.natAbs_natCast] using hprim
  have hab : g = a * Int.gcdA a b + b * Int.gcdB a b :=
    Int.gcd_eq_gcd_ab a b
  have hgc : (1 : ℤ) = g * Int.gcdA g c + c * Int.gcdB g c := by
    simpa only [hg, Nat.cast_one] using Int.gcd_eq_gcd_ab g c
  have hmg : d ∣ m * g := by
    rw [hab, mul_add]
    exact dvd_add
      (by simpa only [mul_assoc] using dvd_mul_of_dvd_left ha (Int.gcdA a b))
      (by simpa only [mul_assoc] using dvd_mul_of_dvd_left hb (Int.gcdB a b))
  have hm : m = (m * g) * Int.gcdA g c + (m * c) * Int.gcdB g c := by
    linear_combination m * hgc
  rw [hm]
  exact dvd_add (dvd_mul_of_dvd_left hmg (Int.gcdA g c))
    (dvd_mul_of_dvd_left hc (Int.gcdB g c))

private theorem primitive_int_linear_eq_zero_of_upperHalfPlane
    (τ : UpperHalfPlane) (u v : ℤ)
    (h : (u : ℂ) * (τ : ℂ) + v = 0) : u = 0 ∧ v = 0 := by
  have him : (u : ℝ) * τ.im = 0 := by
    simpa [Complex.mul_im] using congrArg Complex.im h
  have hu : u = 0 :=
    Int.cast_eq_zero.mp ((mul_eq_zero.mp him).resolve_right τ.im_ne_zero)
  have hvC : (v : ℂ) = 0 := by simpa [hu] using h
  exact ⟨hu, Int.cast_eq_zero.mp hvC⟩

/-- Every primitive-quadratic coordinate matrix satisfies the raw fixed-point
equation; this direction does not require coefficient primitivity. -/
theorem primitiveQuadraticFixedMatrix_fixed (τ : UpperHalfPlane) (a b c : ℤ)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0) (x k : ℤ) :
    ((primitiveQuadraticFixedMatrix a b c x k) 0 0 : ℂ) * (τ : ℂ) +
        (primitiveQuadraticFixedMatrix a b c x k) 0 1 =
      (τ : ℂ) * (((primitiveQuadraticFixedMatrix a b c x k) 1 0 : ℂ) *
        (τ : ℂ) + (primitiveQuadraticFixedMatrix a b c x k) 1 1) := by
  change (x : ℂ) * (τ : ℂ) + ((-k * c : ℤ) : ℂ) =
    (τ : ℂ) * (((k * a : ℤ) : ℂ) * (τ : ℂ) + ((x + k * b : ℤ) : ℂ))
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_add]
  linear_combination -(k : ℂ) * hτ

/-- Every integral fixed matrix has primitive-quadratic coordinates. Nonreality
first identifies the two linear coefficients. Bézout for all three
coefficients then proves `a ∣ A 1 0`, without any pairwise coprimality. -/
theorem fixed_iff_eq_primitiveQuadraticFixedMatrix (τ : UpperHalfPlane) (a b c : ℤ)
    (ha : a ≠ 0)
    (hprim : Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0)
    (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ((A 0 0 : ℂ) * (τ : ℂ) + A 0 1 =
        (τ : ℂ) * ((A 1 0 : ℂ) * (τ : ℂ) + A 1 1)) ↔
      ∃ x k : ℤ, A = primitiveQuadraticFixedMatrix a b c x k := by
  constructor
  · intro hfix
    have hlin : ((a * (A 0 0 - A 1 1) + A 1 0 * b : ℤ) : ℂ) * (τ : ℂ) +
        ((a * A 0 1 + A 1 0 * c : ℤ) : ℂ) = 0 := by
      simp only [Int.cast_add, Int.cast_sub, Int.cast_mul]
      linear_combination (a : ℂ) * hfix + (A 1 0 : ℂ) * hτ
    obtain ⟨hu, hv⟩ := primitive_int_linear_eq_zero_of_upperHalfPlane τ _ _ hlin
    have hab : a ∣ A 1 0 * b := by
      refine ⟨A 1 1 - A 0 0, ?_⟩
      linear_combination hu
    have hac : a ∣ A 1 0 * c := by
      refine ⟨-A 0 1, ?_⟩
      linear_combination hv
    have hdiv : a ∣ A 1 0 :=
      dvd_of_dvd_mul_primitive_coefficients a b c (A 1 0) a hprim
        (dvd_mul_left a (A 1 0)) hab hac
    obtain ⟨k, hk⟩ := hdiv
    rw [hk] at hu hv
    have hb : A 0 1 = -k * c := by
      apply mul_left_cancel₀ ha
      linear_combination hv
    have hd : A 1 1 = A 0 0 + k * b := by
      apply mul_left_cancel₀ ha
      linear_combination -hu
    refine ⟨A 0 0, k, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · change A 0 0 = A 0 0
      rfl
    · change A 0 1 = -k * c
      exact hb
    · change A 1 0 = k * a
      exact hk.trans (mul_comm a k)
    · change A 1 1 = A 0 0 + k * b
      exact hd
  · rintro ⟨x, k, rfl⟩
    exact primitiveQuadraticFixedMatrix_fixed τ a b c hτ x k

/-- The determinant is the norm of the primitive-quadratic coordinates. -/
theorem primitiveQuadraticFixedMatrix_det (a b c x k : ℤ) :
    (primitiveQuadraticFixedMatrix a b c x k).det =
      x ^ 2 + b * x * k + a * c * k ^ 2 := by
  rw [Matrix.det_fin_two]
  change x * (x + k * b) - (-k * c) * (k * a) =
    x ^ 2 + b * x * k + a * c * k ^ 2
  ring

/-- Common entry divisors are exactly the common divisors of the two norm
coordinates, including for divisor zero and arbitrary coefficient signs. -/
theorem dvd_entries_primitiveQuadraticFixedMatrix_iff (a b c : ℤ)
    (hprim : Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1) (x k d : ℤ) :
    (∀ i j, d ∣ (primitiveQuadraticFixedMatrix a b c x k) i j) ↔
      d ∣ x ∧ d ∣ k := by
  constructor
  · intro h
    have hx : d ∣ x := h 0 0
    have ha : d ∣ k * a := h 1 0
    have hb : d ∣ k * b := by
      have h11 : d ∣ x + k * b := h 1 1
      simpa only [add_sub_cancel_left] using dvd_sub h11 hx
    have hc : d ∣ k * c := by
      have h01 : d ∣ -k * c := h 0 1
      exact dvd_neg.mp (by simpa only [neg_mul] using h01)
    exact ⟨hx, dvd_of_dvd_mul_primitive_coefficients a b c k d hprim ha hb hc⟩
  · rintro ⟨hx, hk⟩ i j
    fin_cases i <;> fin_cases j
    · exact hx
    · change d ∣ -k * c
      exact dvd_mul_of_dvd_left (dvd_neg.mpr hk) c
    · change d ∣ k * a
      exact dvd_mul_of_dvd_left hk a
    · change d ∣ x + k * b
      exact dvd_add hx (dvd_mul_of_dvd_left hk b)

/-- Natural common-entry primitivity is precisely coprimality of the
absolute values of the norm coordinates. -/
theorem primitiveQuadraticFixedMatrix_primitive_iff (a b c : ℤ)
    (hprim : Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1) (x k : ℤ) :
    (∀ d : ℕ,
      (∀ i j, (d : ℤ) ∣ (primitiveQuadraticFixedMatrix a b c x k) i j) → d = 1) ↔
      Nat.Coprime x.natAbs k.natAbs := by
  have hentries (d : ℕ) :
      (∀ i j, (d : ℤ) ∣ (primitiveQuadraticFixedMatrix a b c x k) i j) ↔
        d ∣ Nat.gcd x.natAbs k.natAbs := by
    rw [dvd_entries_primitiveQuadraticFixedMatrix_iff a b c hprim]
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

/-- Primitive integral fixed matrices of any specified integer determinant
are equivalent to primitive norm representations for the actual primitive
quadratic relation of the point. -/
theorem exists_primitive_fixedMatrix_iff_primitiveQuadraticNorm
    (τ : UpperHalfPlane) (a b c : ℤ) (ha : a ≠ 0)
    (hprim : Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0) (n : ℤ) :
    (∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      A.det = n ∧
      (∀ d : ℕ, (∀ i j, (d : ℤ) ∣ A i j) → d = 1) ∧
      (A 0 0 : ℂ) * (τ : ℂ) + A 0 1 =
        (τ : ℂ) * ((A 1 0 : ℂ) * (τ : ℂ) + A 1 1)) ↔
      ∃ x k : ℤ, Nat.Coprime x.natAbs k.natAbs ∧
        x ^ 2 + b * x * k + a * c * k ^ 2 = n := by
  constructor
  · rintro ⟨A, hdet, hprimA, hfix⟩
    obtain ⟨x, k, rfl⟩ :=
      (fixed_iff_eq_primitiveQuadraticFixedMatrix τ a b c ha hprim hτ A).mp hfix
    refine ⟨x, k, (primitiveQuadraticFixedMatrix_primitive_iff a b c hprim x k).mp hprimA,
      ?_⟩
    simpa only [primitiveQuadraticFixedMatrix_det] using hdet
  · rintro ⟨x, k, hcop, hnorm⟩
    exact ⟨primitiveQuadraticFixedMatrix a b c x k,
      (primitiveQuadraticFixedMatrix_det a b c x k).trans hnorm,
      (primitiveQuadraticFixedMatrix_primitive_iff a b c hprim x k).mpr hcop,
      primitiveQuadraticFixedMatrix_fixed τ a b c hτ x k⟩

end BakerHeegnerStark
