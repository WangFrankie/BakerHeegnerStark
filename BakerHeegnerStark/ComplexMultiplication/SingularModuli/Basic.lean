/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.Statement
import BakerHeegnerStark.ModularForms.ModularPolynomial.Diagonal
import BakerHeegnerStark.ModularForms.Weber.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Singular Moduli and Weber Class Invariants

This file proves integrality and finite-dimensionality of the actual singular
moduli and states the Weber arithmetic input used by Heegner.
The degree bound is proved in `ComplexMultiplication/SingularModuli/DegreeBound.lean`, using actual
conjugates and QNF's reduced-form/class-group correspondence.
Weber's cube-root rationality is proved in `ComplexMultiplication/Gamma/Rationality.lean`.
`ComplexMultiplication/Weber/ClassInvariant.lean` proves the actual Weber arithmetic input from the
rational joint modular relation and the actual CM torsion action, without
assuming a general CM reciprocity theorem.

* `SingularModulusIntegrality`: `j((1 + √-m)/2)` is an algebraic integer for
  `m ≡ 3 (mod 4)` (part of the first main theorem of complex multiplication;
  Cox, *Primes of the form x² + ny²*, Theorem 11.1). It is **proved unconditionally**
  here from the proved classical modular polynomial theorem, as in Cox §11.
* `SingularModulusDegree`: for squarefree `-m ≡ 1 (mod 4)`, the degree of
  `j((1 + √-m)/2)` over `ℚ` is at most the class number of `ℚ(√-m)`
  (Cox, Theorem 10.23; Silverman, *Advanced Topics in the Arithmetic of
  Elliptic Curves*, Chapter II, §2). Equality holds, but only this bound is used.
  The bound is proved unconditionally in `ComplexMultiplication/SingularModuli/DegreeBound.lean`.
* `GammaTwoRationality`: if `3 ∤ m`, then `γ₂((3 + √-m)/2) ∈ ℚ(j((3 + √-m)/2))`
  (Weber's theorem on `γ₂(τ₀)` for orders with `3 ∤ D`; Cox, §12.A).
  It is proved unconditionally in `ComplexMultiplication/Gamma/Rationality.lean` by rational
  character-twisted modular polynomials and a unique-common-root argument.
* `WeberClassInvariant`: for primes `p ≡ 3 (mod 8)`, `p ≠ 3`, of class number one,
  `𝔣(√-p)² ∈ ℚ(j(√-p))`. This is a special case of Weber's theorem that for
  `m ≡ 3 (mod 4)` and `3 ∤ m`, `𝔣(√-m)²` generates the ring class field of
  `ℤ[√-m]` over `ℚ(√-m)`, together with the reality of `𝔣(√-m)` (Weber,
  *Lehrbuch der Algebra* III; B. J. Birch, *Weber's class invariants*,
  Mathematika 16 (1969); H. M. Stark, 1969; Cox, §12.B–C).
  `ComplexMultiplication/Weber/JointSpecialization.lean` proves the needed inert case directly from
  the rational joint relation and the actual CM torsion action.

The statements and theorem numbers follow the expositions of J. Booher,
*Modular curves and the class number one problem*, and Y. Kezuka, *The class
number problem* (Imperial College MSc thesis), which cite these sources.

No statement here contains the classification or a finite table of class
number one discriminants. `scripts/check_axioms.lean` audits the Weber
application and final classification using only the standard axioms.
-/

open ModularForm IntermediateField QuadraticNumberFields
open scoped NumberField

namespace BakerHeegnerStark

/-- The generator `(1 + √-m)/2` of the maximal order when `-m ≡ 1 (mod 4)`. -/
noncomputable def cmPoint (m : ℕ) : UpperHalfPlane :=
  UpperHalfPlane.ofComplex ((1 + (Real.sqrt m : ℂ) * Complex.I) / 2)

/-- The translate `(3 + √-m)/2` normalizing Weber's cube root `γ₂`. -/
noncomputable def cmPointShift (m : ℕ) : UpperHalfPlane :=
  UpperHalfPlane.ofComplex ((3 + (Real.sqrt m : ℂ) * Complex.I) / 2)

/-- The point `√-m` generating the order `ℤ[√-m]`. -/
noncomputable def sqrtPoint (m : ℕ) : UpperHalfPlane :=
  UpperHalfPlane.ofComplex ((Real.sqrt m : ℂ) * Complex.I)

theorem coe_cmPoint {m : ℕ} (hm : 0 < m) :
    (cmPoint m : ℂ) = (1 + (Real.sqrt m : ℂ) * Complex.I) / 2 := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  exact congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos (by
    simpa using half_pos hs))

theorem coe_cmPointShift {m : ℕ} (hm : 0 < m) :
    (cmPointShift m : ℂ) = (3 + (Real.sqrt m : ℂ) * Complex.I) / 2 := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  exact congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos (by
    simpa using half_pos hs))

theorem coe_sqrtPoint {m : ℕ} (hm : 0 < m) :
    (sqrtPoint m : ℂ) = (Real.sqrt m : ℂ) * Complex.I := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  exact congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos (by
    simpa using hs))

/-- The two normalizations of the maximal-order point have the same `j`. -/
theorem jInvariant_cmPointShift {m : ℕ} (hm : 0 < m) :
    jInvariant (cmPointShift m) = jInvariant (cmPoint m) := by
  have h : cmPointShift m = (1 : ℝ) +ᵥ cmPoint m := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd, coe_cmPointShift hm, coe_cmPoint hm]
    push_cast
    ring
  rw [h, jInvariant_add_one]

/-- Translating `√-m` by one does not change `j`. -/
theorem jInvariant_ofComplex_one_add_sqrt {m : ℕ} (hm : 0 < m) :
    jInvariant (UpperHalfPlane.ofComplex (1 + (Real.sqrt m : ℂ) * Complex.I)) =
      jInvariant (sqrtPoint m) := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have h : UpperHalfPlane.ofComplex (1 + (Real.sqrt m : ℂ) * Complex.I) =
      (1 : ℝ) +ᵥ sqrtPoint m := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd, coe_sqrtPoint hm,
      UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hs)]
    push_cast
    rfl
  rw [h, jInvariant_add_one]

/-- Singular moduli are algebraic integers: `j((1 + √-m)/2)` is integral over `ℤ`
when `m ≡ 3 (mod 4)`. -/
def SingularModulusIntegrality : Prop :=
  ∀ m : ℕ, 0 < m → m % 4 = 3 → IsIntegral ℤ (jInvariant (cmPoint m))

/-- The degree of the singular modulus of the maximal order of `ℚ(√-m)` is at
most its class number, for squarefree `-m ≡ 1 (mod 4)`. -/
def SingularModulusDegree : Prop :=
  ∀ (m : ℕ) [Fact (Squarefree (-(m : ℤ)))] [Fact (-(m : ℤ) ≠ 1)], m % 4 = 3 →
    Module.finrank ℚ ℚ⟮jInvariant (cmPoint m)⟯ ≤
      NumberField.classNumber (Qsqrtd ((-(m : ℤ) : ℤ) : ℚ))

/-- Weber's cube-root theorem: for `3 ∤ m`, the normalized value
`γ₂((3 + √-m)/2)` lies in `ℚ(j((3 + √-m)/2))`. -/
def GammaTwoRationality : Prop :=
  ∀ m : ℕ, 0 < m → m % 4 = 3 → ¬ 3 ∣ m → Squarefree (m : ℤ) →
    gamma₂ (cmPointShift m) ∈ ℚ⟮jInvariant (cmPointShift m)⟯

/-- Weber's class invariant in the inert prime case of class number one:
`𝔣(√-p)²` lies in `ℚ(j(√-p))`. -/
def WeberClassInvariant : Prop :=
  ∀ (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)],
    p.Prime → p % 8 = 3 → p ≠ 3 →
    NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1 →
    weberF ((Real.sqrt p : ℂ) * Complex.I) ^ 2 ∈ ℚ⟮jInvariant (sqrtPoint p)⟯

/-- `(1 + √-m)/2` is a root of `τ² - τ + (m + 1)/4` when `m ≡ 3 (mod 4)`. -/
theorem cmPoint_quadratic {m : ℕ} (hm : 0 < m) (hm4 : m % 4 = 3) :
    (cmPoint m : ℂ) ^ 2 - ((1 : ℤ) : ℂ) * cmPoint m + (((m + 1) / 4 : ℕ) : ℂ) = 0 := by
  have hN : (((m + 1) / 4 : ℕ) : ℂ) * 4 = m + 1 := by
    have : (m + 1) / 4 * 4 = m + 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (by omega))
    exact_mod_cast this
  have hs : ((Real.sqrt m : ℂ) * Complex.I) ^ 2 = -(m : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    push_cast
    ring
  rw [coe_cmPoint hm]
  linear_combination hs / 4 + hN / 4

/-- `(3 + √-m)/2` is a root of `τ² - 3τ + ((m + 1)/4 + 2)` when `m ≡ 3 (mod 4)`. -/
theorem cmPointShift_quadratic {m : ℕ} (hm : 0 < m) (hm4 : m % 4 = 3) :
    (cmPointShift m : ℂ) ^ 2 - ((3 : ℤ) : ℂ) * cmPointShift m +
      (((m + 1) / 4 + 2 : ℕ) : ℂ) = 0 := by
  have hN : (((m + 1) / 4 : ℕ) : ℂ) * 4 = m + 1 := by
    have : (m + 1) / 4 * 4 = m + 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (by omega))
    exact_mod_cast this
  have hs : ((Real.sqrt m : ℂ) * Complex.I) ^ 2 = -(m : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    push_cast
    ring
  rw [coe_cmPointShift hm]
  push_cast
  linear_combination hs / 4 + hN / 4

/-- Two natural numbers differing by two are not both squares. -/
theorem not_isSquare_add_two {n : ℕ} (hn : IsSquare n) : ¬ IsSquare (n + 2) := by
  rintro ⟨s, hs⟩
  obtain ⟨r, rfl⟩ := hn
  have hrs : r < s := by nlinarith
  have hr : r = 0 := by nlinarith
  subst hr
  have hs1 : s ≤ 1 := by nlinarith
  interval_cases s
  omega

/-- **Integrality of singular moduli from modular polynomials** (Cox, §11.C).
Either `(m + 1)/4` or `(m + 1)/4 + 2` is not a square, and the corresponding
normalization of the maximal-order point is a root of a monic integral
quadratic with that constant term. -/
theorem singularModulusIntegrality : SingularModulusIntegrality := by
  intro m hm hm4
  have hN : 0 < (m + 1) / 4 := by omega
  by_cases hsq : IsSquare ((m + 1) / 4)
  · rw [← jInvariant_cmPointShift hm]
    exact isIntegral_jInvariant_of_quadratic modularPolynomialTheorem
      (by omega) (not_isSquare_add_two hsq) (cmPointShift_quadratic hm hm4)
  · exact isIntegral_jInvariant_of_quadratic modularPolynomialTheorem hN hsq
      (cmPoint_quadratic hm hm4)

/-- A positive square and its successor are not both squares. -/
theorem not_isSquare_add_one {n : ℕ} (hn : 0 < n) (hsq : IsSquare n) :
    ¬ IsSquare (n + 1) := by
  rintro ⟨s, hs⟩
  obtain ⟨r, rfl⟩ := hsq
  have hr : 0 < r := by nlinarith
  have hrs : r + 1 ≤ s := by nlinarith
  nlinarith [Nat.mul_le_mul hrs hrs]

/-- The square-root order parameter satisfies its actual integral quadratic. -/
theorem sqrtPoint_quadratic {m : ℕ} (hm : 0 < m) :
    (sqrtPoint m : ℂ) ^ 2 + m = 0 := by
  rw [coe_sqrtPoint hm, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (Nat.cast_nonneg m)]
  push_cast
  ring

/-- The singular modulus of `ℤ[√-m]` is integral for every positive `m`,
without squarefreeness, a class-number hypothesis, or CM reciprocity.
For square `m`, translation by one replaces the norm by the nonsquare `m+1`. -/
theorem isIntegral_jInvariant_sqrtPoint {m : ℕ} (hm : 0 < m) :
    IsIntegral ℤ (jInvariant (sqrtPoint m)) := by
  by_cases hsq : IsSquare m
  · rw [← jInvariant_ofComplex_one_add_sqrt hm]
    apply isIntegral_jInvariant_of_quadratic modularPolynomialTheorem
      (t := 2) (N := m + 1) (by omega) (not_isSquare_add_one hm hsq)
    have hy : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
    have hs := sqrtPoint_quadratic hm
    rw [coe_sqrtPoint hm] at hs
    push_cast
    linear_combination hs
  · exact isIntegral_jInvariant_of_quadratic modularPolynomialTheorem hm hsq
      (t := 0) (by simpa only [Int.cast_zero, zero_mul, sub_zero] using sqrtPoint_quadratic hm)

/-- The maximal-order singular modulus generates a finite extension. The
separate class-number bound is proved in `ComplexMultiplication/SingularModuli/DegreeBound.lean`. -/
theorem finiteDimensional_jInvariant_cmPoint {m : ℕ} (hm : 0 < m) (hm4 : m % 4 = 3) :
    FiniteDimensional ℚ ℚ⟮jInvariant (cmPoint m)⟯ :=
  IntermediateField.adjoin.finiteDimensional
    ((singularModulusIntegrality m hm hm4).tower_top (A := ℚ))

/-- The square-root-order singular modulus generates a finite extension for
every positive parameter, without any CM or class-number hypothesis. -/
theorem finiteDimensional_jInvariant_sqrtPoint {m : ℕ} (hm : 0 < m) :
    FiniteDimensional ℚ ℚ⟮jInvariant (sqrtPoint m)⟯ :=
  IntermediateField.adjoin.finiteDimensional
    ((isIntegral_jInvariant_sqrtPoint hm).tower_top (A := ℚ))

end BakerHeegnerStark
