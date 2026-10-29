/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ClassNumberOne.Classification
import BakerHeegnerStark.ComplexMultiplication.Orders.InertIdealClasses

/-!
# The Conductor-Two Class Polynomial in the Inert Class-Number-One Case

The integral polynomial `Φ₂(j₀, Y)` is monic of degree three for every integer
`j₀`. When `j₀ = j((1+√-p)/2)`, its actual roots are the three level-two CM
values. If `j(√-p)` has degree three over `ℚ`, this polynomial is its minimal
polynomial over `ℚ` and is irreducible there.

The inert class-number-one case follows from the explicit modular/CM
hypotheses used by Heegner's argument. No new CM theorem is assumed, and no
field-degree assertion is inferred merely from the number of ideal classes.
-/

open Polynomial ModularForm IntermediateField QuadraticNumberFields
open scoped Polynomial.Bivariate NumberField

namespace BakerHeegnerStark

/-- The monic integral cubic `Φ₂(j₀, Y)`. It becomes the conductor-two class
polynomial when `j₀` is the maximal-order value in the inert class-number-one case. -/
noncomputable def conductorTwoClassPolynomial (j₀ : ℤ) : ℤ[X] :=
  modularPolynomialTwo.map (evalRingHom j₀)

theorem conductorTwoClassPolynomial_monic (j₀ : ℤ) :
    (conductorTwoClassPolynomial j₀).Monic :=
  modularPolynomialTwo_monic.map _

theorem conductorTwoClassPolynomial_natDegree (j₀ : ℤ) :
    (conductorTwoClassPolynomial j₀).natDegree = 3 := by
  rw [conductorTwoClassPolynomial,
    natDegree_map_eq_of_isUnit_leadingCoeff _
      (by rw [modularPolynomialTwo_monic.leadingCoeff]; exact isUnit_one),
    modularPolynomialTwo_natDegree]

/-- The complex coefficient map agrees with specializing the original
bivariate modular polynomial. -/
theorem conductorTwoClassPolynomial_map_complex (j₀ : ℤ) :
    (conductorTwoClassPolynomial j₀).map (Int.castRingHom ℂ) =
      aevalAeval (C (j₀ : ℂ)) X modularPolynomialTwo := by
  simp [conductorTwoClassPolynomial, modularPolynomialTwo, map_ofNat]

/-- The three actual level-two CM values, with multiplicities, give the full
complex factorization. This needs only the displayed integer `j₀`, not CM reciprocity. -/
theorem conductorTwoClassPolynomial_map_factorization (p : ℕ) (hp : 0 < p)
    (j₀ : ℤ) (hj₀ : jInvariant (cmPoint p) = j₀) :
    (conductorTwoClassPolynomial j₀).map (Int.castRingHom ℂ) =
      (X - C (jInvariant (sqrtPoint p))) *
        (X - C (jInvariant (UpperHalfPlane.ofComplex ((cmPoint p : ℂ) / 2)))) *
        (X - C (jInvariant (UpperHalfPlane.ofComplex (((cmPoint p : ℂ) + 1) / 2)))) := by
  have hdouble : jInvariant (UpperHalfPlane.ofComplex (2 * (cmPoint p : ℂ))) =
      jInvariant (sqrtPoint p) := by
    rw [coe_cmPoint hp, show 2 * ((1 + (Real.sqrt p : ℂ) * Complex.I) / 2) =
      1 + (Real.sqrt p : ℂ) * Complex.I by ring]
    exact jInvariant_ofComplex_one_add_sqrt hp
  rw [conductorTwoClassPolynomial_map_complex, ← hj₀,
    modularPolynomialTwo_jInvariant_factorization_polynomial, hdouble]

/-- The actual `j`-value of the square-root order is a root when `j₀` is the
integer maximal-order value. -/
theorem conductorTwoClassPolynomial_aeval_sqrtPoint (p : ℕ) (hp : 0 < p)
    (j₀ : ℤ) (hj₀ : jInvariant (cmPoint p) = j₀) :
    aeval (jInvariant (sqrtPoint p)) (conductorTwoClassPolynomial j₀) = 0 := by
  change eval₂ (Int.castRingHom ℂ) (jInvariant (sqrtPoint p)) (conductorTwoClassPolynomial j₀) = 0
  have h := congrArg (eval (jInvariant (sqrtPoint p)))
    (conductorTwoClassPolynomial_map_factorization p hp j₀ hj₀)
  simpa only [eval_map, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] using h

/-- The actual degree-three CM value has the level-two integral cubic as its
minimal polynomial over `ℚ`. The degree is an explicit mathematical hypothesis. -/
theorem conductorTwoClassPolynomial_eq_minpoly (p : ℕ) (hp : 0 < p)
    (j₀ : ℤ) (hj₀ : jInvariant (cmPoint p) = j₀)
    (hdegree : Module.finrank ℚ ℚ⟮jInvariant (sqrtPoint p)⟯ = 3) :
    (conductorTwoClassPolynomial j₀).map (algebraMap ℤ ℚ) =
      minpoly ℚ (jInvariant (sqrtPoint p)) := by
  let P := (conductorTwoClassPolynomial j₀).map (algebraMap ℤ ℚ)
  have hmonic : P.Monic := (conductorTwoClassPolynomial_monic j₀).map _
  have hroot : aeval (jInvariant (sqrtPoint p)) P = 0 := by
    dsimp only [P]
    rw [aeval_map_algebraMap]
    exact conductorTwoClassPolynomial_aeval_sqrtPoint p hp j₀ hj₀
  have ht : IsIntegral ℚ (jInvariant (sqrtPoint p)) :=
    ⟨P, hmonic, by rwa [← aeval_def]⟩
  have hPdeg : P.natDegree = 3 := by
    dsimp only [P]
    rw [natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
      conductorTwoClassPolynomial_natDegree]
  have hminDegree : (minpoly ℚ (jInvariant (sqrtPoint p))).natDegree = 3 :=
    (IntermediateField.adjoin.finrank ht).symm.trans hdegree
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ht) hmonic
    (minpoly.dvd ℚ _ hroot) (le_of_eq (hPdeg.trans hminDegree.symm))

/-- Irreducibility holds over `ℤ`, not just after adjoining complex coefficients. -/
theorem conductorTwoClassPolynomial_irreducible (p : ℕ) (hp : 0 < p)
    (j₀ : ℤ) (hj₀ : jInvariant (cmPoint p) = j₀)
    (hdegree : Module.finrank ℚ ℚ⟮jInvariant (sqrtPoint p)⟯ = 3) :
    Irreducible (conductorTwoClassPolynomial j₀) := by
  apply ((conductorTwoClassPolynomial_monic j₀).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mpr
  rw [conductorTwoClassPolynomial_eq_minpoly p hp j₀ hj₀ hdegree]
  have ht := (jInvariant_sqrtPoint_isIntegral_finrank_le p hp (j₀ : ℚ)
    (by simpa only [Rat.cast_intCast] using hj₀)).1
  exact minpoly.irreducible ht

/-- In the nonexceptional inert class-number-one family, the actual conductor-two
CM point has an irreducible monic integer cubic obtained by specializing `Φ₂`
at the integer maximal-order value. No Weber class-invariant hypothesis is used. -/
theorem exists_conductorTwoClassPolynomial
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)] (hp : p.Prime)
    (hp8 : p % 8 = 3) (hp3 : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1) :
    ∃ j₀ : ℤ, jInvariant (cmPoint p) = j₀ ∧
      Irreducible (conductorTwoClassPolynomial j₀) ∧
      (conductorTwoClassPolynomial j₀).map (algebraMap ℤ ℚ) =
        minpoly ℚ (jInvariant (sqrtPoint p)) := by
  obtain ⟨n, hn⟩ := gamma₂_cmPointShift_eq_intCast p hp hp8 hp3 hclass
  have hj₀ : jInvariant (cmPoint p) = ((n ^ 3 : ℤ) : ℂ) := by
    rw [← jInvariant_cmPointShift hp.pos, ← gamma₂_cube, hn]
    push_cast
    rfl
  have hdegree := jInvariant_sqrtPoint_finrank_eq_three p hp hp8 hp3 hclass
  exact ⟨n ^ 3, hj₀, conductorTwoClassPolynomial_irreducible p hp.pos _ hj₀ hdegree,
    conductorTwoClassPolynomial_eq_minpoly p hp.pos _ hj₀ hdegree⟩

/-- For this inert class-number-one family, the actual order class-group
cardinality equals the degree of the actual singular modulus. Both sides are
proved to be three independently: by ideal exhaustion and by Heegner's cubic.
No Weber class-invariant hypothesis or general CM degree axiom is used. -/
theorem sqrtOrderClassGroup_card_eq_jInvariant_finrank
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)]
    [Fact (-(p : ℤ) < 0)] (hp : p.Prime) (hp8 : p % 8 = 3) (hp3 : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1) :
    Nat.card (ClassGroup (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) =
      Module.finrank ℚ ℚ⟮jInvariant (sqrtPoint p)⟯ := by
  exact (inert_sqrtOrderClassGroup_card p hp8 (by have := hp.two_le; omega) hclass).trans
    (jInvariant_sqrtPoint_finrank_eq_three p hp hp8 hp3 hclass).symm

end BakerHeegnerStark
