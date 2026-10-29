/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.SingularModuli.Discriminant
import BakerHeegnerStark.ComplexMultiplication.SingularModuli.ReducedForms
import BakerHeegnerStark.FieldTheory.AlgebraicConjugates
import FormClassGroup.ClassGroup.ClassNumber

/-!
# The Class-Number Bound for the Degree of the Singular Modulus

All actual algebraic conjugates have the original primitive CM discriminant.
QNF's existing proper reduction puts their j-values in its finite reduced-form
image. Counting distinct conjugates gives the degree bound, and QNF's proved
maximal-order class-group/reduced-form correspondence identifies the bound with
the field class number. No CM reciprocity placeholder is used.

The binary quadratic forms and class-group correspondence remain in QNF; only
the connection to the actual analytic singular modulus is proved here.
-/

open ModularForm IntermediateField QuadraticNumberFields
open scoped NumberField

namespace BakerHeegnerStark

/-- Every root of the actual CM minimal polynomial is an actual j-value of an
existing QNF reduced form of the original discriminant. -/
theorem minpoly_cmPoint_root_mem_reducedFormJValues {m : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) {x : ℂ}
    (hx : Polynomial.aeval x (minpoly ℚ (jInvariant (cmPoint m))) = 0) :
    x ∈ reducedFormJValues (-(m : ℤ)) := by
  obtain ⟨τ, hτ, _, a, b, c, ha, hprim, hdisc, hquad⟩ :=
    exists_cmPoint_conjugate_primitive_discriminant hm hm4 hx
  rw [← hτ]
  exact jInvariant_mem_reducedFormJValues τ a b c ha hprim hdisc hquad

/-- Counting the distinct algebraic conjugates bounds the actual generated-field
degree by the reduced-form enumeration, without a squarefreeness hypothesis. -/
theorem jInvariant_cmPoint_finrank_le_reducedForms_card {m : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) :
    Module.finrank ℚ ℚ⟮jInvariant (cmPoint m)⟯ ≤
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(m : ℤ))).card := by
  have hbound := finrank_adjoin_le_card_of_minpoly_roots_subset (jInvariant (cmPoint m))
    ((singularModulusIntegrality m hm hm4).tower_top (A := ℚ))
    (reducedFormJValues (-(m : ℤ)))
    (fun _ hx => minpoly_cmPoint_root_mem_reducedFormJValues hm hm4 hx)
  exact hbound.trans (card_reducedFormJValues_le _)

/-- For the maximal order, QNF's actual class-number/reduced-form correspondence
gives the classical degree bound for the analytic singular modulus. -/
theorem jInvariant_cmPoint_finrank_le_classNumber
    (m : ℕ) [Fact (Squarefree (-(m : ℤ)))] [Fact (-(m : ℤ) ≠ 1)]
    (hm4 : m % 4 = 3) :
    Module.finrank ℚ ℚ⟮jInvariant (cmPoint m)⟯ ≤
      NumberField.classNumber (Qsqrtd ((-(m : ℤ) : ℤ) : ℚ)) := by
  have hm : 0 < m := by omega
  have hcard := classNumber_qsqrtd_eq_reducedForms_card (-(m : ℤ)) (by omega)
  rw [BinaryQuadraticForm.fieldDiscriminant_of_mod_four_eq_one (by omega)] at hcard
  exact (jInvariant_cmPoint_finrank_le_reducedForms_card hm hm4).trans_eq hcard.symm

/-- The classical singular-modulus degree bound (Cox, Theorem 10.23), proved
from actual modular equations, primitive discriminants, and reduced forms. -/
theorem singularModulusDegree : SingularModulusDegree :=
  jInvariant_cmPoint_finrank_le_classNumber

/-- Class number one makes the actual maximal-order j-generated field rational. -/
theorem jInvariant_cmPoint_adjoin_eq_bot_of_classNumber_eq_one
    (m : ℕ) [Fact (Squarefree (-(m : ℤ)))] [Fact (-(m : ℤ) ≠ 1)]
    (hm4 : m % 4 = 3)
    (hclass : NumberField.classNumber (Qsqrtd ((-(m : ℤ) : ℤ) : ℚ)) = 1) :
    ℚ⟮jInvariant (cmPoint m)⟯ = ⊥ := by
  have hm : 0 < m := by omega
  have : FiniteDimensional ℚ ℚ⟮jInvariant (cmPoint m)⟯ :=
    finiteDimensional_jInvariant_cmPoint hm hm4
  have hpos : 0 < Module.finrank ℚ ℚ⟮jInvariant (cmPoint m)⟯ := Module.finrank_pos
  have hle := singularModulusDegree m hm4
  rw [hclass] at hle
  rw [← IntermediateField.finrank_eq_one_iff]
  omega

/-- Under class number one, the actual maximal-order singular modulus is a
rational integer, without assuming Weber's class invariant or CM reciprocity. -/
theorem jInvariant_cmPoint_eq_intCast_of_classNumber_eq_one
    (m : ℕ) [Fact (Squarefree (-(m : ℤ)))] [Fact (-(m : ℤ) ≠ 1)]
    (hm4 : m % 4 = 3)
    (hclass : NumberField.classNumber (Qsqrtd ((-(m : ℤ) : ℤ) : ℚ)) = 1) :
    ∃ n : ℤ, jInvariant (cmPoint m) = n := by
  have hmem : jInvariant (cmPoint m) ∈ (⊥ : IntermediateField ℚ ℂ) := by
    rw [← jInvariant_cmPoint_adjoin_eq_bot_of_classNumber_eq_one m hm4 hclass]
    exact IntermediateField.mem_adjoin_simple_self ℚ _
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hmem
  have hint := singularModulusIntegrality m (by omega) hm4
  rw [← hq] at hint
  have hqint : IsIntegral ℤ q := isIntegral_algebraMap_iff.mp hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
  refine ⟨n, ?_⟩
  rw [← hq, ← hn]
  simp

end BakerHeegnerStark
