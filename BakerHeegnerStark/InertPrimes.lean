/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.Statement
import BakerHeegnerStark.IdealReductions
import QuadraticNumberFields.ClassGroup.GenusTheory.Sieve

/-!
# Reduction to Non-Exceptional Inert Primes

Genus theory reduces the problem to prime parameters. The split-at-two case
gives `-7`, and the exceptional prime `3` is already known. Consequently the
full classification is equivalent to its restriction to primes `p ≡ 3 (mod 8)`,
`p ≠ 3`. This reduction uses the local ideal-theoretic proofs and the genus
sieve from QuadraticNumberFields.

The two elementary branch theorems below are extracted from
`ImaginaryClassNumberOne/StarkHeegner.lean` at QNF commit
`196dd48b3439cc731397fd2cf9b8ac48da211a22`, retaining their original proofs.
-/

open QuadraticNumberFields
open scoped NumberField

namespace BakerHeegnerStark

/-- In the non-half-integral branch, ramification at `2` leaves only `-1` or `-2`. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd4 : d % 4 ≠ 1)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  rcases eq_neg_one_or_eq_neg_two_of_classNumber_eq_one_of_mod_four_ne_one
      d hd hd4 h with rfl | rfl <;>
    simp [heegnerSet]

/-- In the split half-integral branch, the norm obstruction at `2` leaves only `-7`. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd8 : d % 8 = 1)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  have hd_eq : d = -7 :=
    eq_neg_seven_of_classNumber_eq_one_of_mod_eight_eq_one d hd hd8 h
  rw [hd_eq]
  simp [heegnerSet]

/-- The remaining class-number-one classification for primes inert at `2`,
after treating the exceptional prime `3`. This proposition is not yet proved. -/
def InertPrimeClassification : Prop :=
  ∀ (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)],
    p.Prime → p % 8 = 3 → p ≠ 3 →
    NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1 →
    -(p : ℤ) ∈ heegnerSet

/-- Class number one either gives a known Heegner number or a non-exceptional
prime parameter inert at `2`. -/
theorem mem_heegnerSet_or_inert_prime
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet ∨ ∃ p : ℕ, p.Prime ∧ p % 8 = 3 ∧ p ≠ 3 ∧ d = -(p : ℤ) := by
  rcases ClassGroup.GenusTheory.classNumber_eq_one_imp_parameter_prime_shape d hd hclass with
    rfl | rfl | ⟨p, hp, hp4, hdp⟩
  · exact Or.inl (by norm_num [heegnerSet])
  · exact Or.inl (by norm_num [heegnerSet])
  · have hp8 : p % 8 = 3 ∨ p % 8 = 7 := by omega
    rcases hp8 with hp8 | hp8
    · by_cases hp3 : p = 3
      · exact Or.inl (by simp [hdp, hp3, heegnerSet])
      · exact Or.inr ⟨p, hp, hp8, hp3, hdp⟩
    · have hd8 : d % 8 = 1 := by
        rw [hdp]
        omega
      have hd7 := eq_neg_seven_of_classNumber_eq_one_of_mod_eight_eq_one d hd hd8 hclass
      exact Or.inl (by simp [hd7, heegnerSet])

/-- The complete Baker-Heegner-Stark classification is equivalent to the
remaining non-exceptional inert prime case. Neither side is assumed proved. -/
theorem classNumberOneClassification_iff_inertPrimeClassification :
    ClassNumberOneClassification ↔ InertPrimeClassification := by
  constructor
  · intro h p _ _ hp _ _ hclass
    have hneg : -(p : ℤ) < 0 := by
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
    exact (h (-(p : ℤ)) hneg).mp hclass
  · intro h d _ _ hd
    constructor
    · intro hclass
      rcases mem_heegnerSet_or_inert_prime d hd hclass with hmem | ⟨p, hp, hp8, hp3, hdp⟩
      · exact hmem
      · subst d
        exact h p hp hp8 hp3 hclass
    · exact classNumber_eq_one_of_mem_heegnerSet

end BakerHeegnerStark
