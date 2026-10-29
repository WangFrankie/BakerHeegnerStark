/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Separable

/-!
# Counting distinct algebraic conjugates

A finite set containing every complex root of a minimal polynomial over a
characteristic-zero field bounds the degree of the corresponding simple field extension. Separability in
characteristic zero and splitting over the complex numbers identify that degree
with the cardinality of the set of distinct roots.
-/

namespace BakerHeegnerStark

open IntermediateField

/-- The degree of an algebraic complex number over a characteristic-zero field
is bounded by the size of any finite set containing all roots of its minimal polynomial. -/
theorem finrank_adjoin_le_card_of_minpoly_roots_subset
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ] (z : ℂ) (hz : IsIntegral K z)
    (s : Finset ℂ)
    (hs : ∀ x : ℂ, Polynomial.aeval x (minpoly K z) = 0 → x ∈ s) :
    Module.finrank K K⟮z⟯ ≤ s.card := by
  classical
  have hsep : (minpoly K z).Separable := (minpoly.irreducible hz).separable
  have hsplit : ((minpoly K z).map (algebraMap K ℂ)).Splits :=
    IsAlgClosed.splits _
  let f : (minpoly K z).rootSet ℂ → {x : ℂ // x ∈ s} := fun x =>
    ⟨x.1, hs x.1 (Polynomial.aeval_eq_zero_of_mem_rootSet x.2)⟩
  have hf : Function.Injective f := by
    intro x y h
    have hval := congrArg (fun t : {x : ℂ // x ∈ s} => t.val) h
    change x.val = y.val at hval
    exact Subtype.ext hval
  calc
    Module.finrank K K⟮z⟯ = (minpoly K z).natDegree :=
      IntermediateField.adjoin.finrank hz
    _ = Fintype.card ((minpoly K z).rootSet ℂ) :=
      (Polynomial.card_rootSet_eq_natDegree hsep hsplit).symm
    _ ≤ s.card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

end BakerHeegnerStark
