/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Separable

/-!
# Counting distinct algebraic conjugates

A finite set containing every root of a separable minimal polynomial in a
splitting field bounds the degree of the corresponding simple field extension.
Separability and splitting identify that degree with the cardinality of the
set of distinct roots. Both hypotheses are explicit, so the result applies over
arbitrary fields without asserting the same bound for inseparable polynomials.
-/

namespace BakerHeegnerStark

open IntermediateField

/-- If a minimal polynomial is separable and splits in the ambient field, the
degree of the generated simple extension is bounded by the size of any finite
set containing all of its roots. -/
theorem finrank_adjoin_le_card_of_minpoly_roots_subset
    {K L : Type*} [Field K] [Field L] [Algebra K L] (z : L) (hz : IsIntegral K z)
    (hsep : (minpoly K z).Separable)
    (hsplit : ((minpoly K z).map (algebraMap K L)).Splits)
    (s : Finset L)
    (hs : ∀ x : L, Polynomial.aeval x (minpoly K z) = 0 → x ∈ s) :
    Module.finrank K K⟮z⟯ ≤ s.card := by
  classical
  let f : (minpoly K z).rootSet L → {x : L // x ∈ s} := fun x =>
    ⟨x.1, hs x.1 (Polynomial.aeval_eq_zero_of_mem_rootSet x.2)⟩
  have hf : Function.Injective f := by
    intro x y h
    have hval := congrArg (fun t : {x : L // x ∈ s} => t.val) h
    change x.val = y.val at hval
    exact Subtype.ext hval
  calc
    Module.finrank K K⟮z⟯ = (minpoly K z).natDegree :=
      IntermediateField.adjoin.finrank hz
    _ = Fintype.card ((minpoly K z).rootSet L) :=
      (Polynomial.card_rootSet_eq_natDegree hsep hsplit).symm
    _ ≤ s.card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

end BakerHeegnerStark
