/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Natural-number weights separating finite tuples

A natural number can be chosen outside the finitely many roots of the nonzero
pairwise differences of a finite set of polynomials over a characteristic-zero
field. Evaluating at this number therefore distinguishes all distinct polynomials
in the set. Encoding finite tuples as coefficient vectors gives natural-number
power weights that distinguish precisely the distinct tuples, allowing repeated
tuples as well as empty tuples and empty indexing types.
-/

namespace BakerHeegnerStark

open scoped BigOperators

/-- Evaluation at some natural number is injective on any finite set of
polynomials over a characteristic-zero field. -/
theorem exists_nat_eval_injOn {L : Type*} [Field L] [CharZero L]
    {s : Set (Polynomial L)} (hs : s.Finite) :
    ∃ a : ℕ, Set.InjOn (Polynomial.eval (a : L)) s := by
  classical
  let bad : Set L := ⋃ p ∈ s, ⋃ q ∈ s, {x | p ≠ q ∧ (p - q).IsRoot x}
  have hbad : bad.Finite := hs.biUnion fun p _ => hs.biUnion fun q _ => by
    by_cases hpq : p = q
    · simp [hpq]
    · exact (Polynomial.finite_setOfPred_isRoot (sub_ne_zero.mpr hpq)).subset
        (fun _ hx => hx.2)
  obtain ⟨x, ⟨a, rfl⟩, ha⟩ :=
    (Set.infinite_range_of_injective (Nat.cast_injective (R := L))).exists_notMem_finite hbad
  refine ⟨a, ?_⟩
  intro p hp q hq heval
  by_contra hpq
  apply ha
  simp only [bad, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨p, hp, q, hq, hpq, by
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, sub_eq_zero] using heval⟩

/-- A single natural number supplies power weights that distinguish precisely
the distinct tuples in a finite family. The family need not be injective, and
neither the tuple length nor the indexing type is required to be nonempty. -/
theorem exists_nat_weighted_sum_eq_iff {L : Type*} [Field L] [CharZero L]
    {ι : Type*} [Finite ι] (n : ℕ) (v : ι → Fin n → L) :
    ∃ a : ℕ, ∀ i j,
      (∑ k : Fin n, v i k * (a : L) ^ k.val) =
        (∑ k : Fin n, v j k * (a : L) ^ k.val) ↔ v i = v j := by
  classical
  obtain ⟨a, ha⟩ := exists_nat_eval_injOn
    (Set.finite_range (fun i => Polynomial.ofFn n (v i)))
  refine ⟨a, fun i j => ⟨fun hij => ?_, fun hij => by rw [hij]⟩⟩
  apply Polynomial.injective_ofFn n
  apply ha (Set.mem_range_self i) (Set.mem_range_self j)
  simpa only [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial] using hij

end BakerHeegnerStark
