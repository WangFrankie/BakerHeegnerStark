/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Joint finite-orbit polynomials and simultaneous root matching

An auxiliary polynomial variable records two values as one linear polynomial.
A root of their finite product therefore matches both values at the same index,
not merely two independently conjugate marginal values. The construction allows
repeated pairs and empty finite index types. Reindexing and coefficient maps
respect the actual product, so fixed joint coefficients imply simultaneous
conjugate matching by finite polynomial algebra alone. No passage of a field
automorphism through an infinite analytic sum is used or assumed.
-/

open Polynomial
open scoped BigOperators

noncomputable section
namespace BakerHeegnerStark

/-- The auxiliary variable keeps two values separate in one polynomial root. -/
def jointOrbitLinearPolynomial {L : Type*} [CommRing L] (x y : L) : L[X] :=
  C x + C y * X

/-- Equality of these roots determines both values, over any commutative ring. -/
theorem jointOrbitLinearPolynomial_eq_iff {L : Type*} [CommRing L] (x y v w : L) :
    jointOrbitLinearPolynomial x y = jointOrbitLinearPolynomial v w ↔ x = v ∧ y = w := by
  constructor
  · intro h
    exact ⟨by simpa [jointOrbitLinearPolynomial] using congrArg (fun p : L[X] => p.coeff 0) h,
      by simpa [jointOrbitLinearPolynomial] using congrArg (fun p : L[X] => p.coeff 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A joint finite-orbit polynomial, with coefficients polynomial in the
auxiliary variable and a separate outer root variable. Repeated pairs are allowed. -/
def jointOrbitPolynomial {ι L : Type*} [Fintype ι] [CommRing L] (v w : ι → L) : L[X][X] :=
  ∏ i, (X - C (jointOrbitLinearPolynomial (v i) (w i)))

theorem monic_jointOrbitPolynomial {ι L : Type*} [Fintype ι] [CommRing L] (v w : ι → L) :
    (jointOrbitPolynomial v w).Monic := by
  classical
  exact monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_jointOrbitPolynomial {ι L : Type*} [Fintype ι] [CommRing L] [Nontrivial L]
    (v w : ι → L) : (jointOrbitPolynomial v w).natDegree = Fintype.card ι := by
  classical
  unfold jointOrbitPolynomial
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp

/-- A joint root matches both coordinates at one and the same index.
The empty index set has polynomial one and no roots. -/
theorem isRoot_jointOrbitPolynomial_iff {ι L : Type*} [Fintype ι] [CommRing L] [IsDomain L]
    (v w : ι → L) (x y : L) :
    (jointOrbitPolynomial v w).IsRoot (jointOrbitLinearPolynomial x y) ↔
      ∃ i, x = v i ∧ y = w i := by
  classical
  simp [Polynomial.IsRoot, jointOrbitPolynomial, eval_prod,
    Finset.prod_eq_zero_iff, sub_eq_zero, jointOrbitLinearPolynomial_eq_iff]

/-- Simultaneous reindexing leaves the actual joint product unchanged. -/
theorem jointOrbitPolynomial_reindex {ι κ L : Type*} [Fintype ι] [Fintype κ] [CommRing L]
    (e : ι ≃ κ) (v w : κ → L) :
    jointOrbitPolynomial (v ∘ e) (w ∘ e) = jointOrbitPolynomial v w := by
  classical
  exact e.prod_comp (fun i => X - C (jointOrbitLinearPolynomial (v i) (w i)))

/-- Coefficient maps act on both values without evaluating the auxiliary variable. -/
theorem jointOrbitPolynomial_map {ι L M : Type*} [Fintype ι] [CommRing L] [CommRing M]
    (f : L →+* M) (v w : ι → L) :
    (jointOrbitPolynomial v w).map (Polynomial.mapRingHom f) =
      jointOrbitPolynomial (f ∘ v) (f ∘ w) := by
  classical
  simp [jointOrbitPolynomial, jointOrbitLinearPolynomial, Polynomial.map_prod]

/-- Fixed joint coefficients produce one index matching the two conjugated
values simultaneously, not two unrelated marginal roots. -/
theorem exists_jointOrbit_pair_of_map_eq {ι L : Type*} [Fintype ι] [CommRing L] [IsDomain L]
    (f : L →+* L) (v w : ι → L)
    (hfix : (jointOrbitPolynomial v w).map (Polynomial.mapRingHom f) = jointOrbitPolynomial v w)
    (i : ι) : ∃ j, f (v i) = v j ∧ f (w i) = w j := by
  have hr : (jointOrbitPolynomial (f ∘ v) (f ∘ w)).IsRoot
      (jointOrbitLinearPolynomial (f (v i)) (f (w i))) :=
    (isRoot_jointOrbitPolynomial_iff _ _ _ _).mpr ⟨i, rfl, rfl⟩
  rw [← jointOrbitPolynomial_map f v w, hfix] at hr
  exact (isRoot_jointOrbitPolynomial_iff _ _ _ _).mp hr

end BakerHeegnerStark
