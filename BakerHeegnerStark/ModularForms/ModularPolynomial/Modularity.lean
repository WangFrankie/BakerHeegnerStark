/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.CyclicSublattice.Matrices
import BakerHeegnerStark.ModularForms.CyclicSublattice.Mobius
import BakerHeegnerStark.ModularForms.ModularPolynomial.Complex

/-!
# Modularity of the Actual Cyclic-Sublattice Product

Right special-linear translation permutes the primitive Hermite matrices.
Their actual Mobius actions identify the corresponding j-values, so the
entire root product is invariant. Its already proved holomorphic coefficient
functions and cusp growth then give a bivariate modular polynomial over `ℂ`.
No modular polynomial or CM hypothesis is used. Coefficient integrality and
Galois descent to `ℤ` are proved in `ModularForms/ModularPolynomial/Rationality.lean`.
-/

open Matrix UpperHalfPlane ModularForm Polynomial
open scoped MatrixGroups Polynomial.Bivariate

noncomputable section

namespace BakerHeegnerStark

/-- Every actual primitive Hermite triple at positive level has positive diagonal entries. -/
theorem cyclicSublatticeTriple_pos {N : ℕ} (hN : 0 < N)
    (t : {t // t ∈ cyclicSublatticeTriples N}) : 0 < t.1.1 ∧ 0 < t.1.2.2 := by
  obtain ⟨had, hbd, _⟩ := (mem_cyclicSublatticeTriples hN).mp t.2
  have hd : 0 < t.1.2.2 := by omega
  have ha : 0 < t.1.1 := by
    by_contra h
    have hz : t.1.1 = 0 := by omega
    simp [hz] at had
    omega
  exact ⟨ha, hd⟩

/-- The right permutation matches actual j-values after a modular transform. -/
theorem jInvariant_cyclicSublatticeRightPerm {N : ℕ} (hN : 0 < N)
    (γ : SL(2, ℤ)) (t : {t // t ∈ cyclicSublatticeTriples N}) (τ : UpperHalfPlane) :
    jInvariant (cyclicSublatticePoint (cyclicSublatticeRightPerm hN γ t).1 τ) =
      jInvariant (cyclicSublatticePoint t.1 (γ • τ)) := by
  obtain ⟨haT, hdT⟩ := cyclicSublatticeTriple_pos hN t
  obtain ⟨haU, hdU⟩ := cyclicSublatticeTriple_pos hN (cyclicSublatticeRightPerm hN γ t)
  obtain ⟨κ, hκ⟩ := exists_smul_eq_cyclicSublatticeRightPerm hN γ t
  have hmat := congrArg Subtype.val hκ
  rw [FixedDetMatrices.smul_coe] at hmat
  change (κ : Matrix (Fin 2) (Fin 2) ℤ) *
      ((cyclicSublatticeMatrix t).1 * (γ : Matrix (Fin 2) (Fin 2) ℤ)) =
    (cyclicSublatticeMatrix (cyclicSublatticeRightPerm hN γ t)).1 at hmat
  apply jInvariant_cyclicSublatticePoint_of_matrix_relation t.1
    (cyclicSublatticeRightPerm hN γ t).1 haT hdT haU hdU γ κ ?_ τ
  simpa only [cyclicSublatticeMatrix, Matrix.mul_assoc] using hmat.symm

/-- The actual finite root product is invariant under all of `SL₂(ℤ)`. -/
theorem cyclicSublatticePolynomial_smul {N : ℕ} (hN : 0 < N)
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    cyclicSublatticePolynomial N (γ • τ) = cyclicSublatticePolynomial N τ := by
  classical
  unfold cyclicSublatticePolynomial
  let e := cyclicSublatticeRightPerm hN γ
  refine Finset.prod_bij (fun t ht => (e ⟨t, ht⟩).1) (fun t ht => (e ⟨t, ht⟩).2) ?_ ?_ ?_
  · intro a ha b hb hab
    have heq : e ⟨a, ha⟩ = e ⟨b, hb⟩ := Subtype.ext hab
    exact congrArg Subtype.val (e.injective heq)
  · intro b hb
    refine ⟨(e.symm ⟨b, hb⟩).1, (e.symm ⟨b, hb⟩).2, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
  · intro t ht
    exact congrArg (fun z : ℂ => (X - C z : ℂ[X]))
      (jInvariant_cyclicSublatticeRightPerm hN γ ⟨t, ht⟩ τ).symm

/-- Every actual coefficient function is modular-invariant. -/
theorem cyclicSublatticePolynomial_coeff_smul {N : ℕ} (hN : 0 < N)
    (k : ℕ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    (cyclicSublatticePolynomial N (γ • τ)).coeff k =
      (cyclicSublatticePolynomial N τ).coeff k :=
  congrArg (fun p : ℂ[X] => p.coeff k) (cyclicSublatticePolynomial_smul hN γ τ)

/-- The general modular polynomial exists over `ℂ`, with its actual product
formula, without any modular polynomial or complex multiplication hypothesis.
This does not yet assert coefficients in `ℤ` or the unit diagonal leading term. -/
theorem exists_complex_modularPolynomial {N : ℕ} (hN : 0 < N) :
    ∃ Φ : ℂ[X][Y], ∀ τ : UpperHalfPlane,
      Polynomial.aevalAeval (Polynomial.C (ModularForm.jInvariant τ)) Polynomial.X Φ =
        cyclicSublatticePolynomial N τ :=
  exists_complex_modularPolynomial_of_invariant hN (cyclicSublatticePolynomial_smul hN)

end BakerHeegnerStark
