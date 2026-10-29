/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.Coefficients
import BakerHeegnerStark.ModularForms.JInvariant.Polynomial
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Complex Modular Polynomials from Invariance

The actual cyclic-sublattice root product has holomorphic coefficient functions
with polynomial growth in `j`. Assuming invariance of this product under
`SL₂(ℤ)`, each coefficient is therefore a polynomial in `j`. Their finite sum
constructs a bivariate polynomial over `ℂ` with the required product formula.
This does not assert integrality of its coefficients or Galois descent.
-/

open UpperHalfPlane ModularForm Polynomial Asymptotics
open scoped MatrixGroups Manifold Polynomial.Bivariate

noncomputable section

namespace BakerHeegnerStark

/-- The actual cyclic-sublattice root product is monic, including at level zero. -/
theorem monic_cyclicSublatticePolynomial (N : ℕ) (τ : UpperHalfPlane) :
    (cyclicSublatticePolynomial N τ).Monic := by
  classical
  exact monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- The degree of the actual root product counts cyclic sublattices, with
multiplicity; distinctness of their j-values is not required. -/
theorem natDegree_cyclicSublatticePolynomial (N : ℕ) (τ : UpperHalfPlane) :
    (cyclicSublatticePolynomial N τ).natDegree = (cyclicSublatticeTriples N).card := by
  classical
  unfold cyclicSublatticePolynomial
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp

/-- A polynomial-valued modular function with holomorphic, polynomially bounded
coefficients is a bivariate polynomial in the actual j-value. -/
theorem exists_bivariate_polynomial_jInvariant_of_isBigO
    (F : UpperHalfPlane → ℂ[X]) (d n : ℕ)
    (hdegree : ∀ τ, (F τ).natDegree = d)
    (hholo : ∀ k, MDiff (fun τ => (F τ).coeff k))
    (hgrowth : ∀ k, (fun τ => (F τ).coeff k)
      =O[atImInfty] (fun τ => jInvariant τ ^ n))
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (γ • τ) = F τ) :
    ∃ Φ : ℂ[X][Y], ∀ τ : UpperHalfPlane,
      aevalAeval (C (jInvariant τ)) X Φ = F τ := by
  classical
  have hcoeff (k : ℕ) : ∃ P : ℂ[X], ∀ τ : UpperHalfPlane,
      (F τ).coeff k = P.eval (jInvariant τ) := by
    let φ : SlashInvariantForm 𝒮ℒ 0 :=
      { toFun := fun τ => (F τ).coeff k
        slash_action_eq' := by
          intro γ hγ
          obtain ⟨γ, rfl⟩ := hγ
          change ((fun τ => (F τ).coeff k) ∣[(0 : ℤ)] γ) =
            (fun τ => (F τ).coeff k)
          funext τ
          simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using
            congrArg (fun p : ℂ[X] => p.coeff k) (hinv γ τ) }
    obtain ⟨P, _, hP⟩ := exists_polynomial_jInvariant_of_isBigO φ
      (hholo k) n (hgrowth k)
    exact ⟨P, hP⟩
  choose P hP using hcoeff
  refine ⟨∑ k ∈ Finset.range (d + 1), C (P k) * X ^ k, fun τ => ?_⟩
  simp only [map_sum, map_mul, map_pow, aevalAeval_C, aevalAeval_Y]
  rw [(F τ).as_sum_range_C_mul_X_pow, hdegree]
  apply Finset.sum_congr rfl
  intro k _
  change (P k).eval₂ C (C (jInvariant τ)) * X ^ k = _
  rw [eval₂_at_apply, ← hP k τ]

/-- Invariance, together with the proved holomorphicity and cusp growth of the
actual coefficients, constructs a complex bivariate polynomial realizing the
entire cyclic-sublattice product at every upper-half-plane point. -/
theorem exists_complex_modularPolynomial_of_invariant {N : ℕ} (hN : 0 < N)
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane),
      cyclicSublatticePolynomial N (γ • τ) = cyclicSublatticePolynomial N τ) :
    ∃ Φ : ℂ[X][Y], ∀ τ : UpperHalfPlane,
      Polynomial.aevalAeval (Polynomial.C (ModularForm.jInvariant τ)) Polynomial.X Φ =
        cyclicSublatticePolynomial N τ :=
  exists_bivariate_polynomial_jInvariant_of_isBigO (cyclicSublatticePolynomial N)
    (cyclicSublatticeTriples N).card (N * (cyclicSublatticeTriples N).card)
    (natDegree_cyclicSublatticePolynomial N)
    (mdifferentiable_cyclicSublatticePolynomial_coeff hN)
    (isBigO_cyclicSublatticePolynomial_coeff hN) hinv

end BakerHeegnerStark
