/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.Diagonal

/-!
# Monicity of the Actual Integral Modular Polynomial

The cusp leading term makes polynomial evaluation at the actual j-function
injective. Consequently the monicity and degree of the analytic root product
recover the monicity and degree of its integral bivariate polynomial.
-/

open UpperHalfPlane ModularForm Polynomial Filter
open scoped Polynomial.Bivariate Topology

noncomputable section

namespace BakerHeegnerStark

/-- A complex polynomial vanishing on every actual j-value is zero. -/
theorem polynomial_eq_zero_of_eval_jInvariant_eq_zero (P : ℂ[X])
    (hP : ∀ τ : UpperHalfPlane, P.eval (jInvariant τ) = 0) : P = 0 := by
  have hlim := tendsto_qParam_natDegree_mul_polynomial_jInvariant (N := 1) (by decide) P
  have hzero : Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam ((1 : ℕ) : ℝ) (τ : ℂ) ^ (1 * P.natDegree) * P.eval (jInvariant τ))
      atImInfty (𝓝 0) := by
    simpa only [hP, mul_zero] using (tendsto_const_nhds : Tendsto
      (fun _ : UpperHalfPlane => (0 : ℂ)) atImInfty (𝓝 0))
  exact Polynomial.leadingCoeff_eq_zero.mp (tendsto_nhds_unique hlim hzero)

/-- Integer polynomial evaluation on all j-values also detects zero. -/
theorem polynomial_eq_zero_of_aeval_jInvariant_eq_zero (P : ℤ[X])
    (hP : ∀ τ : UpperHalfPlane, aeval (jInvariant τ) P = 0) : P = 0 := by
  have hbase : Int.castRingHom ℂ = algebraMap ℤ ℂ := RingHom.ext_int _ _
  apply (Polynomial.map_eq_zero_iff (f := Int.castRingHom ℂ) Int.cast_injective).mp
  apply polynomial_eq_zero_of_eval_jInvariant_eq_zero
  intro τ
  simpa only [Polynomial.eval_map, hbase, Polynomial.aeval_def] using hP τ

/-- Substituting the first variable alone is coefficientwise evaluation. -/
theorem aevalAeval_C_X_eq_map (Φ : ℤ[X][Y]) (z : ℂ) :
    aevalAeval (C z) X Φ = Φ.map (aeval z).toRingHom := by
  have hh : (aevalAeval (C z) X : ℤ[X][Y] →ₐ[ℤ] ℂ[X]).toRingHom =
      Polynomial.mapRingHom (aeval z).toRingHom := by
    ext <;> simp
  exact congrArg (fun f : ℤ[X][Y] →+* ℂ[X] => f Φ) hh

/-- The actual product formula determines both monicity in the second variable
and the exact degree, without a distinctness assumption on the roots. -/
theorem monic_natDegree_of_modularPolynomial_product {N : ℕ} (Φ : ℤ[X][Y])
    (hΦ : ∀ τ : UpperHalfPlane,
      aevalAeval (C (jInvariant τ)) X Φ = cyclicSublatticePolynomial N τ) :
    Φ.Monic ∧ Φ.natDegree = (cyclicSublatticeTriples N).card := by
  have hcoeff (k : ℕ) (τ : UpperHalfPlane) :
      aeval (jInvariant τ) (Φ.coeff k) = (cyclicSublatticePolynomial N τ).coeff k := by
    have h := congrArg (fun p : ℂ[X] => p.coeff k) (hΦ τ)
    rw [aevalAeval_C_X_eq_map, Polynomial.coeff_map] at h
    exact h
  have hdeg : Φ.natDegree ≤ (cyclicSublatticeTriples N).card := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    apply polynomial_eq_zero_of_aeval_jInvariant_eq_zero
    intro τ
    rw [hcoeff]
    exact coeff_eq_zero_of_natDegree_lt ((natDegree_cyclicSublatticePolynomial N τ).trans_lt hk)
  have hone : Φ.coeff (cyclicSublatticeTriples N).card = 1 := by
    apply sub_eq_zero.mp
    apply polynomial_eq_zero_of_aeval_jInvariant_eq_zero
    intro τ
    rw [map_sub, map_one, hcoeff, ← natDegree_cyclicSublatticePolynomial N τ,
      (monic_cyclicSublatticePolynomial N τ).coeff_natDegree, sub_self]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one _ hdeg hone,
    natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hone]; exact one_ne_zero)⟩

/-- Every positive level has a monic integral modular polynomial of the exact
cyclic-sublattice degree, with the actual product formula and the nonsquare
diagonal unit property. -/
theorem exists_monic_integer_modularPolynomial {N : ℕ} (hN : 0 < N) :
    ∃ Φ : ℤ[X][Y], Φ.Monic ∧ Φ.natDegree = (cyclicSublatticeTriples N).card ∧
      (∀ τ : UpperHalfPlane,
        aevalAeval (C (jInvariant τ)) X Φ = cyclicSublatticePolynomial N τ) ∧
      (¬ IsSquare N → IsUnit (aevalAeval (X : ℤ[X]) X Φ).leadingCoeff) := by
  obtain ⟨Φ, hΦ, hunit⟩ := modularPolynomialTheorem N hN
  obtain ⟨hmonic, hdegree⟩ := monic_natDegree_of_modularPolynomial_product Φ hΦ
  exact ⟨Φ, hmonic, hdegree, hΦ, hunit⟩

end BakerHeegnerStark
