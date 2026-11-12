/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Weber.JointQExpansion

/-!
# Rational trivariate representation of the actual joint polynomial

The entire paired q-product is defined over the actual finite Galois phase
field and is fixed under its actual automorphisms. The shared finite-Galois
q-regularization descent theorem transfers this width-24 formal fixedness to
every bounded-degree coefficient polynomial in `j`, giving a rational
trivariate polynomial without specializing the tuple-separating variable.
-/

open UpperHalfPlane Polynomial BakerHeegnerStark

noncomputable section
namespace ModularForm

/-- Every bounded-degree polynomial representing an actual scalar joint
coefficient descends to `ℚ`, using its full fixed cyclotomic series. -/
theorem exists_rational_polynomial_weberJointPolynomial_repr
    (a k l : ℕ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ 8 * Fintype.card weberJointIndex)
    (hrep : ∀ τ : UpperHalfPlane,
      ((weberJointPolynomial a τ).coeff k).coeff l = P.eval (jInvariant τ)) :
    ∃ Q : ℚ[X], Q.map (algebraMap ℚ ℂ) = P := by
  let K := weberBranchCoefficientField
  let f : K →+* ℂ := algebraMap K ℂ
  let n := 8 * Fintype.card weberJointIndex
  let J : PowerSeries K := PowerSeries.expand 24 (by decide)
    (PowerSeries.map (Int.castRingHom K) jInvariantIntegralNumerator)
  let A : PowerSeries K := ((weberJointQPolynomial a).coeff k).coeff l
  have hJ : J.constantCoeff = 1 := by
    rw [PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      jInvariantIntegralNumerator_constantCoeff, map_one]
  have hmapJ : PowerSeries.map f J = PowerSeries.expand 24 (by decide)
      (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator) := by
    rw [PowerSeries.map_expand]
    congr 1
  have hreg : P.qRegularization (PowerSeries.map f J) 24 n = PowerSeries.map f A := by
    rw [hmapJ]
    exact qRegularization_weberJointPolynomial_repr a k l P hdeg hrep
  have hfixedJ (σ : K ≃ₐ[ℚ] K) : PowerSeries.map σ.toRingHom J = J := by
    rw [PowerSeries.map_expand]
    congr 1
    ext m
    simp
  have hfixedA (σ : K ≃ₐ[ℚ] K) : PowerSeries.map σ.toRingHom A = A := by
    have hm := congrArg
      (fun p : (PowerSeries K)[X][X] => (p.coeff k).coeff l)
      (map_weberJointQPolynomial_eq_self a σ)
    simpa only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, A] using hm
  exact Polynomial.exists_map_of_fixed_qRegularization
    P J A hJ 24 n (by decide) hdeg hreg hfixedJ hfixedA

/-- The actual full joint root product has one rational trivariate
representation valid throughout `ℍ`. The innermost variable is evaluated at
`j`; the auxiliary tuple variable and the outer root variable remain formal. -/
theorem exists_rational_weberJointPolynomial (a : ℕ) :
    ∃ Φ : ℚ[X][X][X], ∀ τ : UpperHalfPlane,
      Φ.map (Polynomial.mapRingHom
        (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) (jInvariant τ))) =
          weberJointPolynomial a τ := by
  classical
  obtain ⟨ΦC, hrep, hdeg⟩ := exists_complex_weberJointPolynomial a
  have hrat (k l : ℕ) :
      ∃ Q : ℚ[X], Q.map (algebraMap ℚ ℂ) = (ΦC.coeff k).coeff l := by
    apply exists_rational_polynomial_weberJointPolynomial_repr a k l _ (hdeg k l)
    intro τ
    have hm := congrArg (fun p : ℂ[X][X] => (p.coeff k).coeff l) (hrep τ)
    simpa only [Polynomial.coeff_map, Polynomial.coe_mapRingHom,
      Polynomial.coe_evalRingHom] using hm.symm
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℚ[X][X][X],
      Φ.map (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap ℚ ℂ))) = ΦC := by
    apply (Polynomial.mem_map_range
      (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap ℚ ℂ)))).mpr
    intro k
    apply (Polynomial.mem_map_range (Polynomial.mapRingHom (algebraMap ℚ ℂ))).mpr
    intro l
    exact hrat k l
  refine ⟨Φ, fun τ => ?_⟩
  calc
    Φ.map (Polynomial.mapRingHom
        (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) (jInvariant τ))) =
      (Φ.map (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap ℚ ℂ)))).map
        (Polynomial.mapRingHom (Polynomial.evalRingHom (jInvariant τ))) := by
          ext k l
          simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom,
            Polynomial.coe_eval₂RingHom, Polynomial.coe_evalRingHom, Polynomial.eval_map]
    _ = weberJointPolynomial a τ := by rw [hΦ]; exact hrep τ

end ModularForm
