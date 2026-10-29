/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Weber.JointQExpansion

/-!
# Rational trivariate representation of the actual joint polynomial

The entire paired q-product is defined over the actual finite Galois phase
field and is fixed under its actual automorphisms. Unit triangular width-24
regularization transfers this formal fixedness to every bounded-degree
coefficient polynomial in `j`. Finite Galois descent then gives a rational
trivariate polynomial, without specializing the tuple-separating variable.
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
  obtain ⟨PK, hPK⟩ := Polynomial.exists_map_of_qRegularization_eq_map
    f P J hJ 24 n (by decide) hdeg A hreg
  have hdegK : PK.natDegree ≤ n := by
    rw [← Polynomial.natDegree_map_eq_of_injective f.injective PK, hPK]
    exact hdeg
  have hregK : PK.qRegularization J 24 n = A := by
    apply PowerSeries.map_injective f f.injective
    calc
      PowerSeries.map f (PK.qRegularization J 24 n) =
          (PK.map f).qRegularization (PowerSeries.map f J) 24 n :=
        (Polynomial.qRegularization_map PK J 24 n f).symm
      _ = PowerSeries.map f A := by rw [hPK, hreg]
  have hfixed (σ : K ≃ₐ[ℚ] K) : PK.map σ.toRingHom = PK := by
    have hσJ : PowerSeries.map σ.toRingHom J = J := by
      rw [PowerSeries.map_expand]
      congr 1
      ext m
      simp
    have hσA : PowerSeries.map σ.toRingHom A = A := by
      have hm := congrArg
        (fun p : (PowerSeries K)[X][X] => (p.coeff k).coeff l)
        (map_weberJointQPolynomial_eq_self a σ)
      simpa only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, A] using hm
    apply Polynomial.map_eq_of_qRegularization_fixed PK J hJ 24 n (by decide)
      hdegK σ.toRingHom hσJ
    rw [hregK]
    exact hσA
  have hcoeff : ∀ i, PK.coeff i ∈ (algebraMap ℚ K).range := by
    intro i
    apply (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) (E := K) (PK.coeff i)).mpr
    intro σ
    have hm := congrArg (fun p : K[X] => p.coeff i) (hfixed σ)
    rw [Polynomial.coeff_map] at hm
    exact hm
  obtain ⟨Q, hQ⟩ : ∃ Q : ℚ[X], Q.map (algebraMap ℚ K) = PK :=
    (Polynomial.mem_map_range (algebraMap ℚ K)).mpr hcoeff
  refine ⟨Q, ?_⟩
  rw [IsScalarTower.algebraMap_eq ℚ K ℂ, ← Polynomial.map_map, hQ]
  exact hPK

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
