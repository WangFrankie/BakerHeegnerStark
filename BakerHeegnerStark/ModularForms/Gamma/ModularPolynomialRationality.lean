/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.CyclotomicPowerSeries
import BakerHeegnerStark.FieldTheory.Cyclotomic
import BakerHeegnerStark.ModularForms.QExpansion.PolynomialAnalytic
import BakerHeegnerStark.ModularForms.QExpansion.Identity

/-!
# Rationality of the Actual Twisted Gamma Modular Polynomial

The full common-width symmetric series descends from its concrete finite
cyclotomic coefficient field. Galois reindexing fixes the series, and unit
triangular q-regularization transfers this fixedness to the actual coefficient
polynomials in j. The resulting bivariate polynomial has rational coefficients.
-/

open UpperHalfPlane ModularForm Polynomial
open scoped MatrixGroups Manifold Polynomial.Bivariate

noncomputable section

namespace BakerHeegnerStark

/-- The actual symmetric gamma series equals the regularized polynomial in j. -/
theorem qRegularization_cyclicSublatticeGammaPolynomial_repr {N : ℕ} (hN : 0 < N) (hN3 : N % 3 = 2)
    (k : ℕ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ (N + 1) * (cyclicSublatticeTriples N).card)
    (hrep : ∀ τ : UpperHalfPlane,
      (cyclicSublatticeGammaPolynomial N τ).coeff k = P.eval (jInvariant τ)) :
    P.qRegularization (PowerSeries.expand N (Nat.ne_of_gt hN)
      (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator)) N
        ((N + 1) * (cyclicSublatticeTriples N).card) =
      PowerSeries.X ^ (N * ((N + 1) * (cyclicSublatticeTriples N).card) -
        cyclicSublatticeGammaTotalPoleOrder N) * (cyclicSublatticeGammaQPolynomial hN).coeff k := by
  let n := (N + 1) * (cyclicSublatticeTriples N).card
  let J : PowerSeries ℂ := PowerSeries.expand N (Nat.ne_of_gt hN)
    (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator)
  have hbound : cyclicSublatticeGammaTotalPoleOrder N ≤ N * n :=
    cyclicSublatticeGammaTotalPoleOrder_le hN
  change P.qRegularization J N n =
    PowerSeries.X ^ (N * n - cyclicSublatticeGammaTotalPoleOrder N) *
      (cyclicSublatticeGammaQPolynomial hN).coeff k
  apply PowerSeries.eq_of_hasSum_qParam (h := (N : ℝ)) (by exact_mod_cast hN)
    (f := fun τ => Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (N * n) *
      P.eval (jInvariant τ))
  · intro τ
    exact Polynomial.hasSum_qRegularization P J N n hdeg _ _
      (hasSum_jInvariantIntegralNumerator_commonWidth hN τ)
  · intro τ
    have hsum := PowerSeries.hasSum_coeff_X_pow_mul
      (hasSum_cyclicSublatticeGammaQPolynomial_coeff hN hN3 k τ)
      (N * n - cyclicSublatticeGammaTotalPoleOrder N)
    let q := Function.Periodic.qParam (N : ℝ) (τ : ℂ)
    have hvalue : q ^ (N * n - cyclicSublatticeGammaTotalPoleOrder N) *
        (q ^ cyclicSublatticeGammaTotalPoleOrder N *
          (cyclicSublatticeGammaPolynomial N τ).coeff k) =
        q ^ (N * n) * P.eval (jInvariant τ) := by
      calc
        _ = q ^ (N * n - cyclicSublatticeGammaTotalPoleOrder N +
            cyclicSublatticeGammaTotalPoleOrder N) * P.eval (jInvariant τ) := by
          rw [hrep τ, pow_add]
          ring
        _ = _ := by rw [Nat.sub_add_cancel hbound]
    exact hvalue ▸ hsum

/-- Cyclotomic Galois fixedness descends the actual gamma coefficient polynomial. -/
theorem exists_rational_polynomial_cyclicSublatticeGammaPolynomial_repr
    {N : ℕ} (hN : 0 < N) (hN3 : N % 3 = 2) (k : ℕ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ (N + 1) * (cyclicSublatticeTriples N).card)
    (hrep : ∀ τ : UpperHalfPlane,
      (cyclicSublatticeGammaPolynomial N τ).coeff k = P.eval (jInvariant τ)) :
    ∃ Q : ℚ[X], Q.map (algebraMap ℚ ℂ) = P := by
  let K := cyclicSublatticeCyclotomicField N
  let ξ : K := cyclicSublatticeCyclotomicRoot N
  let f : K →+* ℂ := algebraMap K ℂ
  let n := (N + 1) * (cyclicSublatticeTriples N).card
  let s := N * n - cyclicSublatticeGammaTotalPoleOrder N
  let J : PowerSeries K := PowerSeries.expand N (Nat.ne_of_gt hN)
    (PowerSeries.map (Int.castRingHom K) jInvariantIntegralNumerator)
  let A : PowerSeries K := PowerSeries.X ^ s * (cyclotomicGammaQPolynomial hN ξ).coeff k
  have hJ : J.constantCoeff = 1 := by
    rw [PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      jInvariantIntegralNumerator_constantCoeff, map_one]
  have hmapIntJ : PowerSeries.map f
      (PowerSeries.map (Int.castRingHom K) jInvariantIntegralNumerator) =
      PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator := by
    ext m
    simp
  have hmapJ : PowerSeries.map f J = PowerSeries.expand N (Nat.ne_of_gt hN)
      (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator) := by
    rw [PowerSeries.map_expand, hmapIntJ]
  have hmapB : PowerSeries.map f ((cyclotomicGammaQPolynomial hN ξ).coeff k) =
      (cyclicSublatticeGammaQPolynomial hN).coeff k := by
    have hm := map_cyclotomicGammaQPolynomial hN f ξ
    rw [show f ξ = cyclicSublatticePhase 1 N from rfl,
      cyclotomicGammaQPolynomial_complex] at hm
    simpa only [Polynomial.coeff_map] using congrArg (fun p : (PowerSeries ℂ)[X] => p.coeff k) hm
  have hreg : P.qRegularization (PowerSeries.map f J) N n = PowerSeries.map f A := by
    rw [hmapJ, qRegularization_cyclicSublatticeGammaPolynomial_repr hN hN3 k P hdeg hrep]
    simp only [A, map_mul, map_pow, PowerSeries.map_X, hmapB, s, n]
  obtain ⟨PK, hPK⟩ := Polynomial.exists_map_of_qRegularization_eq_map
    f P J hJ N n hN hdeg A hreg
  have hdegK : PK.natDegree ≤ n := by
    rw [← Polynomial.natDegree_map_eq_of_injective f.injective PK, hPK]
    exact hdeg
  have hregK : PK.qRegularization J N n = A := by
    apply PowerSeries.map_injective f f.injective
    calc
      PowerSeries.map f (PK.qRegularization J N n) =
          (PK.map f).qRegularization (PowerSeries.map f J) N n :=
        (Polynomial.qRegularization_map PK J N n f).symm
      _ = PowerSeries.map f A := by rw [hPK, hreg]
  have hξ : ξ ^ N = 1 := (isPrimitiveRoot_cyclicSublatticeCyclotomicRoot hN).pow_eq_one
  have hfixed (σ : K ≃ₐ[ℚ] K) : PK.map σ.toRingHom = PK := by
    have hσJ : PowerSeries.map σ.toRingHom J = J := by
      rw [PowerSeries.map_expand]
      congr 1
      ext m
      simp
    obtain ⟨u, hu, hσξ⟩ := exists_coprime_cyclicSublatticeCyclotomicRoot_aut hN σ
    have hσpoly := map_cyclotomicGammaQPolynomial_eq_self hN ξ hξ σ.toRingHom u hu hσξ
    have hσB : PowerSeries.map σ.toRingHom ((cyclotomicGammaQPolynomial hN ξ).coeff k) =
        (cyclotomicGammaQPolynomial hN ξ).coeff k := by
      simpa only [Polynomial.coeff_map] using
        congrArg (fun p : (PowerSeries K)[X] => p.coeff k) hσpoly
    have hσA : PowerSeries.map σ.toRingHom A = A := by
      simp only [A, map_mul, map_pow, PowerSeries.map_X, hσB]
    apply Polynomial.map_eq_of_qRegularization_fixed PK J hJ N n hN hdegK σ.toRingHom hσJ
    rw [hregK]
    exact hσA
  let : FiniteDimensional ℚ K := finiteDimensional_cyclicSublatticeCyclotomicField hN
  let : IsGalois ℚ K := isGalois_cyclicSublatticeCyclotomicField hN
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

/-- Every actual twisted symmetric coefficient is a rational polynomial in j. -/
theorem exists_rational_polynomial_cyclicSublatticeGammaPolynomial_coeff
    {N : ℕ} (hN : 0 < N) (hN3 : N % 3 = 2) (k : ℕ) :
    ∃ Q : ℚ[X], ∀ τ : UpperHalfPlane,
      (cyclicSublatticeGammaPolynomial N τ).coeff k =
        (Q.map (algebraMap ℚ ℂ)).eval (jInvariant τ) := by
  let φ : SlashInvariantForm 𝒮ℒ 0 :=
    { toFun := fun τ => (cyclicSublatticeGammaPolynomial N τ).coeff k
      slash_action_eq' := by
        intro γ hγ
        obtain ⟨γ, rfl⟩ := hγ
        change ((fun τ => (cyclicSublatticeGammaPolynomial N τ).coeff k) ∣[(0 : ℤ)] γ) =
          (fun τ => (cyclicSublatticeGammaPolynomial N τ).coeff k)
        funext τ
        simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using
          cyclicSublatticeGammaPolynomial_coeff_smul hN hN3 k γ τ }
  obtain ⟨P, hdeg, hrep⟩ := exists_polynomial_jInvariant_of_isBigO φ
    (mdifferentiable_cyclicSublatticeGammaPolynomial_coeff hN k)
    ((N + 1) * (cyclicSublatticeTriples N).card)
    (isBigO_cyclicSublatticeGammaPolynomial_coeff hN k)
  obtain ⟨Q, hQ⟩ :=
    exists_rational_polynomial_cyclicSublatticeGammaPolynomial_repr hN hN3 k P hdeg hrep
  refine ⟨Q, fun τ => ?_⟩
  rw [hQ]
  exact hrep τ

/-- The actual full twisted gamma product has a rational bivariate realization
at every level congruent to two modulo three, without CM reciprocity. -/
theorem exists_rational_gammaModularPolynomial {N : ℕ} (hN : 0 < N) (hN3 : N % 3 = 2) :
    ∃ Ψ : ℚ[X][Y], ∀ τ : UpperHalfPlane,
      aevalAeval (C (jInvariant τ)) (X : ℂ[X]) Ψ = cyclicSublatticeGammaPolynomial N τ := by
  classical
  have hcoeff (k : ℕ) :=
    exists_rational_polynomial_cyclicSublatticeGammaPolynomial_coeff hN hN3 k
  choose Q hQ using hcoeff
  refine ⟨∑ k ∈ Finset.range ((cyclicSublatticeTriples N).card + 1),
    C (Q k) * X ^ k, fun τ => ?_⟩
  simp only [map_sum, map_mul, map_pow, aevalAeval_C, aevalAeval_Y]
  rw [(cyclicSublatticeGammaPolynomial N τ).as_sum_range_C_mul_X_pow,
    natDegree_cyclicSublatticeGammaPolynomial]
  apply Finset.sum_congr rfl
  intro k _
  change (Q k).eval₂ (algebraMap ℚ ℂ[X]) (C (jInvariant τ)) * X ^ k =
    C ((cyclicSublatticeGammaPolynomial N τ).coeff k) * X ^ k
  have hbase : algebraMap ℚ ℂ[X] =
      (C : ℂ →+* ℂ[X]).comp (algebraMap ℚ ℂ) :=
    IsScalarTower.algebraMap_eq ℚ ℂ ℂ[X]
  rw [hbase, ← Polynomial.eval₂_map (algebraMap ℚ ℂ) (C : ℂ →+* ℂ[X])
    (C (jInvariant τ)), Polynomial.eval₂_at_apply, ← hQ k τ]

end BakerHeegnerStark
