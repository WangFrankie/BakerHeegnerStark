/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.QExpansion.PolynomialAnalytic
import BakerHeegnerStark.ModularForms.QExpansion.Identity
import BakerHeegnerStark.ModularForms.ModularPolynomial.CoefficientQExpansion
import BakerHeegnerStark.ModularForms.ModularPolynomial.Modularity
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Algebraic Integrality of the Actual Modular Polynomial Coefficients

The full common-width q-expansion of each actual symmetric coefficient agrees
with the regularization of its polynomial representation in `j`. Its
algebraic-integer coefficients therefore descend through the unit triangular
regularization system. This proves algebraic integrality, without asserting
rationality or descent to the integers.
-/

open UpperHalfPlane ModularForm Polynomial
open scoped MatrixGroups Manifold

noncomputable section

namespace BakerHeegnerStark

/-- The actual symmetric coefficient expansion agrees with the regularized
series of any bounded-degree polynomial representing it in `j`. -/
theorem qRegularization_cyclicSublatticePolynomial_repr {N : ℕ} (hN : 0 < N)
    (k : ℕ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ N * (cyclicSublatticeTriples N).card)
    (hrep : ∀ τ : UpperHalfPlane,
      (cyclicSublatticePolynomial N τ).coeff k = P.eval (jInvariant τ)) :
    P.qRegularization (PowerSeries.expand N (Nat.ne_of_gt hN)
      (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator)) N
        (N * (cyclicSublatticeTriples N).card) =
      PowerSeries.X ^ (N * (N * (cyclicSublatticeTriples N).card) -
        cyclicSublatticeTotalPoleOrder N) * (cyclicSublatticeQPolynomial hN).coeff k := by
  let n := N * (cyclicSublatticeTriples N).card
  let J : PowerSeries ℂ := PowerSeries.expand N (Nat.ne_of_gt hN)
    (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator)
  have hbound : cyclicSublatticeTotalPoleOrder N ≤ N * n :=
    cyclicSublatticeTotalPoleOrder_le hN
  change P.qRegularization J N n =
    PowerSeries.X ^ (N * n - cyclicSublatticeTotalPoleOrder N) *
      (cyclicSublatticeQPolynomial hN).coeff k
  apply PowerSeries.eq_of_hasSum_qParam (h := (N : ℝ)) (by exact_mod_cast hN)
    (f := fun τ => Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (N * n) *
      P.eval (jInvariant τ))
  · intro τ
    exact Polynomial.hasSum_qRegularization P J N n hdeg _ _
      (hasSum_jInvariantIntegralNumerator_commonWidth hN τ)
  · intro τ
    have hsum := PowerSeries.hasSum_coeff_X_pow_mul
      (hasSum_cyclicSublatticeQPolynomial_coeff hN k τ)
      (N * n - cyclicSublatticeTotalPoleOrder N)
    let q := Function.Periodic.qParam (N : ℝ) (τ : ℂ)
    have hvalue : q ^ (N * n - cyclicSublatticeTotalPoleOrder N) *
        (q ^ cyclicSublatticeTotalPoleOrder N *
          (cyclicSublatticePolynomial N τ).coeff k) =
        q ^ (N * n) * P.eval (jInvariant τ) := by
      calc
        _ = q ^ (N * n - cyclicSublatticeTotalPoleOrder N +
            cyclicSublatticeTotalPoleOrder N) * P.eval (jInvariant τ) := by
          rw [hrep τ, pow_add]
          ring
        _ = _ := by rw [Nat.sub_add_cancel hbound]
    exact hvalue ▸ hsum

/-- Any polynomial representation of an actual symmetric coefficient, with the
proved uniform degree bound, has algebraic-integer coefficients. The descent
uses the integral closure as a subring, not closure under division. -/
theorem isIntegral_coeff_of_cyclicSublatticePolynomial_repr {N : ℕ} (hN : 0 < N)
    (k : ℕ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ N * (cyclicSublatticeTriples N).card)
    (hrep : ∀ τ : UpperHalfPlane,
      (cyclicSublatticePolynomial N τ).coeff k = P.eval (jInvariant τ)) :
    ∀ i, IsIntegral ℤ (P.coeff i) := by
  let n := N * (cyclicSublatticeTriples N).card
  let J : PowerSeries ℂ := PowerSeries.expand N (Nat.ne_of_gt hN)
    (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator)
  have heq : P.qRegularization J N n =
      PowerSeries.X ^ (N * n - cyclicSublatticeTotalPoleOrder N) *
        (cyclicSublatticeQPolynomial hN).coeff k :=
    qRegularization_cyclicSublatticePolynomial_repr hN k P hdeg hrep
  let S : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  let JS : PowerSeries S := PowerSeries.expand N (Nat.ne_of_gt hN)
    (PowerSeries.map (Int.castRingHom S) jInvariantIntegralNumerator)
  have hJS : JS.constantCoeff = 1 := by
    dsimp only [JS]
    rw [PowerSeries.constantCoeff_expand,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, jInvariantIntegralNumerator_constantCoeff,
      map_one]
  have hmap : PowerSeries.map S.subtype JS = J := by
    rw [PowerSeries.map_expand]
    congr 1
  have hreg : ∀ m,
      (P.qRegularization (PowerSeries.map S.subtype JS) N n).coeff m ∈ S := by
    intro m
    rw [hmap, heq, PowerSeries.coeff_X_pow_mul']
    change IsIntegral ℤ _
    split_ifs
    · exact isIntegral_cyclicSublatticeQPolynomial_coeff hN k _
    · exact isIntegral_zero
  exact Polynomial.coeff_mem_of_qRegularization P S JS hJS N n hN hdeg hreg

/-- Every coefficient of the actual cyclic-sublattice product is a polynomial
in `j`, of the proved uniform degree bound, whose coefficients are algebraic
integers. Holomorphicity, cusp growth, and modular invariance are all supplied
by the actual root product. -/
theorem exists_integral_polynomial_cyclicSublatticePolynomial_coeff {N : ℕ}
    (hN : 0 < N) (k : ℕ) :
    ∃ P : ℂ[X], P.natDegree ≤ N * (cyclicSublatticeTriples N).card ∧
      (∀ τ : UpperHalfPlane,
        (cyclicSublatticePolynomial N τ).coeff k = P.eval (jInvariant τ)) ∧
      ∀ i, IsIntegral ℤ (P.coeff i) := by
  let φ : SlashInvariantForm 𝒮ℒ 0 :=
    { toFun := fun τ => (cyclicSublatticePolynomial N τ).coeff k
      slash_action_eq' := by
        intro γ hγ
        obtain ⟨γ, rfl⟩ := hγ
        change ((fun τ => (cyclicSublatticePolynomial N τ).coeff k) ∣[(0 : ℤ)] γ) =
          (fun τ => (cyclicSublatticePolynomial N τ).coeff k)
        funext τ
        simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using
          cyclicSublatticePolynomial_coeff_smul hN k γ τ }
  obtain ⟨P, hdeg, hrep⟩ := exists_polynomial_jInvariant_of_isBigO φ
    (mdifferentiable_cyclicSublatticePolynomial_coeff hN k)
    (N * (cyclicSublatticeTriples N).card)
    (isBigO_cyclicSublatticePolynomial_coeff hN k)
  exact ⟨P, hdeg, hrep,
    isIntegral_coeff_of_cyclicSublatticePolynomial_repr hN k P hdeg hrep⟩

end BakerHeegnerStark
