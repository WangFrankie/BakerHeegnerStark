/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.QExpansion
import BakerHeegnerStark.ModularForms.ModularPolynomial.Coefficients

/-!
# Integral q-Expansions of the Actual Symmetric Product

A single pole shift regularizes every coefficient of the actual
cyclic-sublattice root product. The resulting full power series converge
throughout the upper half-plane and have algebraic-integer coefficients.
These statements do not yet assert rationality or Galois descent.
-/

open UpperHalfPlane ModularForm Polynomial

noncomputable section

namespace BakerHeegnerStark

private theorem cyclicSublatticeCoefficient_pos {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) :
    0 < t.1 ∧ 0 < t.2.2 := by
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  have hpos : 0 < t.1 * t.2.2 := by omega
  constructor
  · by_contra h
    have hz : t.1 = 0 := by omega
    simp [hz] at hpos
  · by_contra h
    have hz : t.2.2 = 0 := by omega
    simp [hz] at hpos

/-- The common pole shift used for all coefficients of the symmetric product. -/
def cyclicSublatticeTotalPoleOrder (N : ℕ) : ℕ :=
  ∑ t ∈ cyclicSublatticeTriples N, t.1 * t.1

/-- The actual product of regularized linear factors, with power-series
coefficients. No coefficientwise convergence or integrality is assumed. -/
def cyclicSublatticeQPolynomial {N : ℕ} (hN : 0 < N) : (PowerSeries ℂ)[X] :=
  ∏ t ∈ (cyclicSublatticeTriples N).attach,
    (C ((PowerSeries.X : PowerSeries ℂ) ^ (t.1.1 * t.1.1)) * X -
      C (cyclicSublatticeRootQExpansion t.1
        (cyclicSublatticeCoefficient_pos hN t.2).1))

private theorem hasSum_powerSeries_C (a z : ℂ) :
    HasSum (fun m : ℕ => (PowerSeries.C a).coeff m * z ^ m) a := by
  convert hasSum_ite_eq 0 a using 1
  funext m
  by_cases hm : m = 0 <;> simp [PowerSeries.coeff_C, hm]

/-- A monomial power series sums to its actual monomial value. -/
theorem hasSum_powerSeries_X_pow (n : ℕ) (z : ℂ) :
    HasSum (fun m : ℕ => ((PowerSeries.X : PowerSeries ℂ) ^ n).coeff m * z ^ m)
      (z ^ n) := by
  convert hasSum_ite_eq n (z ^ n) using 1
  funext m
  by_cases hm : m = n <;> simp [PowerSeries.coeff_X_pow, hm]

private theorem hasSum_powerSeries_polynomial_mul
    {P Q : (PowerSeries ℂ)[X]} {p q : ℂ[X]} {z : ℂ}
    (hP : ∀ k : ℕ, HasSum (fun m : ℕ => (P.coeff k).coeff m * z ^ m) (p.coeff k))
    (hQ : ∀ k : ℕ, HasSum (fun m : ℕ => (Q.coeff k).coeff m * z ^ m) (q.coeff k))
    (k : ℕ) :
    HasSum (fun m : ℕ => ((P * Q).coeff k).coeff m * z ^ m) ((p * q).coeff k) := by
  classical
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  have h := hasSum_sum (s := Finset.antidiagonal k)
    (fun ij _ => PowerSeries.hasSum_coeff_mul (hP ij.1) (hQ ij.2))
  convert h using 1
  funext m
  simp only [map_sum, Finset.sum_mul]

/-- Complete coefficientwise sums commute with a finite polynomial product. -/
theorem hasSum_powerSeries_polynomial_prod {ι : Type*}
    (s : Finset ι) (P : ι → (PowerSeries ℂ)[X]) (p : ι → ℂ[X]) (z : ℂ)
    (h : ∀ i ∈ s, ∀ k : ℕ,
      HasSum (fun m : ℕ => ((P i).coeff k).coeff m * z ^ m) ((p i).coeff k))
    (k : ℕ) :
    HasSum (fun m : ℕ => ((∏ i ∈ s, P i).coeff k).coeff m * z ^ m)
      ((∏ i ∈ s, p i).coeff k) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
      by_cases hk : k = 0
      · subst k
        simpa using hasSum_powerSeries_C 1 z
      · simp [Polynomial.coeff_one, hk]
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact hasSum_powerSeries_polynomial_mul
        (h i (Finset.mem_insert_self i s))
        (fun j => ih (fun l hl => h l (Finset.mem_insert_of_mem hl)) j) k

/-- A regularized linear factor has the corresponding complete coefficient sums. -/
theorem hasSum_powerSeries_linear_factor
    {A B : PowerSeries ℂ} {a b z : ℂ}
    (hA : HasSum (fun m : ℕ => A.coeff m * z ^ m) a)
    (hB : HasSum (fun m : ℕ => B.coeff m * z ^ m) b) (k : ℕ) :
    HasSum (fun m : ℕ => ((C A * X - C B).coeff k).coeff m * z ^ m)
      ((C a * X - C b).coeff k) := by
  cases k with
  | zero =>
      simpa using hB.neg
  | succ k =>
      cases k with
      | zero => simpa using hA
      | succ k => simp

/-- Multiplying every root factor by its individual monomial gives one total pole shift. -/
theorem regularized_root_product {ι : Type*} (s : Finset ι)
    (pole : ι → ℕ) (root : ι → ℂ) (Q : ℂ) :
    (∏ t ∈ s, (C (Q ^ pole t) * X - C (Q ^ pole t * root t))) =
      C (Q ^ (∑ t ∈ s, pole t)) * ∏ t ∈ s, (X - C (root t)) := by
  classical
  calc
    _ = ∏ t ∈ s, C (Q ^ pole t) * (X - C (root t)) := by
      apply Finset.prod_congr rfl
      intro t ht
      rw [mul_sub, ← C_mul]
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]

/-- The full common-width q-expansion of every actual symmetric coefficient,
with one pole shift independent of the polynomial coefficient index. -/
theorem hasSum_cyclicSublatticeQPolynomial_coeff {N : ℕ} (hN : 0 < N)
    (k : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => ((cyclicSublatticeQPolynomial hN).coeff k).coeff m *
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ m)
      (Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ cyclicSublatticeTotalPoleOrder N *
        (cyclicSublatticePolynomial N τ).coeff k) := by
  classical
  let Q := Function.Periodic.qParam (N : ℝ) (τ : ℂ)
  have h := hasSum_powerSeries_polynomial_prod
    (cyclicSublatticeTriples N).attach
    (fun t => C ((PowerSeries.X : PowerSeries ℂ) ^ (t.1.1 * t.1.1)) * X -
      C (cyclicSublatticeRootQExpansion t.1
        (cyclicSublatticeCoefficient_pos hN t.2).1))
    (fun t => C (Q ^ (t.1.1 * t.1.1)) * X -
      C (Q ^ (t.1.1 * t.1.1) * jInvariant (cyclicSublatticePoint t.1 τ))) Q
    (fun t _ k => hasSum_powerSeries_linear_factor
      (hasSum_powerSeries_X_pow _ Q)
      (hasSum_cyclicSublatticeRootQExpansion hN t.2
        (cyclicSublatticeCoefficient_pos hN t.2).1 τ) k) k
  have hmodel := Finset.prod_attach (cyclicSublatticeTriples N)
    (fun t => (C (Q ^ (t.1 * t.1)) * X -
      C (Q ^ (t.1 * t.1) * jInvariant (cyclicSublatticePoint t τ)) : ℂ[X]))
  rw [hmodel, regularized_root_product, Polynomial.coeff_C_mul] at h
  exact h

private theorem isIntegral_powerSeries_mul_coeff {P Q : PowerSeries ℂ}
    (hP : ∀ m, IsIntegral ℤ (P.coeff m))
    (hQ : ∀ m, IsIntegral ℤ (Q.coeff m)) (m : ℕ) :
    IsIntegral ℤ ((P * Q).coeff m) := by
  rw [PowerSeries.coeff_mul]
  exact IsIntegral.sum _ (fun ij _ => (hP ij.1).mul (hQ ij.2))

private theorem isIntegral_powerSeries_polynomial_mul_coeff
    {P Q : (PowerSeries ℂ)[X]}
    (hP : ∀ k m, IsIntegral ℤ ((P.coeff k).coeff m))
    (hQ : ∀ k m, IsIntegral ℤ ((Q.coeff k).coeff m)) (k m : ℕ) :
    IsIntegral ℤ (((P * Q).coeff k).coeff m) := by
  rw [Polynomial.coeff_mul, map_sum]
  exact IsIntegral.sum _ (fun ij _ =>
    isIntegral_powerSeries_mul_coeff (hP ij.1) (hQ ij.2) m)

/-- Finite polynomial products preserve algebraic integrality of every series coefficient. -/
theorem isIntegral_powerSeries_polynomial_prod_coeff {ι : Type*}
    (s : Finset ι) (P : ι → (PowerSeries ℂ)[X])
    (h : ∀ i ∈ s, ∀ k m, IsIntegral ℤ (((P i).coeff k).coeff m)) (k m : ℕ) :
    IsIntegral ℤ (((∏ i ∈ s, P i).coeff k).coeff m) := by
  classical
  induction s using Finset.induction_on generalizing k m with
  | empty =>
      simp only [Finset.prod_empty, Polynomial.coeff_one, apply_ite,
        PowerSeries.coeff_one, map_zero]
      split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact isIntegral_powerSeries_polynomial_mul_coeff
        (h i (Finset.mem_insert_self i s))
        (fun j n => ih (fun l hl => h l (Finset.mem_insert_of_mem hl)) j n) k m

/-- A linear factor preserves algebraic integrality of its two full coefficient series. -/
theorem isIntegral_powerSeries_linear_factor_coeff {A B : PowerSeries ℂ}
    (hA : ∀ m, IsIntegral ℤ (A.coeff m))
    (hB : ∀ m, IsIntegral ℤ (B.coeff m)) (k m : ℕ) :
    IsIntegral ℤ (((C A * X - C B).coeff k).coeff m) := by
  cases k with
  | zero => simpa using (hB m).neg
  | succ k =>
      cases k with
      | zero => simpa using hA m
      | succ k => simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))

/-- Every power-series coefficient of every symmetric coefficient is an
algebraic integer. This uses finite sums and products only, not division. -/
theorem isIntegral_cyclicSublatticeQPolynomial_coeff {N : ℕ} (hN : 0 < N)
    (k m : ℕ) :
    IsIntegral ℤ (((cyclicSublatticeQPolynomial hN).coeff k).coeff m) := by
  classical
  apply isIntegral_powerSeries_polynomial_prod_coeff
  intro t ht k m
  apply isIntegral_powerSeries_linear_factor_coeff
  · intro n
    rw [PowerSeries.coeff_X_pow]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  · exact isIntegral_cyclicSublatticeRootQExpansion_coeff t.1
      (cyclicSublatticeCoefficient_pos hN t.2).1
      (cyclicSublatticeCoefficient_pos hN t.2).2

/-- The common shift fits the uniform bound needed for polynomial
regularization at the cusp. -/
theorem cyclicSublatticeTotalPoleOrder_le {N : ℕ} (hN : 0 < N) :
    cyclicSublatticeTotalPoleOrder N ≤ N * (N * (cyclicSublatticeTriples N).card) := by
  classical
  calc
    cyclicSublatticeTotalPoleOrder N ≤
        ∑ _t ∈ cyclicSublatticeTriples N, N * N := by
      apply Finset.sum_le_sum
      intro t ht
      have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
      have hd := (cyclicSublatticeCoefficient_pos hN ht).2
      have haN : t.1 ≤ N := by
        calc
          t.1 = t.1 * 1 := by omega
          _ ≤ t.1 * t.2.2 := Nat.mul_le_mul_left _ hd
          _ = N := had
      exact Nat.mul_le_mul haN haN
    _ = N * (N * (cyclicSublatticeTriples N).card) := by
      simp only [Finset.sum_const, smul_eq_mul]
      ac_rfl

end BakerHeegnerStark
