/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.CyclicQExpansion
import BakerHeegnerStark.ModularForms.ModularPolynomial.CoefficientQExpansion

/-!
# Full q-Expansions of Symmetric Gamma Coefficients

The individual common-width gamma series give the complete finite product of
regularized linear factors. Every coefficient has a convergent series for the
actual symmetric coefficient and every series coefficient is an algebraic
integer. The total pole order fits the existing polynomial regularization
bound. This does not yet assert rationality of the coefficient polynomials.
-/

open UpperHalfPlane ModularForm Polynomial

noncomputable section

namespace BakerHeegnerStark

/-- The common pole shift for all coefficients of the twisted root product. -/
def cyclicSublatticeGammaTotalPoleOrder (N : ℕ) : ℕ :=
  ∑ t ∈ cyclicSublatticeTriples N, cyclicSublatticeGammaPoleOrder N t

/-- The actual product of regularized gamma factors over the full series ring. -/
def cyclicSublatticeGammaQPolynomial {N : ℕ} (hN : 0 < N) : (PowerSeries ℂ)[X] :=
  ∏ t ∈ (cyclicSublatticeTriples N).attach,
    (C ((PowerSeries.X : PowerSeries ℂ) ^ cyclicSublatticeGammaPoleOrder N t.1) * X -
      C (cyclicSublatticeGammaRootQExpansion hN t.1 (cyclicSublatticeTriple_pos hN t).1))

/-- Every symmetric coefficient has its full actual common-width series. -/
theorem hasSum_cyclicSublatticeGammaQPolynomial_coeff {N : ℕ}
    (hN : 0 < N) (hN3 : N % 3 = 2) (k : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => ((cyclicSublatticeGammaQPolynomial hN).coeff k).coeff m *
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ m)
      (Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ cyclicSublatticeGammaTotalPoleOrder N *
        (cyclicSublatticeGammaPolynomial N τ).coeff k) := by
  classical
  let Q := Function.Periodic.qParam (N : ℝ) (τ : ℂ)
  have h := hasSum_powerSeries_polynomial_prod
    (cyclicSublatticeTriples N).attach
    (fun t => C ((PowerSeries.X : PowerSeries ℂ) ^ cyclicSublatticeGammaPoleOrder N t.1) * X -
      C (cyclicSublatticeGammaRootQExpansion hN t.1 (cyclicSublatticeTriple_pos hN t).1))
    (fun t => C (Q ^ cyclicSublatticeGammaPoleOrder N t.1) * X -
      C (Q ^ cyclicSublatticeGammaPoleOrder N t.1 * cyclicSublatticeGammaRoot t.1 τ)) Q
    (fun t _ k => hasSum_powerSeries_linear_factor
      (hasSum_powerSeries_X_pow _ Q)
      (hasSum_cyclicSublatticeGammaRootQExpansion hN hN3 t.2
        (cyclicSublatticeTriple_pos hN t).1 τ) k) k
  have hmodel := Finset.prod_attach (cyclicSublatticeTriples N)
    (fun t => (C (Q ^ cyclicSublatticeGammaPoleOrder N t) * X -
      C (Q ^ cyclicSublatticeGammaPoleOrder N t * cyclicSublatticeGammaRoot t τ) : ℂ[X]))
  rw [hmodel, regularized_root_product, Polynomial.coeff_C_mul] at h
  exact h

/-- Every coefficient of every symmetric full series is an algebraic integer. -/
theorem isIntegral_cyclicSublatticeGammaQPolynomial_coeff {N : ℕ} (hN : 0 < N)
    (k m : ℕ) :
    IsIntegral ℤ (((cyclicSublatticeGammaQPolynomial hN).coeff k).coeff m) := by
  classical
  apply isIntegral_powerSeries_polynomial_prod_coeff
  intro t ht k m
  apply isIntegral_powerSeries_linear_factor_coeff
  · intro n
    rw [PowerSeries.coeff_X_pow]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  · exact isIntegral_cyclicSublatticeGammaRootQExpansion_coeff hN t.1
      (cyclicSublatticeTriple_pos hN t).1 (cyclicSublatticeTriple_pos hN t).2

/-- The total pole shift fits the uniform actual coefficient growth bound. -/
theorem cyclicSublatticeGammaTotalPoleOrder_le {N : ℕ} (hN : 0 < N) :
    cyclicSublatticeGammaTotalPoleOrder N ≤
      N * ((N + 1) * (cyclicSublatticeTriples N).card) := by
  classical
  calc
    cyclicSublatticeGammaTotalPoleOrder N ≤
        ∑ _t ∈ cyclicSublatticeTriples N, N * (N + 1) := by
      apply Finset.sum_le_sum
      intro t ht
      have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
      have hd := (cyclicSublatticeTriple_pos hN ⟨t, ht⟩).2
      have haN : t.1 ≤ N := by
        calc
          t.1 = t.1 * 1 := by omega
          _ ≤ t.1 * t.2.2 := Nat.mul_le_mul_left _ hd
          _ = N := had
      calc
        cyclicSublatticeGammaPoleOrder N t ≤ N + t.1 * t.1 := by
          simp only [cyclicSublatticeGammaPoleOrder]
          omega
        _ ≤ N + N * N := Nat.add_le_add_left (Nat.mul_le_mul haN haN) N
        _ = N * (N + 1) := by ring
    _ = N * ((N + 1) * (cyclicSublatticeTriples N).card) := by
      simp only [Finset.sum_const, smul_eq_mul]
      ac_rfl

end BakerHeegnerStark
