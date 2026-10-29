/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.QExpansion
import BakerHeegnerStark.ModularForms.ModularPolynomial.Coefficients
import BakerHeegnerStark.ModularForms.QExpansion.PolynomialAnalytic

/-!
# The Diagonal Cyclic-Sublattice Product at the Cusp

For a nonsquare level, each diagonal root factor has a unique dominant pole.
The full convergent q-expansions determine its leading constant, and the finite
product therefore has a nonzero leading constant of complex norm one. No degree
assumption on a modular polynomial is used.
-/

open UpperHalfPlane ModularForm Filter Polynomial
open scoped Topology

noncomputable section

namespace BakerHeegnerStark

/-- The total pole order of the diagonal root product in the width-`N` parameter. -/
def cyclicSublatticeDiagonalPoleOrder (N : ℕ) : ℕ :=
  ∑ t ∈ cyclicSublatticeTriples N, max N (t.1 * t.1)

/-- The actual leading constant of the diagonal root product at a nonsquare level. -/
def cyclicSublatticeDiagonalConstant (N : ℕ) : ℂ :=
  ∏ t ∈ cyclicSublatticeTriples N,
    if N < t.1 * t.1 then -(cyclicSublatticePhase t.2.1 t.2.2)⁻¹ else 1

/-- A translation phase has complex norm one, even at denominator zero. -/
theorem norm_cyclicSublatticePhase (b d : ℕ) :
    ‖cyclicSublatticePhase b d‖ = 1 := by
  have heq : 2 * (Real.pi : ℂ) * Complex.I * b / d =
      ((2 * Real.pi * b / d : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [cyclicSublatticePhase, heq, Complex.norm_exp_ofReal_mul_I]

/-- The normalized ordinary j-value tends to its integral numerator's constant term. -/
theorem tendsto_qParam_pow_mul_jInvariant {N : ℕ} (hN : 0 < N) :
    Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ N * jInvariant τ)
      atImInfty (𝓝 1) := by
  have h := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion
    (show (0 : ℝ) < N by exact_mod_cast hN)
    (fun τ => by
      simpa only [smul_eq_mul] using
        hasSum_jInvariantIntegralNumerator_commonWidth hN τ)
  rw [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_expand,
    ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, jInvariantIntegralNumerator_constantCoeff,
    map_one] at h
  exact h

/-- A transformed j-value has the inverse translation phase as its leading constant. -/
theorem tendsto_qParam_pow_mul_cyclicSublattice_jInvariant {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) :
    Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (t.1 * t.1) *
        jInvariant (cyclicSublatticePoint t τ))
      atImInfty (𝓝 ((cyclicSublatticePhase t.2.1 t.2.2)⁻¹)) := by
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  have ha : 0 < t.1 := by
    by_contra h
    have hz : t.1 = 0 := by omega
    simp [hz] at had
    omega
  have h := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion
    (show (0 : ℝ) < N by exact_mod_cast hN)
    (fun τ => by
      simpa only [smul_eq_mul] using hasSum_cyclicSublatticeRootQExpansion hN ht ha τ)
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff,
    cyclicSublatticeRootQExpansion_constantCoeff] using h

/-- The dominant pole of one diagonal factor has no cancellation at a nonsquare level. -/
theorem tendsto_cyclicSublatticeDiagonalFactor {N : ℕ} (hN : 0 < N)
    (hns : ¬ IsSquare N) {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) :
    Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ max N (t.1 * t.1) *
        (jInvariant τ - jInvariant (cyclicSublatticePoint t τ)))
      atImInfty
      (𝓝 (if N < t.1 * t.1 then -(cyclicSublatticePhase t.2.1 t.2.2)⁻¹ else 1)) := by
  have hbase := tendsto_qParam_pow_mul_jInvariant hN
  have hroot := tendsto_qParam_pow_mul_cyclicSublattice_jInvariant hN ht
  have hq := UpperHalfPlane.qParam_tendsto_atImInfty
    (show (0 : ℝ) < N by exact_mod_cast hN)
  have hne : t.1 * t.1 ≠ N := by
    intro heq
    exact hns ⟨t.1, heq.symm⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hz : Tendsto (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (N - t.1 * t.1))
        atImInfty (𝓝 (0 : ℂ)) := by
      simpa only [zero_pow (show N - t.1 * t.1 ≠ 0 by omega)] using
        hq.pow (N - t.1 * t.1)
    have hsmall : Tendsto (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ N *
          jInvariant (cyclicSublatticePoint t τ)) atImInfty (𝓝 (0 : ℂ)) := by
      convert hz.mul hroot using 1
      · funext τ
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      · simp only [zero_mul]
    simpa only [max_eq_left (Nat.le_of_lt hlt),
      ite_eq_right (by omega : ¬ N < t.1 * t.1), mul_sub, sub_zero] using hbase.sub hsmall
  · have hz : Tendsto (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (t.1 * t.1 - N))
        atImInfty (𝓝 (0 : ℂ)) := by
      simpa only [zero_pow (show t.1 * t.1 - N ≠ 0 by omega)] using
        hq.pow (t.1 * t.1 - N)
    have hsmall : Tendsto (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (t.1 * t.1) * jInvariant τ)
        atImInfty (𝓝 (0 : ℂ)) := by
      convert hz.mul hbase using 1
      · funext τ
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hgt)]
      · simp only [zero_mul]
    simpa only [max_eq_right (Nat.le_of_lt hgt), ite_eq_left hgt, mul_sub, zero_sub] using
      hsmall.sub hroot

/-- The actual diagonal root product has the stated normalized cusp limit. -/
theorem tendsto_cyclicSublatticeDiagonal {N : ℕ} (hN : 0 < N) (hns : ¬ IsSquare N) :
    Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ cyclicSublatticeDiagonalPoleOrder N *
        (cyclicSublatticePolynomial N τ).eval (jInvariant τ))
      atImInfty (𝓝 (cyclicSublatticeDiagonalConstant N)) := by
  classical
  have h := tendsto_finsetProd (cyclicSublatticeTriples N)
    (fun t ht => tendsto_cyclicSublatticeDiagonalFactor hN hns ht)
  change Tendsto _ _ (𝓝 (cyclicSublatticeDiagonalConstant N)) at h
  convert h using 1
  funext τ
  simp only [cyclicSublatticePolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, cyclicSublatticeDiagonalPoleOrder]

/-- The finite product of the dominant phase constants has complex norm one. -/
theorem norm_cyclicSublatticeDiagonalConstant (N : ℕ) :
    ‖cyclicSublatticeDiagonalConstant N‖ = 1 := by
  classical
  unfold cyclicSublatticeDiagonalConstant
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro t _
  split_ifs <;> simp [norm_cyclicSublatticePhase]

/-- In particular the diagonal leading constant cannot vanish. -/
theorem cyclicSublatticeDiagonalConstant_ne_zero (N : ℕ) :
    cyclicSublatticeDiagonalConstant N ≠ 0 := by
  intro h
  have hn := norm_cyclicSublatticeDiagonalConstant N
  simp [h] at hn

end BakerHeegnerStark
