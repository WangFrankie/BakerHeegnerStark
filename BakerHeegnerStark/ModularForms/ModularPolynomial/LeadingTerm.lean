/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.QExpansion.PolynomialAnalytic

/-!
# Leading Terms of Polynomials in the Modular Invariant

The full regularized q-expansion identifies the leading coefficient of a
polynomial in `j` with its normalized limit at the cusp. Conversely, a nonzero
normalized limit determines both the normalization exponent and the leading
coefficient.
-/

noncomputable section

open Filter Polynomial UpperHalfPlane
open scoped Topology

namespace Polynomial

/-- The constant term of a positive-width regularization recovers the final
coefficient, without any degree bound on the polynomial. -/
theorem qRegularization_constantCoeff {R : Type*} [CommRing R]
    (P : R[X]) (J : PowerSeries R) (hJ : J.constantCoeff = 1)
    (w n : ℕ) (hw : 0 < w) :
    (P.qRegularization J w n).constantCoeff = P.coeff n := by
  classical
  have h := P.qRegularization_coeff J w n hw (le_refl n)
  rw [Nat.sub_self, mul_zero] at h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  rw [Finset.sum_eq_single n]
  · simp [PowerSeries.coeff_zero_eq_constantCoeff, hJ]
  · intro i hi hin
    have hni : ¬n ≤ i := by
      have := Finset.mem_range.mp hi
      omega
    simp [hni]
  · simp

end Polynomial

namespace BakerHeegnerStark

/-- Normalizing a polynomial in `j` by its pole order gives its leading
coefficient as the limit at the cusp, also for the zero polynomial. -/
theorem tendsto_qParam_natDegree_mul_polynomial_jInvariant {N : ℕ} (hN : 0 < N)
    (P : ℂ[X]) :
    Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (N * P.natDegree) *
        P.eval (ModularForm.jInvariant τ)) atImInfty (nhds P.leadingCoeff) := by
  let J : PowerSeries ℂ := PowerSeries.expand N (Nat.ne_of_gt hN)
    (PowerSeries.map (Int.castRingHom ℂ) ModularForm.jInvariantIntegralNumerator)
  have hJ : J.constantCoeff = 1 := by
    dsimp only [J]
    rw [PowerSeries.constantCoeff_expand,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff,
      ModularForm.jInvariantIntegralNumerator_constantCoeff, map_one]
  have hsum (τ : UpperHalfPlane) := P.hasSum_qRegularization J N P.natDegree
    (le_refl _) (Function.Periodic.qParam (N : ℝ) (τ : ℂ))
    (ModularForm.jInvariant τ)
    (ModularForm.hasSum_jInvariantIntegralNumerator_commonWidth hN τ)
  have hlim := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion
    (c := fun m => (P.qRegularization J N P.natDegree).coeff m)
    (Nat.cast_pos.mpr hN) (by simpa only [smul_eq_mul] using hsum)
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff,
    Polynomial.qRegularization_constantCoeff P J hJ N P.natDegree hN,
    Polynomial.coeff_natDegree] using hlim

/-- A nonzero normalized cusp limit determines the pole order and the leading
coefficient of a polynomial in `j`. -/
theorem leadingCoeff_eq_of_tendsto_qParam_mul_polynomial_jInvariant {N : ℕ}
    (hN : 0 < N) (P : ℂ[X]) (D : ℕ) (c : ℂ) (hc : c ≠ 0)
    (hlim : Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ D *
        P.eval (ModularForm.jInvariant τ)) atImInfty (nhds c)) :
    N * P.natDegree = D ∧ P.leadingCoeff = c := by
  have hP : P ≠ 0 := by
    intro hP
    subst P
    simp only [Polynomial.eval_zero, mul_zero] at hlim
    exact hc (tendsto_nhds_unique hlim tendsto_const_nhds)
  have hlead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hnorm := tendsto_qParam_natDegree_mul_polynomial_jInvariant hN P
  have hq := UpperHalfPlane.qParam_tendsto_atImInfty (Nat.cast_pos.mpr hN)
  rcases lt_trichotomy (N * P.natDegree) D with hlt | heq | hgt
  · have hpow : Tendsto (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (D - N * P.natDegree))
        atImInfty (nhds (0 : ℂ)) := by
      simpa only [zero_pow (Nat.sub_pos_of_lt hlt).ne'] using
        hq.pow (D - N * P.natDegree)
    have hz := hpow.mul hnorm
    have hfun : (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (D - N * P.natDegree) *
          (Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (N * P.natDegree) *
            P.eval (ModularForm.jInvariant τ))) =
        (fun τ : UpperHalfPlane => Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ D *
          P.eval (ModularForm.jInvariant τ)) := by
      funext τ
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le]
    change Tendsto _ atImInfty (nhds (0 * P.leadingCoeff)) at hz
    rw [hfun, zero_mul] at hz
    exact (hc (tendsto_nhds_unique hlim hz)).elim
  · refine ⟨heq, ?_⟩
    rw [heq] at hnorm
    exact tendsto_nhds_unique hnorm hlim
  · have hpow : Tendsto (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (N * P.natDegree - D))
        atImInfty (nhds (0 : ℂ)) := by
      simpa only [zero_pow (Nat.sub_pos_of_lt hgt).ne'] using
        hq.pow (N * P.natDegree - D)
    have hz := hpow.mul hlim
    have hfun : (fun τ : UpperHalfPlane =>
        Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (N * P.natDegree - D) *
          (Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ D *
            P.eval (ModularForm.jInvariant τ))) =
        (fun τ : UpperHalfPlane =>
          Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (N * P.natDegree) *
            P.eval (ModularForm.jInvariant τ)) := by
      funext τ
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hgt.le]
    change Tendsto _ atImInfty (nhds (0 * c)) at hz
    rw [hfun, zero_mul] at hz
    exact (hlead (tendsto_nhds_unique hnorm hz)).elim

end BakerHeegnerStark
