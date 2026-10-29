/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.QExpansion
import BakerHeegnerStark.ModularForms.Gamma.CyclicModularity
import BakerHeegnerStark.ModularForms.ModularPolynomial.QExpansion

/-!
# Common-Width Expansions of Twisted Gamma Roots

At levels congruent to two modulo three the actual gamma multipliers reduce
from a 3d-th root to a d-th root. The common-width pole order is integral.
The two complete integer gamma numerator series then give a convergent series
for each actual twisted root with algebraically integral coefficients.
-/

open UpperHalfPlane ModularForm
namespace BakerHeegnerStark

/-- The integral pole order of a twisted gamma root in the common width-N parameter. -/
def cyclicSublatticeGammaPoleOrder (N : ℕ) (t : ℕ × ℕ × ℕ) : ℕ :=
  (N + t.1 * t.1) / 3

private theorem gammaCommonWidth_pos {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) : 0 < t.1 ∧ 0 < t.2.2 := by
  obtain ⟨had, hbd, _⟩ := (mem_cyclicSublatticeTriples hN).mp ht
  have hd : 0 < t.2.2 := by omega
  have ha : 0 < t.1 := by
    by_contra h
    have hz : t.1 = 0 := by omega
    simp [hz] at had
    omega
  exact ⟨ha, hd⟩

/-- The cube-root pole orders become integral precisely at these levels. -/
theorem cyclicSublatticeGammaPoleOrder_mul_three {N : ℕ}
    (hN : 0 < N) (hN3 : N % 3 = 2) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) :
    cyclicSublatticeGammaPoleOrder N t * 3 = N + t.1 * t.1 := by
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  have ha3 : t.1 % 3 ≠ 0 := by
    intro h
    rw [← had, Nat.mul_mod, h, zero_mul, Nat.zero_mod] at hN3
    omega
  have ha : t.1 % 3 = 1 ∨ t.1 % 3 = 2 := by omega
  have hmod : (N + t.1 * t.1) % 3 = 0 := by
    rcases ha with ha | ha <;> norm_num [Nat.add_mod, Nat.mul_mod, hN3, ha]
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)

/-- The residual phase has order dividing d, not 3d. -/
noncomputable def cyclicSublatticeGammaPhase (N : ℕ) (t : ℕ × ℕ × ℕ) : ℂ :=
  (cyclicSublatticePhase t.2.1 t.2.2 ^ ((N + 1) / 3))⁻¹

/-- Normalizing in the common width cancels the extra cubic-root phase. -/
theorem qParam_mul_cyclicSublatticeGammaPhase {N : ℕ}
    (hN : 0 < N) (hN3 : N % 3 = 2) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ cyclicSublatticeGammaPoleOrder N t *
        gammaPhaseThree ^ (t.1 * t.2.1) =
      cyclicSublatticeGammaPhase N t *
        Function.Periodic.qParam 3 (τ : ℂ) *
        Function.Periodic.qParam 3 (cyclicSublatticePoint t τ : ℂ) := by
  obtain ⟨ha, hd⟩ := gammaCommonWidth_pos hN ht
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  have hAd : (t.1 : ℂ) * (t.2.2 : ℂ) = (N : ℂ) := by exact_mod_cast had
  have hL : (cyclicSublatticeGammaPoleOrder N t : ℂ) * 3 =
      (N : ℂ) + (t.1 : ℂ) * (t.1 : ℂ) := by
    exact_mod_cast cyclicSublatticeGammaPoleOrder_mul_three hN hN3 ht
  have hK : (((N + 1) / 3 : ℕ) : ℂ) * 3 = (N : ℂ) + 1 := by
    have h := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (show (N + 1) % 3 = 0 by omega))
    exact_mod_cast h
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hdC : (t.2.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hinner : (cyclicSublatticeGammaPoleOrder N t : ℂ) * (τ : ℂ) / N -
      (t.1 : ℂ) * t.2.1 / 3 =
      -(((N + 1) / 3 : ℕ) : ℂ) * t.2.1 / t.2.2 + (τ : ℂ) / 3 +
        ((t.1 : ℂ) * (τ : ℂ) + t.2.1) / (3 * t.2.2) := by
    field_simp [hNC, hdC]
    linear_combination
      (t.2.2 : ℂ) * (τ : ℂ) * hL +
      (N : ℂ) * t.2.1 * hK +
      ((t.1 : ℂ) * (τ : ℂ) - (N : ℂ) * t.2.1) * hAd
  rw [cyclicSublatticePoint_coe ha hd]
  simp only [Function.Periodic.qParam, cyclicSublatticeGammaPhase, gammaPhaseThree,
    cyclicSublatticePhase, Complex.ofReal_natCast, ← Complex.exp_nat_mul,
    ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (2 * Real.pi * Complex.I) * hinner


/-- The residual root phase is nonzero. -/
theorem cyclicSublatticeGammaPhase_ne_zero (N : ℕ) (t : ℕ × ℕ × ℕ) :
    cyclicSublatticeGammaPhase N t ≠ 0 :=
  inv_ne_zero (pow_ne_zero _ (cyclicSublatticePhase_ne_zero _ _))

/-- The residual phase is a d-th root of unity. -/
theorem cyclicSublatticeGammaPhase_pow (N : ℕ) (t : ℕ × ℕ × ℕ) (hd : 0 < t.2.2) :
    cyclicSublatticeGammaPhase N t ^ t.2.2 = 1 := by
  rw [cyclicSublatticeGammaPhase, inv_pow, ← pow_mul,
    Nat.mul_comm ((N + 1) / 3) t.2.2, pow_mul, cyclicSublatticePhase_pow hd,
    one_pow, inv_one]

/-- The residual phase is integral by finite order, not by division closure. -/
theorem isIntegral_cyclicSublatticeGammaPhase (N : ℕ) (t : ℕ × ℕ × ℕ) (hd : 0 < t.2.2) :
    IsIntegral ℤ (cyclicSublatticeGammaPhase N t) := by
  rw [cyclicSublatticeGammaPhase, ← inv_pow]
  exact (isIntegral_cyclicSublatticePhase_inv hd).pow _

/-- The normalized actual root is the product of the two regularized gamma values. -/
theorem qParam_pow_mul_cyclicSublatticeGammaRoot {N : ℕ}
    (hN : 0 < N) (hN3 : N % 3 = 2) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ cyclicSublatticeGammaPoleOrder N t *
        cyclicSublatticeGammaRoot t τ =
      cyclicSublatticeGammaPhase N t *
        (Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ) *
        (Function.Periodic.qParam 3 (cyclicSublatticePoint t τ : ℂ) *
          gamma₂ (cyclicSublatticePoint t τ)) := by
  rw [cyclicSublatticeGammaRoot]
  linear_combination (gamma₂ τ * gamma₂ (cyclicSublatticePoint t τ)) *
    qParam_mul_cyclicSublatticeGammaPhase hN hN3 ht τ

/-- The ordinary parameter is the N-th power of the common-width parameter. -/
theorem qParam_one_commonWidth {N : ℕ} (hN : 0 < N) (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (τ : ℂ) =
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ N := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one,
    Complex.ofReal_natCast, ← Complex.exp_nat_mul]
  congr 1
  field_simp [hNC]

/-- Both factors in a normalized twisted root use powers of one common parameter. -/
theorem qParam_cyclicSublatticePoint_commonWidth {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (cyclicSublatticePoint t τ : ℂ) =
      cyclicSublatticePhase t.2.1 t.2.2 *
        Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (t.1 * t.1) := by
  obtain ⟨ha, hd⟩ := gammaCommonWidth_pos hN ht
  rw [qParam_cyclicSublatticePoint ha hd, qParam_cyclicSublattice_commonWidth hN ht,
    ← pow_mul]


/-- The full common-width series of a normalized actual twisted gamma root. -/
noncomputable def cyclicSublatticeGammaRootQExpansion {N : ℕ} (hN : 0 < N)
    (t : ℕ × ℕ × ℕ) (ha : 0 < t.1) : PowerSeries ℂ :=
  PowerSeries.C (cyclicSublatticeGammaPhase N t) *
    (PowerSeries.expand N (Nat.ne_of_gt hN)
      (PowerSeries.map (Int.castRingHom ℂ) gammaIntegralNumerator) *
    PowerSeries.expand (t.1 * t.1) (Nat.mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt ha))
      (PowerSeries.rescale (cyclicSublatticePhase t.2.1 t.2.2)
        (PowerSeries.map (Int.castRingHom ℂ) gammaIntegralNumerator)))

/-- The normalized principal coefficient is the exact residual d-th-root phase. -/
theorem cyclicSublatticeGammaRootQExpansion_constantCoeff {N : ℕ} (hN : 0 < N)
    (t : ℕ × ℕ × ℕ) (ha : 0 < t.1) :
    (cyclicSublatticeGammaRootQExpansion hN t ha).constantCoeff =
      cyclicSublatticeGammaPhase N t := by
  have hc : (PowerSeries.map (Int.castRingHom ℂ) gammaIntegralNumerator).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, gammaIntegralNumerator_constantCoeff, map_one]
  have hr : (PowerSeries.rescale (cyclicSublatticePhase t.2.1 t.2.2)
      (PowerSeries.map (Int.castRingHom ℂ) gammaIntegralNumerator)).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
      pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff, hc]
  simp [cyclicSublatticeGammaRootQExpansion, hc, hr]

private theorem gamma_isIntegral_expand_coeff (p : ℕ) (hp : p ≠ 0)
    (P : PowerSeries ℂ) (hP : ∀ m, IsIntegral ℤ (P.coeff m)) (m : ℕ) :
    IsIntegral ℤ ((PowerSeries.expand p hp P).coeff m) := by
  by_cases hm : p ∣ m
  · obtain ⟨n, rfl⟩ := hm
    rw [PowerSeries.coeff_expand_mul]
    exact hP n
  · rw [PowerSeries.coeff_expand_of_not_dvd p hp P hm]
    exact isIntegral_zero

/-- Every common-width coefficient is an algebraic integer, including inserted
zeros and the Cauchy products of the two complete integer numerator series. -/
theorem isIntegral_cyclicSublatticeGammaRootQExpansion_coeff {N : ℕ} (hN : 0 < N)
    (t : ℕ × ℕ × ℕ) (ha : 0 < t.1) (hd : 0 < t.2.2) (m : ℕ) :
    IsIntegral ℤ ((cyclicSublatticeGammaRootQExpansion hN t ha).coeff m) := by
  have hB : ∀ n, IsIntegral ℤ
      ((PowerSeries.map (Int.castRingHom ℂ) gammaIntegralNumerator).coeff n) := by
    intro n
    rw [PowerSeries.coeff_map]
    exact isIntegral_intCast _
  have hR : ∀ n, IsIntegral ℤ ((PowerSeries.rescale (cyclicSublatticePhase t.2.1 t.2.2)
      (PowerSeries.map (Int.castRingHom ℂ) gammaIntegralNumerator)).coeff n) := by
    intro n
    rw [PowerSeries.coeff_rescale]
    exact ((isIntegral_cyclicSublatticePhase hd).pow n).mul (hB n)
  rw [cyclicSublatticeGammaRootQExpansion, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul]
  exact (isIntegral_cyclicSublatticeGammaPhase N t hd).mul
    (IsIntegral.sum _ (fun ij _ =>
      (gamma_isIntegral_expand_coeff N (Nat.ne_of_gt hN) _ hB ij.1).mul
        (gamma_isIntegral_expand_coeff (t.1 * t.1)
          (Nat.mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt ha)) _ hR ij.2)))

/-- The entire common-width series converges to the actual normalized twisted
root at every upper-half-plane point. No finite coefficient approximation is used. -/
theorem hasSum_cyclicSublatticeGammaRootQExpansion {N : ℕ} (hN : 0 < N)
    (hN3 : N % 3 = 2) {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N)
    (ha : 0 < t.1) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => (cyclicSublatticeGammaRootQExpansion hN t ha).coeff m *
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ m)
      (Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ cyclicSublatticeGammaPoleOrder N t *
        cyclicSublatticeGammaRoot t τ) := by
  have h0 := hasSum_gammaIntegralNumerator τ
  rw [qParam_one_commonWidth hN τ] at h0
  have hBase : HasSum (fun m : ℕ =>
      (PowerSeries.expand N (Nat.ne_of_gt hN)
        (PowerSeries.map (Int.castRingHom ℂ) gammaIntegralNumerator)).coeff m *
          Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ m)
      (Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ) := by
    apply hasSum_powerSeries_expand
    simpa only [PowerSeries.coeff_map, Int.coe_castRingHom, ← pow_mul] using h0
  have h1 := hasSum_gammaIntegralNumerator (cyclicSublatticePoint t τ)
  rw [qParam_cyclicSublatticePoint_commonWidth hN ht τ] at h1
  have hTrans : HasSum (fun m : ℕ =>
      (PowerSeries.expand (t.1 * t.1) (Nat.mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt ha))
        (PowerSeries.rescale (cyclicSublatticePhase t.2.1 t.2.2)
          (PowerSeries.map (Int.castRingHom ℂ) gammaIntegralNumerator))).coeff m *
            Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ m)
      (Function.Periodic.qParam 3 (cyclicSublatticePoint t τ : ℂ) *
        gamma₂ (cyclicSublatticePoint t τ)) := by
    apply hasSum_powerSeries_expand
    convert h1 using 1
    funext n
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_map, Int.coe_castRingHom,
      mul_pow, ← pow_mul]
    ring
  have h := HasSum.mul_left (cyclicSublatticeGammaPhase N t)
    (PowerSeries.hasSum_coeff_mul hBase hTrans)
  rw [qParam_pow_mul_cyclicSublatticeGammaRoot hN hN3 ht τ]
  unfold cyclicSublatticeGammaRootQExpansion
  simpa only [PowerSeries.coeff_C_mul, mul_assoc] using h

end BakerHeegnerStark
