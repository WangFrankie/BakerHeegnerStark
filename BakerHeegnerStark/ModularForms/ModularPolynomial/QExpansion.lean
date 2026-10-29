/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.QExpansion.Cyclotomic
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Common-width q-Expansions of Cyclic-Sublattice Roots

At level `N`, all cyclic-sublattice transforms admit full convergent power
series in the single parameter `qParam N τ`. Their translation phases are
powers of the same `N`-th root of unity, and their normalized coefficients are
algebraic integers. These individual-root expansions do not assert integrality
or Galois descent of the finite symmetric product.
-/

open UpperHalfPlane ModularForm

noncomputable section

namespace BakerHeegnerStark

private theorem cyclicSublatticeRoot_pos {N : ℕ} (hN : 0 < N)
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

/-- The width-`d` parameter is the `a`-th power of the common width-`N`
parameter when `ad = N`. -/
theorem qParam_cyclicSublattice_commonWidth {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    Function.Periodic.qParam (t.2.2 : ℝ) (τ : ℂ) =
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ t.1 := by
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  obtain ⟨ha, hd⟩ := cyclicSublatticeRoot_pos hN ht
  have haC : (t.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hdC : (t.2.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  rw [← had]
  simp only [Function.Periodic.qParam, Nat.cast_mul, Complex.ofReal_mul,
    Complex.ofReal_natCast, ← Complex.exp_nat_mul]
  congr 1
  field_simp [haC, hdC]

/-- Every translation phase is a power of one common `N`-th root of unity. -/
theorem cyclicSublatticePhase_commonRoot {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) :
    cyclicSublatticePhase t.2.1 t.2.2 =
      cyclicSublatticePhase 1 N ^ (t.1 * t.2.1) := by
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  obtain ⟨ha, hd⟩ := cyclicSublatticeRoot_pos hN ht
  have haC : (t.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hdC : (t.2.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  rw [← had]
  simp only [cyclicSublatticePhase, Nat.cast_mul, Nat.cast_one, mul_one,
    ← Complex.exp_nat_mul]
  congr 1
  field_simp [haC, hdC]

/-- Inserting zero coefficients between the coefficients of a power series
preserves its actual infinite sum after the corresponding exponent change. -/
theorem hasSum_powerSeries_expand {p : ℕ} (hp : p ≠ 0)
    {f : PowerSeries ℂ} {q s : ℂ}
    (h : HasSum (fun n : ℕ => f.coeff n * q ^ (p * n)) s) :
    HasSum (fun m : ℕ => (PowerSeries.expand p hp f).coeff m * q ^ m) s := by
  have hinj : Function.Injective (fun n : ℕ => p * n) :=
    mul_right_injective₀ hp
  apply (hinj.hasSum_iff ?_).mp
  · change HasSum (fun n : ℕ =>
      (PowerSeries.expand p hp f).coeff (p * n) * q ^ (p * n)) s
    simpa only [PowerSeries.coeff_expand_mul] using h
  · intro m hm
    have hndvd : ¬ p ∣ m := by
      rintro ⟨n, rfl⟩
      exact hm ⟨n, rfl⟩
    rw [PowerSeries.coeff_expand_of_not_dvd p hp f hndvd, zero_mul]

/-- The genuine normalized root series in the common-width variable. The
positive `a` is needed for the power-series substitution `X ↦ X^(a*a)`. -/
def cyclicSublatticeRootQExpansion (t : ℕ × ℕ × ℕ) (ha : 0 < t.1) :
    PowerSeries ℂ :=
  PowerSeries.C (cyclicSublatticePhase t.2.1 t.2.2)⁻¹ *
    PowerSeries.expand (t.1 * t.1)
      (Nat.mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt ha))
      (PowerSeries.rescale (cyclicSublatticePhase t.2.1 t.2.2)
        (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator))

/-- At each sparse index `a*a*n`, the coefficient is the original integral
numerator coefficient times the appropriate finite-order phase. -/
theorem cyclicSublatticeRootQExpansion_coeff_mul (t : ℕ × ℕ × ℕ)
    (ha : 0 < t.1) (n : ℕ) :
    (cyclicSublatticeRootQExpansion t ha).coeff (t.1 * t.1 * n) =
      ((jInvariantIntegralNumerator.coeff n : ℂ) *
        cyclicSublatticePhase t.2.1 t.2.2 ^ n) /
        cyclicSublatticePhase t.2.1 t.2.2 := by
  simp only [cyclicSublatticeRootQExpansion, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_expand_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_map,
    Int.coe_castRingHom, div_eq_mul_inv]
  ring

/-- All indices not divisible by `a*a` have zero coefficient. -/
theorem cyclicSublatticeRootQExpansion_coeff_of_not_dvd (t : ℕ × ℕ × ℕ)
    (ha : 0 < t.1) {m : ℕ} (hm : ¬ t.1 * t.1 ∣ m) :
    (cyclicSublatticeRootQExpansion t ha).coeff m = 0 := by
  simp only [cyclicSublatticeRootQExpansion, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_expand_of_not_dvd _ _ _ hm, mul_zero]

/-- The coefficient formula at every natural index, including all inserted
zeros. -/
theorem cyclicSublatticeRootQExpansion_coeff (t : ℕ × ℕ × ℕ)
    (ha : 0 < t.1) (m : ℕ) :
    (cyclicSublatticeRootQExpansion t ha).coeff m =
      if t.1 * t.1 ∣ m then
        ((jInvariantIntegralNumerator.coeff (m / (t.1 * t.1)) : ℂ) *
          cyclicSublatticePhase t.2.1 t.2.2 ^ (m / (t.1 * t.1))) /
          cyclicSublatticePhase t.2.1 t.2.2
      else 0 := by
  by_cases hm : t.1 * t.1 ∣ m
  · obtain ⟨n, rfl⟩ := hm
    rw [cyclicSublatticeRootQExpansion_coeff_mul]
    simp [Nat.mul_div_cancel_left n (Nat.mul_pos ha ha)]
  · rw [ite_eq_right hm, cyclicSublatticeRootQExpansion_coeff_of_not_dvd t ha hm]

/-- The nonvanishing constant coefficient records the precise normalized
principal part of the transformed j-value. -/
theorem cyclicSublatticeRootQExpansion_constantCoeff (t : ℕ × ℕ × ℕ)
    (ha : 0 < t.1) :
    (cyclicSublatticeRootQExpansion t ha).constantCoeff =
      (cyclicSublatticePhase t.2.1 t.2.2)⁻¹ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, ← mul_zero (t.1 * t.1),
    cyclicSublatticeRootQExpansion_coeff_mul]
  simp [PowerSeries.coeff_zero_eq_constantCoeff,
    jInvariantIntegralNumerator_constantCoeff]

/-- Every coefficient of the full common-width root series is an algebraic
integer, including the inserted zero coefficients. -/
theorem isIntegral_cyclicSublatticeRootQExpansion_coeff (t : ℕ × ℕ × ℕ)
    (ha : 0 < t.1) (hd : 0 < t.2.2) (m : ℕ) :
    IsIntegral ℤ ((cyclicSublatticeRootQExpansion t ha).coeff m) := by
  rw [cyclicSublatticeRootQExpansion_coeff]
  split_ifs
  · exact isIntegral_jInvariant_cyclicSublatticePoint_coeff hd _
  · exact isIntegral_zero

/-- The entire power series indexed by all `m : ℕ` converges to the actual
normalized transformed j-value, in the common parameter `qParam N τ`. -/
theorem hasSum_cyclicSublatticeRootQExpansion {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N)
    (ha : 0 < t.1) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => (cyclicSublatticeRootQExpansion t ha).coeff m *
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ m)
      (Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (t.1 * t.1) *
        jInvariant (cyclicSublatticePoint t τ)) := by
  have hd := (cyclicSublatticeRoot_pos hN ht).2
  have h := hasSum_jInvariant_cyclicSublatticePoint ha hd τ
  rw [qParam_cyclicSublattice_commonWidth hN ht] at h
  simp only [← pow_mul] at h
  have heq : cyclicSublatticeRootQExpansion t ha =
      PowerSeries.expand (t.1 * t.1)
        (Nat.mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt ha))
        (PowerSeries.C (cyclicSublatticePhase t.2.1 t.2.2)⁻¹ *
          PowerSeries.rescale (cyclicSublatticePhase t.2.1 t.2.2)
            (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator)) := by
    simp only [cyclicSublatticeRootQExpansion, map_mul, PowerSeries.expand_C]
  rw [heq]
  apply hasSum_powerSeries_expand
  convert h using 1
  funext n
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
    PowerSeries.coeff_map, Int.coe_castRingHom, div_eq_mul_inv]
  rw [Nat.mul_assoc]
  ring

end BakerHeegnerStark
