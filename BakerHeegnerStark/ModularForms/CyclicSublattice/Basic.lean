/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.Basic
import BakerHeegnerStark.ModularForms.QExpansion.Integral
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Analytic Behavior of Cyclic-Sublattice Transforms

For positive `a,d`, the actual map `τ ↦ (aτ+b)/d` is holomorphic and tends
up the cusp with imaginary part `a Im(τ)/d`. Its q-parameter satisfies
`q((aτ+b)/d)^d = q(τ)^a`. Together with `qj → 1`, this controls the
transformed j-values used in the general modular polynomial.
-/

open UpperHalfPlane ModularForm Filter Complex Asymptotics
open scoped Topology Manifold

noncomputable section

namespace BakerHeegnerStark

private theorem cyclicSublattice_raw_im (t : ℕ × ℕ × ℕ) (τ : UpperHalfPlane) :
    ((t.1 * (τ : ℂ) + t.2.1) / t.2.2 : ℂ).im =
      (t.1 : ℝ) * τ.im / t.2.2 := by
  simp only [← Complex.ofReal_natCast, Complex.div_ofReal_im, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rfl

private theorem cyclicSublattice_raw_im_pos {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) (τ : UpperHalfPlane) :
    0 < ((t.1 * (τ : ℂ) + t.2.1) / t.2.2 : ℂ).im := by
  rw [cyclicSublattice_raw_im]
  exact div_pos (mul_pos (Nat.cast_pos.mpr ha) τ.im_pos) (Nat.cast_pos.mpr hd)

/-- Positive upper-triangular triples give their actual affine complex point;
the arbitrary extension outside the upper half-plane is never used. -/
theorem cyclicSublatticePoint_coe {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) (τ : UpperHalfPlane) :
    (cyclicSublatticePoint t τ : ℂ) = (t.1 * (τ : ℂ) + t.2.1) / t.2.2 := by
  rw [cyclicSublatticePoint,
    UpperHalfPlane.ofComplex_apply_of_im_pos (cyclicSublattice_raw_im_pos ha hd τ)]

/-- The imaginary part is multiplied by the positive slope `a/d`. -/
theorem cyclicSublatticePoint_im {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) (τ : UpperHalfPlane) :
    (cyclicSublatticePoint t τ).im = (t.1 : ℝ) * τ.im / t.2.2 := by
  change (cyclicSublatticePoint t τ : ℂ).im = _
  rw [cyclicSublatticePoint_coe ha hd, cyclicSublattice_raw_im]

/-- The actual cyclic-sublattice transformation is holomorphic. -/
theorem mdifferentiable_cyclicSublatticePoint {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) : MDiff (cyclicSublatticePoint t) := by
  have hf : MDiff (fun τ : UpperHalfPlane =>
      (t.1 * (τ : ℂ) + t.2.1) / t.2.2 : UpperHalfPlane → ℂ) := by
    exact ((mdifferentiable_const.mul mdifferentiable_coe).add mdifferentiable_const).div
      mdifferentiable_const (fun _ => Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
  intro τ
  exact (mdifferentiableAt_ofComplex (cyclicSublattice_raw_im_pos ha hd τ)).comp τ (hf τ)

/-- Every transformed j-value is holomorphic on the whole upper half-plane. -/
theorem mdifferentiable_jInvariant_cyclicSublatticePoint {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) :
    MDiff (fun τ => jInvariant (cyclicSublatticePoint t τ)) :=
  mdifferentiable_jInvariant.comp (mdifferentiable_cyclicSublatticePoint ha hd)

/-- A positive cyclic-sublattice transformation preserves approach to the cusp. -/
theorem tendsto_cyclicSublatticePoint_atImInfty {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) :
    Tendsto (cyclicSublatticePoint t) atImInfty atImInfty := by
  change Tendsto _ atImInfty (Filter.comap UpperHalfPlane.im atTop)
  rw [Filter.tendsto_comap_iff]
  have him : Tendsto (fun τ : UpperHalfPlane => τ.im) atImInfty atTop := tendsto_comap
  have hpos : 0 < (t.1 : ℝ) / t.2.2 :=
    div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hd)
  convert Filter.Tendsto.const_mul_atTop hpos him using 1
  funext τ
  simp only [Function.comp_apply, cyclicSublatticePoint_im ha hd]
  ring

/-- The integral translation disappears after taking the `d`-th power of q. -/
theorem qParam_cyclicSublatticePoint_pow {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (cyclicSublatticePoint t τ : ℂ) ^ t.2.2 =
      Function.Periodic.qParam 1 (τ : ℂ) ^ t.1 := by
  have hdC : (t.2.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hexp : (t.2.2 : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * ((t.1 * (τ : ℂ) + t.2.1) / t.2.2)) =
      (t.1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) +
        (t.2.1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp [hdC]
  rw [cyclicSublatticePoint_coe ha hd]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
  rw [hexp, Complex.exp_add, Complex.exp_nat_mul]
  simp

/-- Exact normalized cusp growth of the transformed j-value, independent of
any modular polynomial or complex multiplication theorem. -/
theorem tendsto_qParam_pow_mul_jInvariant_cyclicSublatticePoint_pow
    {t : ℕ × ℕ × ℕ} (ha : 0 < t.1) (hd : 0 < t.2.2) :
    Tendsto (fun τ : UpperHalfPlane => Function.Periodic.qParam 1 (τ : ℂ) ^ t.1 *
      jInvariant (cyclicSublatticePoint t τ) ^ t.2.2) atImInfty (𝓝 1) := by
  have ht := (tendsto_qParam_mul_jInvariant.comp
    (tendsto_cyclicSublatticePoint_atImInfty ha hd)).pow t.2.2
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      (Function.Periodic.qParam 1 (cyclicSublatticePoint t τ : ℂ) *
        jInvariant (cyclicSublatticePoint t τ)) ^ t.2.2) atImInfty (𝓝 1) := by
    simpa only [Function.comp_apply, one_pow] using ht
  convert hlim using 1
  funext τ
  rw [mul_pow, qParam_cyclicSublatticePoint_pow ha hd]

/-- Taking the `d`-th power removes the cyclotomic leading coefficient:
`j((aτ+b)/d)^d` is asymptotic to `j(τ)^a`. -/
theorem jInvariant_cyclicSublatticePoint_pow_isEquivalent
    {t : ℕ × ℕ × ℕ} (ha : 0 < t.1) (hd : 0 < t.2.2) :
    (fun τ : UpperHalfPlane => jInvariant (cyclicSublatticePoint t τ) ^ t.2.2)
      ~[atImInfty] (fun τ : UpperHalfPlane => jInvariant τ ^ t.1) := by
  have ht := (tendsto_qParam_pow_mul_jInvariant_cyclicSublatticePoint_pow ha hd).div
    (tendsto_qParam_mul_jInvariant.pow t.1) (by simp)
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      (Function.Periodic.qParam 1 (τ : ℂ) ^ t.1 *
        jInvariant (cyclicSublatticePoint t τ) ^ t.2.2) /
      (Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ) ^ t.1)
      atImInfty (𝓝 1) := by
    change Tendsto (fun τ : UpperHalfPlane =>
      (Function.Periodic.qParam 1 (τ : ℂ) ^ t.1 *
        jInvariant (cyclicSublatticePoint t τ) ^ t.2.2) /
      (Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ) ^ t.1)
      atImInfty (𝓝 ((1 : ℂ) / 1 ^ t.1)) at ht
    simpa only [one_pow, div_one] using ht
  apply isEquivalent_of_tendsto_one
  convert hlim using 1
  funext τ
  rw [mul_pow, mul_div_mul_left _ _
    (pow_ne_zero _ (Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ)))]
  simp only [Pi.div_apply]

/-- The actual j-value eventually has norm at least one at the cusp. -/
theorem eventually_one_le_norm_jInvariant :
    ∀ᶠ τ : UpperHalfPlane in atImInfty, 1 ≤ ‖jInvariant τ‖ := by
  have hj : ∀ᶠ τ : UpperHalfPlane in atImInfty, (1 / 2 : ℝ) ≤
      ‖Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ‖ :=
    tendsto_qParam_mul_jInvariant.norm.eventually_const_le (by norm_num)
  have hq : ∀ᶠ τ : UpperHalfPlane in atImInfty,
      ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ≤ (1 / 2 : ℝ) :=
    (qParam_tendsto_atImInfty one_pos).norm.eventually_le_const (by norm_num)
  filter_upwards [hj, hq] with τ hj hq
  rw [norm_mul] at hj
  have hprod := mul_le_mul_of_nonneg_right hq (norm_nonneg (jInvariant τ))
  nlinarith

/-- Any integral exponent above the affine slope gives a polynomial j-growth
bound for the corresponding transformed j-value. -/
theorem isBigO_jInvariant_cyclicSublatticePoint
    {t : ℕ × ℕ × ℕ} (ha : 0 < t.1) (hd : 0 < t.2.2)
    (m : ℕ) (hm : t.1 ≤ m * t.2.2) :
    (fun τ : UpperHalfPlane => jInvariant (cyclicSublatticePoint t τ))
      =O[atImInfty] (fun τ : UpperHalfPlane => jInvariant τ ^ m) := by
  have hpow : (fun τ : UpperHalfPlane => jInvariant τ ^ t.1)
      =O[atImInfty] (fun τ : UpperHalfPlane => jInvariant τ ^ (m * t.2.2)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_one_le_norm_jInvariant] with τ hτ
    simpa only [norm_pow, one_mul] using pow_le_pow_right₀ hτ hm
  have hcomp := (jInvariant_cyclicSublatticePoint_pow_isEquivalent ha hd).isBigO.trans hpow
  apply IsBigO.of_pow (n := t.2.2) (Nat.ne_of_gt hd)
  have hleft : (fun τ : UpperHalfPlane => jInvariant (cyclicSublatticePoint t τ)) ^ t.2.2 =
      fun τ : UpperHalfPlane => jInvariant (cyclicSublatticePoint t τ) ^ t.2.2 := by
    funext τ
    exact Pi.pow_apply _ _ _
  have hright : (fun τ : UpperHalfPlane => jInvariant τ ^ m) ^ t.2.2 =
      fun τ : UpperHalfPlane => jInvariant τ ^ (m * t.2.2) := by
    funext τ
    rw [Pi.pow_apply, ← pow_mul]
  rw [hleft, hright]
  exact hcomp

/-- Every actual level-N cyclic-sublattice root grows at most as `j^N`. -/
theorem isBigO_jInvariant_of_mem_cyclicSublatticeTriples
    {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) :
    (fun τ : UpperHalfPlane => jInvariant (cyclicSublatticePoint t τ))
      =O[atImInfty] (fun τ : UpperHalfPlane => jInvariant τ ^ N) := by
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  have hpos : 0 < t.1 * t.2.2 := by omega
  have ha : 0 < t.1 := by
    by_contra h
    have hz : t.1 = 0 := by omega
    simp [hz] at hpos
  have hd : 0 < t.2.2 := by
    by_contra h
    have hz : t.2.2 = 0 := by omega
    simp [hz] at hpos
  have haN : t.1 ≤ N := by
    nlinarith [Nat.mul_le_mul_left t.1 (Nat.succ_le_of_lt hd)]
  have hNN : N ≤ N * t.2.2 := by
    nlinarith [Nat.mul_le_mul_left N (Nat.succ_le_of_lt hd)]
  exact isBigO_jInvariant_cyclicSublatticePoint ha hd N (haN.trans hNN)

end BakerHeegnerStark
