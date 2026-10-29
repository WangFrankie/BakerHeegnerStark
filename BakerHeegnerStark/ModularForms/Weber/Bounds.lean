/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Weber Values Used in Heegner's Argument

The normalized gamma value at `(z + 3) / 2` is a rational function of the
Weber value `𝔣(z)`. On the positive imaginary axis the product expansion of
`𝔣` gives two-sided exponential bounds. These are analytic identities and
estimates; no arithmetic property of singular values is used.
The actual Weber cubic also gives a global twenty-fourth-power norm bound
uniform under all modular transformations. Together with the principal part
of `j`, this controls the Weber square at every cusp.
-/

open Complex
open scoped Real MatrixGroups

namespace ModularForm

/-- The actual Weber cubic bounds its twenty-fourth power using the actual `j`-value. -/
theorem norm_weberF_pow_24_sq_le (τ : UpperHalfPlane) :
    ‖weberF (τ : ℂ) ^ 24‖ ^ 2 ≤ 1024 + 8 * ‖jInvariant τ‖ := by
  let s := ‖weberF (τ : ℂ) ^ 24‖
  let a := ‖weberF (τ : ℂ) ^ 24 - 16‖
  let J := ‖jInvariant τ‖
  change s ^ 2 ≤ 1024 + 8 * J
  have hs0 : 0 ≤ s := norm_nonneg _
  have hJ : 0 ≤ J := norm_nonneg _
  have hcube : a ^ 3 = J * s := by
    simpa only [a, J, s, norm_pow, norm_mul] using congrArg norm (weberF_cubic τ)
  have htri : s ≤ a + 16 := by
    calc
      s = ‖(weberF (τ : ℂ) ^ 24 - 16) + (16 : ℂ)‖ := by simp [s]
      _ ≤ ‖weberF (τ : ℂ) ^ 24 - 16‖ + ‖(16 : ℂ)‖ := Complex.norm_add_le' _ _
      _ = a + 16 := by norm_num [a]
  by_cases hs : s ≤ 32
  · nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs)]
  · have hspos : 0 < s := by linarith
    have hhalf : s / 2 ≤ a := by linarith
    have hpow : (s / 2) ^ 3 ≤ a ^ 3 :=
      pow_le_pow_left₀ (by positivity) hhalf 3
    have hsq : s ^ 2 ≤ 8 * J := by
      apply (mul_le_mul_iff_right₀ hspos).mp
      nlinarith [hcube, hpow]
    linarith

/-- A uniform norm bound after every modular transformation, without selecting roots. -/
theorem norm_weberF_sq_smul_pow_24_le (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ‖weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2‖ ^ 24 ≤ 1024 + 8 * ‖jInvariant τ‖ := by
  simpa only [norm_pow, ← pow_mul, jInvariant_smul] using
    norm_weberF_pow_24_sq_le (g • τ)

/-- Shifting by three half-periods expresses gamma through Weber's `𝔣`:
`γ₂((z + 3)/2) = (256 - 𝔣(z)²⁴)/𝔣(z)¹⁶`. -/
theorem gamma₂_half_add_three_eq_weberF {z : ℂ} (hz : 0 < z.im) :
    gamma₂ (UpperHalfPlane.ofComplex ((z + 3) / 2)) =
      (256 - weberF z ^ 24) / weberF z ^ 16 := by
  have hτim : 0 < ((z + 3) / 2).im := by
    have : ((z + 3) / 2).im = z.im / 2 := by simp
    rw [this]
    positivity
  have hτ : ((UpperHalfPlane.ofComplex ((z + 3) / 2) : UpperHalfPlane) : ℂ) = (z + 3) / 2 :=
    congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos hτim)
  rw [gamma₂_eq_weberF₂, hτ]
  have hprod := weberF₁_two_mul_mul_weberF₂ hτim
  rw [show 2 * ((z + 3) / 2) = z + 1 + 1 + 1 by ring, weberF₁_add_one, weberF_add_one,
    weberF₁_add_one] at hprod
  have hf : weberF z ≠ 0 := weberF_ne_zero hz
  have hζ : zeta48 ≠ 0 := zeta48_ne_zero
  have hζ24 : zeta48 ^ 24 = -1 := by
    rw [zeta48, ← Complex.exp_nat_mul,
      show ((24 : ℕ) : ℂ) * (2 * π * I / 48) = π * I by push_cast; ring]
    exact Complex.exp_pi_mul_I
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hg : weberF₂ ((z + 3) / 2) = (Real.sqrt 2 : ℂ) * zeta48 ^ 3 / weberF z := by
    rw [eq_div_iff hf, ← hprod]
    field_simp
  have hg8 : weberF₂ ((z + 3) / 2) ^ 8 = -16 / weberF z ^ 8 := by
    rw [hg, div_pow, mul_pow, ← pow_mul, show (2 : ℝ) = 2 by rfl,
      show ((Real.sqrt 2 : ℝ) : ℂ) ^ 8 = (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) ^ 4 by ring, hs2, hζ24]
    norm_num
  rw [show weberF₂ ((z + 3) / 2) ^ 24 = (weberF₂ ((z + 3) / 2) ^ 8) ^ 3 by ring, hg8]
  field_simp
  ring

/-- Heegner's actual Weber value `v = 2/𝔣(z)²` satisfies the cubic equation
in its fourth power, with the normalized gamma value as coefficient. -/
theorem weberF_fourthPower_cubic {z : ℂ} (hz : 0 < z.im) :
    ((2 / weberF z ^ 2) ^ 4) ^ 3 -
      gamma₂ (UpperHalfPlane.ofComplex ((z + 3) / 2)) * (2 / weberF z ^ 2) ^ 4 - 16 = 0 := by
  rw [gamma₂_half_add_three_eq_weberF hz]
  have hf := weberF_ne_zero hz
  field_simp
  ring

/-- The actual j-value is a rational function of Heegner's fourth-power quantity. -/
theorem jInvariant_mul_weberFourthPower_pow_six (τ : UpperHalfPlane) :
    jInvariant τ * ((2 / weberF (τ : ℂ) ^ 2) ^ 4) ^ 6 =
      (256 - ((2 / weberF (τ : ℂ) ^ 2) ^ 4) ^ 3) ^ 3 := by
  rw [jInvariant_eq_weberF τ]
  field_simp [weberF_ne_zero τ.im_pos]
  ring

/-- The real product expansion of `𝔣` on the positive imaginary axis. -/
theorem weberF_mul_I_eq_tprod (y : ℝ) (hy : 0 < y) :
    weberF ((y : ℂ) * I) =
      ((Real.exp (π * y / 24) *
        ∏' n : ℕ, (1 + Real.exp (-(π * y)) ^ (2 * n + 1)) : ℝ) : ℂ) := by
  set r := Real.exp (-(π * y)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hsum : Summable (fun n : ℕ ↦ r ^ (2 * n + 1)) := by
    have hr2 : r ^ 2 < 1 := by nlinarith
    refine ((summable_geometric_of_lt_one (by positivity) hr2).mul_left r).congr fun n => ?_
    ring
  have hprod : Multipliable (fun n : ℕ ↦ 1 + r ^ (2 * n + 1)) :=
    Real.multipliable_one_add_of_summable hsum
  have hmap := hprod.map_tprod Complex.ofRealHom Complex.continuous_ofReal
  change ((∏' n : ℕ, (1 + r ^ (2 * n + 1)) : ℝ) : ℂ) =
    ∏' n : ℕ, ((1 + r ^ (2 * n + 1) : ℝ) : ℂ) at hmap
  rw [weberF_eq_exp_mul_tprod (by simpa using hy)]
  have hexp₁ : cexp (-(π * I * ((y : ℂ) * I)) / 24) = (Real.exp (π * y / 24) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hexp₂ : cexp (π * I * ((y : ℂ) * I)) = (r : ℂ) := by
    rw [hr, Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [hexp₁, hexp₂, Complex.ofReal_mul, hmap]
  push_cast
  rfl

/-- The odd-power product is at least one. -/
theorem one_le_tprod_one_add_odd_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    1 ≤ ∏' n : ℕ, (1 + r ^ (2 * n + 1)) := by
  have hsum : Summable (fun n : ℕ ↦ r ^ (2 * n + 1)) := by
    have hr2 : r ^ 2 < 1 := by nlinarith
    refine ((summable_geometric_of_lt_one (by positivity) hr2).mul_left r).congr fun n => ?_
    ring
  have hpos : ∀ n : ℕ, 0 < 1 + r ^ (2 * n + 1) := fun n => by positivity
  rw [← Real.rexp_tsum_eq_tprod hpos (Real.summable_log_one_add_of_summable hsum)]
  apply Real.one_le_exp
  apply tsum_nonneg
  intro n
  apply Real.log_nonneg
  have := pow_nonneg hr0 (2 * n + 1)
  linarith

/-- The odd-power product is at most `exp (r / (1 - r²))`. -/
theorem tprod_one_add_odd_pow_le_exp {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∏' n : ℕ, (1 + r ^ (2 * n + 1)) ≤ Real.exp (r / (1 - r ^ 2)) := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hgeom := summable_geometric_of_lt_one (by positivity : 0 ≤ r ^ 2) hr2
  have hsum : Summable (fun n : ℕ ↦ r ^ (2 * n + 1)) :=
    (hgeom.mul_left r).congr fun n => by ring
  have hpos : ∀ n : ℕ, 0 < 1 + r ^ (2 * n + 1) := fun n => by positivity
  have hlog := Real.summable_log_one_add_of_summable hsum
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  apply Real.exp_le_exp.mpr
  have hle : ∑' n : ℕ, Real.log (1 + r ^ (2 * n + 1)) ≤ ∑' n : ℕ, r ^ (2 * n + 1) := by
    apply Summable.tsum_le_tsum _ hlog hsum
    intro n
    have h := Real.log_le_sub_one_of_pos (hpos n)
    linarith
  have htsum : ∑' n : ℕ, r ^ (2 * n + 1) = r / (1 - r ^ 2) := by
    have h := tsum_geometric_of_lt_one (by positivity : 0 ≤ r ^ 2) hr2
    calc ∑' n : ℕ, r ^ (2 * n + 1) = ∑' n : ℕ, r * (r ^ 2) ^ n := by
          congr 1
          funext n
          ring
      _ = r * (1 - r ^ 2)⁻¹ := by rw [tsum_mul_left, h]
      _ = r / (1 - r ^ 2) := by rw [div_eq_mul_inv]
  linarith

/-- Lower exponential bound for `𝔣` on the positive imaginary axis. -/
theorem exp_le_weberF_mul_I_re (y : ℝ) (hy : 0 < y) :
    Real.exp (π * y / 24) ≤ (weberF ((y : ℂ) * I)).re := by
  have hr0 : 0 ≤ Real.exp (-(π * y)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(π * y)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  rw [weberF_mul_I_eq_tprod y hy, Complex.ofReal_re]
  have h := one_le_tprod_one_add_odd_pow hr0 hr1
  have he := Real.exp_pos (π * y / 24)
  nlinarith

/-- Upper exponential bound for `𝔣` on the positive imaginary axis. -/
theorem weberF_mul_I_re_le_exp (y : ℝ) (hy : 0 < y) :
    (weberF ((y : ℂ) * I)).re ≤
      Real.exp (π * y / 24 + Real.exp (-(π * y)) / (1 - Real.exp (-(π * y)) ^ 2)) := by
  have hr0 : 0 ≤ Real.exp (-(π * y)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(π * y)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  rw [weberF_mul_I_eq_tprod y hy, Complex.ofReal_re, Real.exp_add]
  exact mul_le_mul_of_nonneg_left (tprod_one_add_odd_pow_le_exp hr0 hr1)
    (Real.exp_pos _).le

/-- The normalized gamma value is strictly below `-15` once `πy > 10`.
This is a purely analytic bound, independent of class numbers or CM arithmetic. -/
theorem gamma₂_half_add_three_mul_I_re_lt_neg_fifteen (y : ℝ) (hy : 0 < y)
    (hπy : 10 < π * y) :
    (gamma₂ (UpperHalfPlane.ofComplex (((y : ℂ) * I + 3) / 2))).re < -15 := by
  let x := (weberF ((y : ℂ) * I)).re
  have hx : 0 < x := weberF_mul_I_re_pos y hy
  have hf : weberF ((y : ℂ) * I) = (x : ℂ) :=
    Complex.ext rfl (by simpa using weberF_mul_I_im y hy)
  have hγ : gamma₂ (UpperHalfPlane.ofComplex (((y : ℂ) * I + 3) / 2)) =
      (((256 - x ^ 24) / x ^ 16 : ℝ) : ℂ) := by
    rw [gamma₂_half_add_three_eq_weberF (by simpa using hy), hf]
    push_cast
    rfl
  rw [hγ, Complex.ofReal_re]
  let F := x ^ 8
  have hF : 0 < F := pow_pos hx 8
  have hlow : Real.exp (π * y) ≤ F ^ 3 := by
    have h := pow_le_pow_left₀ (Real.exp_pos _).le (exp_le_weberF_mul_I_re y hy) 24
    have he : Real.exp (π * y / 24) ^ 24 = Real.exp (π * y) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he] at h
    convert h using 1
    ring
  have he10 : (2.7 : ℝ) ^ 10 < Real.exp 10 := by
    have h : (2.7 : ℝ) ^ 10 < Real.exp 1 ^ 10 :=
      pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) (by norm_num)
    simpa only [Real.exp_one_pow, Nat.cast_ofNat] using h
  have hexp : (4096 : ℝ) < Real.exp (π * y) := by
    have h := Real.exp_lt_exp.mpr hπy
    norm_num at he10
    linarith
  have hF16 : 16 < F := by
    by_contra h
    have hle : F ≤ 16 := not_lt.mp h
    have hpow := pow_le_pow_left₀ hF.le hle 3
    norm_num at hpow
    linarith
  have hF2 : F ^ 2 = x ^ 16 := by dsimp [F]; ring
  have hF3 : F ^ 3 = x ^ 24 := by dsimp [F]; ring
  rw [← hF3, ← hF2, div_lt_iff₀ (pow_pos hF 2)]
  have hsq : 256 < F ^ 2 := by nlinarith
  have hfactor : 0 < F ^ 2 * (F - 16) := mul_pos (pow_pos hF 2) (by linarith)
  nlinarith

end ModularForm
