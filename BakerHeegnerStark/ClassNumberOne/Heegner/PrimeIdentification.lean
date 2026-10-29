/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ClassNumberOne.Heegner.IntegralPoints
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Recovering the Prime from Heegner's Gamma Value

Let `F > 0` satisfy `F³ + γF² - 256 = 0` and lie between `exp(π√p / 3)` and a
slightly larger exponential. For each value `γ` in Heegner's finite list, these
inequalities admit exactly one `p ≡ 3 (mod 8)` with `p ≥ 11`. The proof compares
exponentials of explicit integers with `e ∈ (2.7, 2.72)` and `π ∈ (3.14, 3.15)`.
No table relating primes and gamma values is assumed.
-/

open Real

namespace BakerHeegnerStark

theorem two_point_seven_pow_lt_exp (K : ℕ) (hK : K ≠ 0) : (2.7 : ℝ) ^ K < Real.exp K := by
  rw [← Real.exp_one_pow]
  exact pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) hK

theorem exp_lt_two_point_seven_two_pow (K : ℕ) (hK : K ≠ 0) : Real.exp K < (2.72 : ℝ) ^ K := by
  rw [← Real.exp_one_pow]
  exact pow_lt_pow_left₀ (by linarith [Real.exp_one_lt_d9]) (Real.exp_pos 1).le hK

theorem lt_pi_mul_sqrt {K s : ℝ} {n : ℕ} (hs : 0 ≤ s) (hsn : s ^ 2 < n)
    (hK : K ≤ 3.14 * s) : K < π * Real.sqrt n := by
  have h₁ : s < Real.sqrt n := (Real.lt_sqrt hs).mpr hsn
  have h₂ : π * s < π * Real.sqrt n := mul_lt_mul_of_pos_left h₁ Real.pi_pos
  have h₃ : 3.14 * s ≤ π * s := mul_le_mul_of_nonneg_right Real.pi_gt_d2.le hs
  linarith

theorem pi_mul_sqrt_lt {K s : ℝ} {n : ℕ} (hs : 0 < s) (hsn : (n : ℝ) < s ^ 2)
    (hK : 3.15 * s ≤ K) : π * Real.sqrt n < K := by
  have h₁ : Real.sqrt n < s := (Real.sqrt_lt' hs).mpr hsn
  have h₂ : π * Real.sqrt n < π * s := mul_lt_mul_of_pos_left h₁ Real.pi_pos
  have h₃ : π * s ≤ 3.15 * s := mul_le_mul_of_nonneg_right Real.pi_lt_d2.le hs.le
  linarith

/-- An upper bound for `G ≥ exp(π√p)` bounds `p` above. -/
theorem lt_of_exp_pi_sqrt_le {p q : ℕ} {G B K : ℝ} (hG : Real.exp (π * Real.sqrt p) ≤ G)
    (hGB : G < B) (hBK : B ≤ Real.exp K) (hKq : K < π * Real.sqrt q) : p < q := by
  by_contra h
  have hqp : q ≤ p := not_lt.mp h
  have hsq : Real.sqrt q ≤ Real.sqrt p := Real.sqrt_le_sqrt (by exact_mod_cast hqp)
  have h₁ : π * Real.sqrt q ≤ π * Real.sqrt p := mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
  have h₂ : Real.exp K < Real.exp (π * Real.sqrt p) := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- A lower bound for `G ≤ exp(π√p + 3/1000)` bounds `p` below. -/
theorem lt_of_le_exp_pi_sqrt_add {p q : ℕ} {G B K : ℝ}
    (hG : G ≤ Real.exp (π * Real.sqrt p + 3 / 1000)) (hBG : B < G) (hKB : Real.exp K ≤ B)
    (hqK : π * Real.sqrt q + 3 / 1000 < K) : q < p := by
  by_contra h
  have hpq : p ≤ q := not_lt.mp h
  have hsq : Real.sqrt p ≤ Real.sqrt q := Real.sqrt_le_sqrt (by exact_mod_cast hpq)
  have h₁ : π * Real.sqrt p ≤ π * Real.sqrt q := mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
  have h₂ : Real.exp (π * Real.sqrt p + 3 / 1000) < Real.exp K :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- A positive root of `F³ - NF² - 256` with `N ≥ 32` lies strictly between
`N` and `N + 1`. -/
theorem cube_bounds_of_heegner_cubic {F N : ℝ} (hF : 0 < F) (hN : 32 ≤ N)
    (h : F ^ 3 - N * F ^ 2 - 256 = 0) : N ^ 3 < F ^ 3 ∧ F ^ 3 < (N + 1) ^ 3 := by
  have hF2 : 0 < F ^ 2 := by positivity
  have hdiff : F ^ 2 * (F - N) = 256 := by linear_combination h
  have hgt : N < F := by
    by_contra hle
    have hle' : F ≤ N := not_lt.mp hle
    have : F ^ 2 * (F - N) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hF2.le (by linarith)
    linarith
  have hlt : F < N + 1 := by
    by_contra hge
    have hge' : N + 1 ≤ F := not_lt.mp hge
    have h₁ : F ^ 2 ≤ F ^ 2 * (F - N) := le_mul_of_one_le_right hF2.le (by linarith)
    have h₂ : (32 : ℝ) ^ 2 < F ^ 2 := pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
    linarith
  exact ⟨pow_lt_pow_left₀ hgt (by linarith) (by norm_num),
    pow_lt_pow_left₀ hlt hF.le (by norm_num)⟩

/-- **Prime identification.** If `F > 0` satisfies Heegner's relation
`F³ + γF² - 256 = 0` for `γ` in the finite gamma list, and
`exp(π√p) ≤ F³ ≤ exp(π√p + 3/1000)` with `p ≡ 3 (mod 8)` and `p ≥ 11`, then `p`
is one of `11, 19, 43, 67, 163`. -/
theorem eq_of_heegnerGamma_of_exp_bounds {p : ℕ} {F : ℝ} {γ : ℤ} (hp8 : p % 8 = 3)
    (hp11 : 11 ≤ p) (hF : 0 < F) (hlow : Real.exp (π * Real.sqrt p) ≤ F ^ 3)
    (hup : F ^ 3 ≤ Real.exp (π * Real.sqrt p + 3 / 1000))
    (hcubic : F ^ 3 + γ * F ^ 2 - 256 = 0) (hγ : γ ∈ heegnerGammaSet) :
    p = 11 ∨ p = 19 ∨ p = 43 ∨ p = 67 ∨ p = 163 := by
  have h₁₁ : (10 : ℝ) < π * Real.sqrt 11 :=
    lt_pi_mul_sqrt (s := 3.31) (by norm_num) (by norm_num) (by norm_num)
  have hlow₁₁ : Real.exp 10 ≤ F ^ 3 := by
    have hs : Real.sqrt 11 ≤ Real.sqrt p := Real.sqrt_le_sqrt (by exact_mod_cast hp11)
    have := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
    exact le_trans (Real.exp_le_exp.mpr (by linarith)) hlow
  have he₁₀ := two_point_seven_pow_lt_exp 10 (by norm_num)
  norm_num at he₁₀
  simp only [heegnerGammaSet, Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at hcubic
    linarith
  · obtain ⟨-, h₂⟩ := cube_bounds_of_heegner_cubic hF (N := 32) (by norm_num)
      (by push_cast at hcubic; linarith)
    have hK := two_point_seven_pow_lt_exp 13 (by norm_num)
    norm_num at hK
    have hq : (13 : ℝ) < π * Real.sqrt (19 : ℕ) :=
      lt_pi_mul_sqrt (s := 4.35) (by norm_num) (by norm_num) (by norm_num)
    have hlt : p < 19 := lt_of_exp_pi_sqrt_le hlow h₂ (K := 13) (by norm_num; linarith) hq
    omega
  · obtain ⟨h₁, h₂⟩ := cube_bounds_of_heegner_cubic hF (N := 96) (by norm_num)
      (by push_cast at hcubic; linarith)
    have hK₁ := two_point_seven_pow_lt_exp 16 (by norm_num)
    have hK₂ := exp_lt_two_point_seven_two_pow 11 (by norm_num)
    norm_num at hK₁ hK₂
    have hq₁ : (16 : ℝ) < π * Real.sqrt (27 : ℕ) :=
      lt_pi_mul_sqrt (s := 5.19) (by norm_num) (by norm_num) (by norm_num)
    have hq₂ : π * Real.sqrt (11 : ℕ) < 10.46 :=
      pi_mul_sqrt_lt (s := 3.32) (by norm_num) (by norm_num) (by norm_num)
    have hlt : p < 27 := lt_of_exp_pi_sqrt_le hlow h₂ (K := 16) (by norm_num; linarith) hq₁
    have hgt : 11 < p :=
      lt_of_le_exp_pi_sqrt_add hup h₁ (K := 11) (by norm_num; linarith) (by linarith)
    omega
  · obtain ⟨h₁, h₂⟩ := cube_bounds_of_heegner_cubic hF (N := 960) (by norm_num)
      (by push_cast at hcubic; linarith)
    have hK₁ := two_point_seven_pow_lt_exp 22 (by norm_num)
    have hK₂ := exp_lt_two_point_seven_two_pow 19 (by norm_num)
    norm_num at hK₁ hK₂
    have hq₁ : (22 : ℝ) < π * Real.sqrt (51 : ℕ) :=
      lt_pi_mul_sqrt (s := 7.14) (by norm_num) (by norm_num) (by norm_num)
    have hq₂ : π * Real.sqrt (35 : ℕ) < 18.65 :=
      pi_mul_sqrt_lt (s := 5.92) (by norm_num) (by norm_num) (by norm_num)
    have hlt : p < 51 := lt_of_exp_pi_sqrt_le hlow h₂ (K := 22) (by norm_num; linarith) hq₁
    have hgt : 35 < p :=
      lt_of_le_exp_pi_sqrt_add hup h₁ (K := 19) (by norm_num; linarith) (by linarith)
    omega
  · obtain ⟨h₁, h₂⟩ := cube_bounds_of_heegner_cubic hF (N := 5280) (by norm_num)
      (by push_cast at hcubic; linarith)
    have hK₁ := two_point_seven_pow_lt_exp 27 (by norm_num)
    have hK₂ := exp_lt_two_point_seven_two_pow 25 (by norm_num)
    norm_num at hK₁ hK₂
    have hq₁ : (27 : ℝ) < π * Real.sqrt (75 : ℕ) :=
      lt_pi_mul_sqrt (s := 8.66) (by norm_num) (by norm_num) (by norm_num)
    have hq₂ : π * Real.sqrt (59 : ℕ) < 24.23 :=
      pi_mul_sqrt_lt (s := 7.69) (by norm_num) (by norm_num) (by norm_num)
    have hlt : p < 75 := lt_of_exp_pi_sqrt_le hlow h₂ (K := 27) (by norm_num; linarith) hq₁
    have hgt : 59 < p :=
      lt_of_le_exp_pi_sqrt_add hup h₁ (K := 25) (by norm_num; linarith) (by linarith)
    omega
  · obtain ⟨h₁, h₂⟩ := cube_bounds_of_heegner_cubic hF (N := 640320) (by norm_num)
      (by push_cast at hcubic; linarith)
    have hK₁ := two_point_seven_pow_lt_exp 41 (by norm_num)
    have hK₂ := exp_lt_two_point_seven_two_pow 40 (by norm_num)
    norm_num at hK₁ hK₂
    have hq₁ : (41 : ℝ) < π * Real.sqrt (171 : ℕ) :=
      lt_pi_mul_sqrt (s := 13.07) (by norm_num) (by norm_num) (by norm_num)
    have hq₂ : π * Real.sqrt (155 : ℕ) < 39.22 :=
      pi_mul_sqrt_lt (s := 12.45) (by norm_num) (by norm_num) (by norm_num)
    have hlt : p < 171 :=
      lt_of_exp_pi_sqrt_le hlow h₂ (K := 41) (by norm_num; linarith) hq₁
    have hgt : 155 < p :=
      lt_of_le_exp_pi_sqrt_add hup h₁ (K := 40) (by norm_num; linarith) (by linarith)
    omega

end BakerHeegnerStark
