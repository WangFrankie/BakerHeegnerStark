/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Eta.Positivity
import BakerHeegnerStark.ModularForms.Weber.Basic
import BakerHeegnerStark.ModularForms.Hecke.Two
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Weber's Positive Normalization and Eighth-Power Identity

On the positive imaginary axis the two unshifted eta quotients are positive
real numbers. Weber's product identity determines the phase and sign of the
remaining function. Analyticity and connectedness then select the correct
factor of the higher-power identities on the entire upper half-plane.
-/

namespace ModularForm

/-- Weber's first eta quotient is real on the positive imaginary axis. -/
theorem weberF₁_mul_I_im (y : ℝ) (hy : 0 < y) :
    (weberF₁ ((y : ℂ) * Complex.I)).im = 0 := by
  have hhalf : (y : ℂ) * Complex.I / 2 = ((y / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [weberF₁, hhalf, Complex.div_im, eta_mul_I_im y hy,
    eta_mul_I_im (y / 2) (half_pos hy)]
  simp

/-- Weber's first eta quotient has positive real part on the positive imaginary axis. -/
theorem weberF₁_mul_I_re_pos (y : ℝ) (hy : 0 < y) :
    0 < (weberF₁ ((y : ℂ) * Complex.I)).re := by
  have hhalf : (y : ℂ) * Complex.I / 2 = ((y / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simp only [weberF₁, hhalf, Complex.div_re, Complex.normSq_apply,
    eta_mul_I_im y hy, eta_mul_I_im (y / 2) (half_pos hy),
    mul_zero, add_zero]
  have h₁ := eta_mul_I_re_pos (y / 2) (half_pos hy)
  have h₂ := eta_mul_I_re_pos y hy
  positivity

/-- Weber's second eta quotient is real on the positive imaginary axis. -/
theorem weberF₂_mul_I_im (y : ℝ) (hy : 0 < y) :
    (weberF₂ ((y : ℂ) * Complex.I)).im = 0 := by
  have hdouble : 2 * ((y : ℂ) * Complex.I) = ((2 * y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [weberF₂, hdouble, Complex.mul_im, Complex.div_im, eta_mul_I_im y hy,
    eta_mul_I_im (2 * y) (mul_pos two_pos hy)]
  simp

/-- Weber's second eta quotient has positive real part on the positive imaginary axis. -/
theorem weberF₂_mul_I_re_pos (y : ℝ) (hy : 0 < y) :
    0 < (weberF₂ ((y : ℂ) * Complex.I)).re := by
  have hdouble : 2 * ((y : ℂ) * Complex.I) = ((2 * y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simp only [weberF₂, hdouble, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_re, Complex.normSq_apply, eta_mul_I_im y hy,
    eta_mul_I_im (2 * y) (mul_pos two_pos hy), mul_zero, zero_mul, add_zero, sub_zero]
  have h₁ := eta_mul_I_re_pos (2 * y) (mul_pos two_pos hy)
  have h₂ := eta_mul_I_re_pos y hy
  positivity

/-- Weber's shifted eta quotient is real on the positive imaginary axis. -/
theorem weberF_mul_I_im (y : ℝ) (hy : 0 < y) :
    (weberF ((y : ℂ) * Complex.I)).im = 0 := by
  have h := congrArg Complex.im
    (weberF_mul_weberF₁_mul_weberF₂ (by simpa using hy :
      0 < ((y : ℂ) * Complex.I).im))
  simp only [Complex.mul_im, weberF₁_mul_I_im y hy, weberF₂_mul_I_im y hy,
    mul_zero, zero_add, Complex.ofReal_im] at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right
    (ne_of_gt (weberF₂_mul_I_re_pos y hy)))).resolve_right
      (ne_of_gt (weberF₁_mul_I_re_pos y hy))

/-- Weber's shifted eta quotient has positive real part on the positive imaginary axis. -/
theorem weberF_mul_I_re_pos (y : ℝ) (hy : 0 < y) :
    0 < (weberF ((y : ℂ) * Complex.I)).re := by
  have h := congrArg Complex.re
    (weberF_mul_weberF₁_mul_weberF₂ (by simpa using hy :
      0 < ((y : ℂ) * Complex.I).im))
  simp only [Complex.mul_re, weberF₁_mul_I_im y hy, weberF₂_mul_I_im y hy,
    mul_zero, sub_zero, Complex.ofReal_re] at h
  have hpos : 0 < (weberF ((y : ℂ) * Complex.I)).re *
      (weberF₁ ((y : ℂ) * Complex.I)).re * (weberF₂ ((y : ℂ) * Complex.I)).re := by
    rw [h]
    exact Real.sqrt_pos.mpr (by norm_num)
  exact pos_of_mul_pos_left
    (pos_of_mul_pos_left hpos (weberF₂_mul_I_re_pos y hy).le)
    (weberF₁_mul_I_re_pos y hy).le

/-- Weber's shifted eta quotient is analytic on the upper half-plane. -/
theorem analyticOnNhd_weberF :
    AnalyticOnNhd ℂ weberF UpperHalfPlane.upperHalfPlaneSet := by
  apply DifferentiableOn.analyticOnNhd _ UpperHalfPlane.isOpen_upperHalfPlaneSet
  intro z hz
  change 0 < z.im at hz
  have hd : DifferentiableAt ℂ (fun w : ℂ ↦ (w + 1) / 2) z := by fun_prop
  have hz' : 0 < ((z + 1) / 2).im := by simpa using half_pos hz
  exact (((differentiableAt_eta_of_mem_upperHalfPlaneSet hz').comp z
    hd).div
      (differentiableAt_eta_of_mem_upperHalfPlaneSet hz) (eta_ne_zero hz)).const_mul
        zeta48⁻¹ |>.differentiableWithinAt

/-- Weber's first eta quotient is analytic on the upper half-plane. -/
theorem analyticOnNhd_weberF₁ :
    AnalyticOnNhd ℂ weberF₁ UpperHalfPlane.upperHalfPlaneSet := by
  apply DifferentiableOn.analyticOnNhd _ UpperHalfPlane.isOpen_upperHalfPlaneSet
  intro z hz
  change 0 < z.im at hz
  have hd : DifferentiableAt ℂ (fun w : ℂ ↦ w / 2) z := by fun_prop
  have hz' : 0 < (z / 2).im := by simpa using half_pos hz
  exact ((differentiableAt_eta_of_mem_upperHalfPlaneSet hz').comp z
    hd).div
      (differentiableAt_eta_of_mem_upperHalfPlaneSet hz) (eta_ne_zero hz)
        |>.differentiableWithinAt

/-- Weber's second eta quotient is analytic on the upper half-plane. -/
theorem analyticOnNhd_weberF₂ :
    AnalyticOnNhd ℂ weberF₂ UpperHalfPlane.upperHalfPlaneSet := by
  apply DifferentiableOn.analyticOnNhd _ UpperHalfPlane.isOpen_upperHalfPlaneSet
  intro z hz
  change 0 < z.im at hz
  have hd : DifferentiableAt ℂ (fun w : ℂ ↦ 2 * w) z := by fun_prop
  have hz' : 0 < (2 * z).im := by simpa using mul_pos two_pos hz
  exact (((differentiableAt_eta_of_mem_upperHalfPlaneSet hz').comp z
    hd).div
      (differentiableAt_eta_of_mem_upperHalfPlaneSet hz) (eta_ne_zero hz)).const_mul
        (Real.sqrt 2 : ℂ) |>.differentiableWithinAt

/-- The product of the three eighth powers is `16`. -/
theorem weber_product_pow_eight {z : ℂ} (hz : 0 < z.im) :
    weberF z ^ 8 * weberF₁ z ^ 8 * weberF₂ z ^ 8 = 16 := by
  rw [← mul_pow, ← mul_pow, weberF_mul_weberF₁_mul_weberF₂ hz,
    show (8 : ℕ) = 2 * 4 by decide, pow_mul, ← Complex.ofReal_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

/-- Weber's eighth-power identity on the whole upper half-plane. -/
theorem weberF_pow_eight {z : ℂ} (hz : 0 < z.im) :
    weberF z ^ 8 = weberF₁ z ^ 8 + weberF₂ z ^ 8 := by
  let a : ℂ → ℂ := fun w ↦ weberF w ^ 8
  let b : ℂ → ℂ := fun w ↦ weberF₁ w ^ 8
  let c : ℂ → ℂ := fun w ↦ weberF₂ w ^ 8
  have ha : AnalyticOnNhd ℂ a UpperHalfPlane.upperHalfPlaneSet :=
    analyticOnNhd_weberF.pow 8
  have hb : AnalyticOnNhd ℂ b UpperHalfPlane.upperHalfPlaneSet :=
    analyticOnNhd_weberF₁.pow 8
  have hc : AnalyticOnNhd ℂ c UpperHalfPlane.upperHalfPlaneSet :=
    analyticOnNhd_weberF₂.pow 8
  have hfactor : ∀ w ∈ UpperHalfPlane.upperHalfPlaneSet,
      (a w - b w - c w) *
        (a w ^ 2 + a w * (b w + c w) + b w ^ 2 - b w * c w + c w ^ 2) = 0 := by
    intro w hw
    have hs : a w ^ 3 - b w ^ 3 - c w ^ 3 = 48 := by
      simpa only [a, b, c, ← pow_mul] using
        weberF_pow_24_sub_weberF₁_pow_24_sub_weberF₂_pow_24 hw
    have hp : a w * b w * c w = 16 := weber_product_pow_eight hw
    linear_combination hs - 3 * hp
  have hconnected : IsPreconnected UpperHalfPlane.upperHalfPlaneSet :=
    (convex_halfSpace_im_gt 0).isPreconnected
  rcases (ha.sub hb |>.sub hc).eq_zero_or_eq_zero_of_mul_eq_zero
      (((ha.pow 2).add (ha.mul (hb.add hc))).add (hb.pow 2) |>.sub (hb.mul hc)
        |>.add (hc.pow 2)) hfactor hconnected with hzero | hzero
  · have h := hzero z hz
    change weberF z ^ 8 - weberF₁ z ^ 8 - weberF₂ z ^ 8 = 0 at h
    exact sub_eq_zero.mp (by simpa only [sub_sub] using h)
  · have hi := hzero Complex.I (by simp)
    have hF : weberF Complex.I = ((weberF Complex.I).re : ℂ) :=
      Complex.ext rfl (by simpa using weberF_mul_I_im 1 one_pos)
    have hF₁ : weberF₁ Complex.I = ((weberF₁ Complex.I).re : ℂ) :=
      Complex.ext rfl (by simpa using weberF₁_mul_I_im 1 one_pos)
    have hF₂ : weberF₂ Complex.I = ((weberF₂ Complex.I).re : ℂ) :=
      Complex.ext rfl (by simpa using weberF₂_mul_I_im 1 one_pos)
    dsimp [a, b, c] at hi
    rw [hF, hF₁, hF₂] at hi
    norm_cast at hi
    let A := (weberF Complex.I).re ^ 8
    let B := (weberF₁ Complex.I).re ^ 8
    let C := (weberF₂ Complex.I).re ^ 8
    change A ^ 2 + A * (B + C) + B ^ 2 - B * C + C ^ 2 = 0 at hi
    have hA : 0 < A := pow_pos (by simpa using weberF_mul_I_re_pos 1 one_pos) _
    have hB : 0 < B := pow_pos (by simpa using weberF₁_mul_I_re_pos 1 one_pos) _
    have hC : 0 < C := pow_pos (by simpa using weberF₂_mul_I_re_pos 1 one_pos) _
    have hpos : 0 < A ^ 2 + A * (B + C) + B ^ 2 - B * C + C ^ 2 := by
      nlinarith [sq_nonneg (B - C), sq_nonneg A, mul_pos hA (add_pos hB hC)]
    exact False.elim (ne_of_gt hpos hi)

/-- The eighth-power identity specialized to the positive imaginary axis. -/
theorem weberF_pow_eight_mul_I (y : ℝ) (hy : 0 < y) :
    weberF ((y : ℂ) * Complex.I) ^ 8 =
      weberF₁ ((y : ℂ) * Complex.I) ^ 8 + weberF₂ ((y : ℂ) * Complex.I) ^ 8 :=
  weberF_pow_eight (by simpa using hy)

end ModularForm
