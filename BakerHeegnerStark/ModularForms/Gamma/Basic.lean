/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.Identity
import BakerHeegnerStark.ModularForms.Weber.Polynomial

/-!
# Gamma Normalization

Real q-expansions on the positive imaginary axis fix the cube-root
normalization in the gamma identities.
-/

open Complex EisensteinSeries
open scoped Real ArithmeticFunction.sigma

namespace ModularForm

/-- The real q-expansion of the normalized weight-four Eisenstein series on the imaginary axis. -/
theorem E₄_mul_I_eq (y : ℝ) (hy : 0 < y) :
    E₄ (⟨(y : ℂ) * I, by simpa using hy⟩ : UpperHalfPlane) =
      ((1 + 240 * ∑' n : ℕ+, (σ 3 n : ℝ) * Real.exp (-2 * Real.pi * y) ^ (n : ℤ)) : ℝ) := by
  let τ : UpperHalfPlane := ⟨(y : ℂ) * I, by simpa using hy⟩
  have hexp : cexp (2 * π * I * (τ : ℂ)) = (Real.exp (-2 * Real.pi * y) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    dsimp [τ]
    push_cast
    ring_nf
    simp [I_sq]
  have h := EisensteinSeries.q_expansion_bernoulli (k := 4) (by norm_num) (by decide) τ
  have hb : bernoulli 4 = -1 / 30 := by decide +kernel
  norm_num [hb] at h
  rw [hexp] at h
  convert h using 1
  push_cast
  simp only [zpow_natCast]

/-- The weight-four Eisenstein series is real on the positive imaginary axis. -/
theorem E₄_mul_I_im (y : ℝ) (hy : 0 < y) :
    (E₄ (⟨(y : ℂ) * I, by simpa using hy⟩ : UpperHalfPlane)).im = 0 := by
  rw [E₄_mul_I_eq y hy]
  exact Complex.ofReal_im _

/-- The weight-four Eisenstein series is strictly positive on the positive imaginary axis. -/
theorem E₄_mul_I_re_pos (y : ℝ) (hy : 0 < y) :
    0 < (E₄ (⟨(y : ℂ) * I, by simpa using hy⟩ : UpperHalfPlane)).re := by
  rw [E₄_mul_I_eq y hy, Complex.ofReal_re]
  have hnonneg : 0 ≤ ∑' n : ℕ+, (σ 3 n : ℝ) * Real.exp (-2 * Real.pi * y) ^ (n : ℤ) :=
    tsum_nonneg (fun n ↦ by positivity)
  linarith

/-- Gamma is real at a point on the positive imaginary axis. -/
theorem gamma₂_mul_I_im (y : ℝ) (hy : 0 < y) :
    (gamma₂ (⟨(y : ℂ) * I, by simpa using hy⟩ : UpperHalfPlane)).im = 0 := by
  have hη : eta ((y : ℂ) * I) = ((eta ((y : ℂ) * I)).re : ℂ) :=
    Complex.ext rfl (eta_mul_I_im y hy)
  rw [gamma₂]
  change (E₄ (⟨(y : ℂ) * I, _⟩ : UpperHalfPlane) / eta ((y : ℂ) * I) ^ 8).im = 0
  rw [hη, ← Complex.ofReal_pow, Complex.div_im, E₄_mul_I_im y hy]
  simp only [Complex.ofReal_im, mul_zero, zero_mul, sub_self, zero_div]

/-- Gamma has positive real part on the positive imaginary axis. -/
theorem gamma₂_mul_I_re_pos (y : ℝ) (hy : 0 < y) :
    0 < (gamma₂ (⟨(y : ℂ) * I, by simpa using hy⟩ : UpperHalfPlane)).re := by
  have hη : eta ((y : ℂ) * I) = ((eta ((y : ℂ) * I)).re : ℂ) :=
    Complex.ext rfl (eta_mul_I_im y hy)
  rw [gamma₂]
  change 0 < (E₄ (⟨(y : ℂ) * I, _⟩ : UpperHalfPlane) / eta ((y : ℂ) * I) ^ 8).re
  rw [hη, ← Complex.ofReal_pow, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply,
    E₄_mul_I_im y hy, mul_zero, add_zero]
  have hE := E₄_mul_I_re_pos y hy
  have hηpos := eta_mul_I_re_pos y hy
  positivity

/-- The second Weber quotient gives gamma with its actual cube-root normalization. -/
theorem gamma₂_eq_weberF₂ (τ : UpperHalfPlane) :
    gamma₂ τ = (weberF₂ τ ^ 24 + 16) / weberF₂ τ ^ 8 := by
  let f : ℂ → ℂ := fun z ↦ E₄ (UpperHalfPlane.ofComplex z) / eta z ^ 8
  let g : ℂ → ℂ := fun z ↦ (weberF₂ z ^ 24 + 16) / weberF₂ z ^ 8
  have hE : AnalyticOnNhd ℂ (E₄ ∘ UpperHalfPlane.ofComplex)
      UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₄.holo').analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hη : AnalyticOnNhd ℂ eta UpperHalfPlane.upperHalfPlaneSet := by
    apply DifferentiableOn.analyticOnNhd _ UpperHalfPlane.isOpen_upperHalfPlaneSet
    exact fun z hz ↦ (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt
  have hf : AnalyticOnNhd ℂ f UpperHalfPlane.upperHalfPlaneSet :=
    hE.div (hη.pow 8) (fun z hz ↦ pow_ne_zero _ (eta_ne_zero hz))
  have hg : AnalyticOnNhd ℂ g UpperHalfPlane.upperHalfPlaneSet :=
    ((analyticOnNhd_weberF₂.pow 24).add analyticOnNhd_const).div
      (analyticOnNhd_weberF₂.pow 8) (fun z hz ↦ pow_ne_zero _ (weberF₂_ne_zero hz))
  have hcube : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, f z ^ 3 = g z ^ 3 := by
    intro z hz
    have hf3 : f z ^ 3 = jInvariant (UpperHalfPlane.ofComplex z) := by
      simpa only [f, gamma₂, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
        gamma₂_cube (UpperHalfPlane.ofComplex z)
    have hg3 : g z ^ 3 = jInvariant (UpperHalfPlane.ofComplex z) := by
      dsimp [g]
      rw [div_pow, ← pow_mul]
      simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
        (jInvariant_eq_weberF₂ (UpperHalfPlane.ofComplex z)).symm
    exact hf3.trans hg3.symm
  have hfactor : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      (f z - g z) * (f z ^ 2 + f z * g z + g z ^ 2) = 0 := by
    intro z hz
    linear_combination hcube z hz
  rcases (hf.sub hg).eq_zero_or_eq_zero_of_mul_eq_zero
      (((hf.pow 2).add (hf.mul hg)).add (hg.pow 2)) hfactor
      (convex_halfSpace_im_gt 0).isPreconnected with hzero | hzero
  · have h := sub_eq_zero.mp (hzero τ τ.im_pos)
    simpa only [f, g, UpperHalfPlane.ofComplex_apply, gamma₂] using h
  · let τi : UpperHalfPlane := ⟨I, by simp⟩
    have hfi : f I = gamma₂ τi := by
      simp only [f, gamma₂, τi, UpperHalfPlane.ofComplex_apply_of_im_pos
        (by simp : 0 < I.im)]
    have hfireal : f I = ((f I).re : ℂ) := by
      apply Complex.ext
      · rfl
      · change (f I).im = 0
        rw [hfi]
        simpa [τi] using gamma₂_mul_I_im 1 one_pos
    have hfpos : 0 < (f I).re := by
      rw [hfi]
      simpa [τi] using gamma₂_mul_I_re_pos 1 one_pos
    have hF₂ : weberF₂ I = ((weberF₂ I).re : ℂ) :=
      Complex.ext rfl (by simpa using weberF₂_mul_I_im 1 one_pos)
    have hgi : g I = (((weberF₂ I).re ^ 24 + 16) / (weberF₂ I).re ^ 8 : ℝ) := by
      dsimp [g]
      rw [hF₂]
      push_cast
      rfl
    have hgpos : 0 < ((weberF₂ I).re ^ 24 + 16) / (weberF₂ I).re ^ 8 := by
      have hp : 0 < (weberF₂ I).re := by simpa using weberF₂_mul_I_re_pos 1 one_pos
      positivity
    have hi := hzero I (by simp)
    change f I ^ 2 + f I * g I + g I ^ 2 = 0 at hi
    rw [hfireal, hgi] at hi
    norm_cast at hi
    nlinarith [sq_pos_of_pos hfpos, mul_pos hfpos hgpos,
      sq_nonneg (((weberF₂ I).re ^ 24 + 16) / (weberF₂ I).re ^ 8)]

/-- The shifted Weber quotient gives the same normalized gamma value. -/
theorem gamma₂_eq_weberF (τ : UpperHalfPlane) :
    gamma₂ τ = (weberF τ ^ 24 - 16) / weberF τ ^ 8 := by
  rw [gamma₂_eq_weberF₂]
  let a := weberF τ ^ 8
  let b := weberF₁ τ ^ 8
  let c := weberF₂ τ ^ 8
  have hs : a = b + c := weberF_pow_eight τ.im_pos
  have hp : a * b * c = 16 := weber_product_pow_eight τ.im_pos
  have ha : a ≠ 0 := pow_ne_zero _ (weberF_ne_zero τ.im_pos)
  have hc : c ≠ 0 := pow_ne_zero _ (weberF₂_ne_zero τ.im_pos)
  simp only [show (24 : ℕ) = 8 * 3 by decide, pow_mul]
  change (c ^ 3 + 16) / c = (a ^ 3 - 16) / a
  apply (div_eq_div_iff hc ha).mpr
  rw [← hp, hs]
  ring

/-- The first Weber quotient gives the same normalized gamma value. -/
theorem gamma₂_eq_weberF₁ (τ : UpperHalfPlane) :
    gamma₂ τ = (weberF₁ τ ^ 24 + 16) / weberF₁ τ ^ 8 := by
  rw [gamma₂_eq_weberF₂]
  let a := weberF τ ^ 8
  let b := weberF₁ τ ^ 8
  let c := weberF₂ τ ^ 8
  have hs : a = b + c := weberF_pow_eight τ.im_pos
  have hp : a * b * c = 16 := weber_product_pow_eight τ.im_pos
  have hb : b ≠ 0 := pow_ne_zero _ (weberF₁_ne_zero τ.im_pos)
  have hc : c ≠ 0 := pow_ne_zero _ (weberF₂_ne_zero τ.im_pos)
  simp only [show (24 : ℕ) = 8 * 3 by decide, pow_mul]
  change (c ^ 3 + 16) / c = (b ^ 3 + 16) / b
  apply (div_eq_div_iff hc hb).mpr
  rw [← hp, hs]
  ring

end ModularForm
