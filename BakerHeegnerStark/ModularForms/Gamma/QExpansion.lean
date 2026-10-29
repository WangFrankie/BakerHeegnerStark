/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.Modularity
import BakerHeegnerStark.ModularForms.QExpansion.Integral
import BakerHeegnerStark.ModularForms.QExpansion.Identity

/-!
# The Integral q-Expansion of Normalized Gamma

The actual product defining Dedekind eta identifies its eighth power with
`qParam 3` times the eighth power of Euler's function at `qParam 1`. Thus the
width-three regularization of the actual normalized `gamma₂` is periodic of
width one, holomorphic, and tends to one at the cusp. Its complete q-expansion
is obtained by inverting the integer pentagonal series to the eighth power.
The resulting integer series converges at every point of the upper half-plane.
No cube root is chosen from the identity `gamma₂ ^ 3 = jInvariant`.
-/

open EisensteinSeries UpperHalfPlane Filter Complex
open scoped Topology Manifold ModularForm

noncomputable section

namespace ModularForm

/-- The integer Euler-product denominator in the regularized gamma expansion. -/
def gammaDenominatorIntegralQExpansion : PowerSeries ℤ :=
  (PowerSeries.pentagonalSeries ℤ) ^ 8

theorem gammaDenominatorIntegralQExpansion_constantCoeff :
    gammaDenominatorIntegralQExpansion.constantCoeff = 1 := by
  have hp : (PowerSeries.pentagonalSeries ℤ).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.coeff_pentagonalSeries_pentagonal ℤ (0 : ℤ)
  change ((PowerSeries.pentagonalSeries ℤ) ^ 8).constantCoeff = 1
  rw [map_pow, hp, one_pow]

/-- The full integer numerator for `qParam 3 * gamma₂`, formed over `ℤ⟦q⟧`. -/
def gammaIntegralNumerator : PowerSeries ℤ :=
  eisensteinFourIntegralQExpansion *
    PowerSeries.invOfUnit gammaDenominatorIntegralQExpansion 1

theorem gammaDenominator_mul_gammaIntegralNumerator :
    gammaDenominatorIntegralQExpansion * gammaIntegralNumerator =
      eisensteinFourIntegralQExpansion := by
  dsimp only [gammaIntegralNumerator]
  rw [mul_left_comm, PowerSeries.mul_invOfUnit _
    1 (by simpa using gammaDenominatorIntegralQExpansion_constantCoeff), mul_one]

theorem gammaIntegralNumerator_constantCoeff :
    gammaIntegralNumerator.constantCoeff = 1 := by
  simp [gammaIntegralNumerator, eisensteinFourIntegralQExpansion_constantCoeff]

/-- The eighth power of the actual eta product has its actual width-three
exponential factor, not an arbitrarily selected cube root of `qParam 1`. -/
theorem eta_pow_eight_eq_qParam_three_mul_eulerFunction (τ : UpperHalfPlane) :
    eta (τ : ℂ) ^ 8 = Function.Periodic.qParam 3 (τ : ℂ) *
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8 := by
  have hq : Function.Periodic.qParam 24 (τ : ℂ) ^ 8 =
      Function.Periodic.qParam 3 (τ : ℂ) := by
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  change (Function.Periodic.qParam 24 (τ : ℂ) *
      ∏' n : ℕ, (1 - Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ 8 = _
  rw [mul_pow, hq, eulerFunction_eq_tprod
    (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)]

theorem eulerFunction_qParam_one_pow_eight_eq_eta_div_qParam_three (τ : UpperHalfPlane) :
    eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8 =
      eta (τ : ℂ) ^ 8 / Function.Periodic.qParam 3 (τ : ℂ) := by
  rw [eta_pow_eight_eq_qParam_three_mul_eulerFunction,
    mul_div_cancel_left₀ _ (Function.Periodic.qParam_ne_zero (h := 3) (τ : ℂ))]

theorem eulerFunction_qParam_one_pow_eight_ne_zero (τ : UpperHalfPlane) :
    eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8 ≠ 0 := by
  rw [eulerFunction_qParam_one_pow_eight_eq_eta_div_qParam_three]
  exact div_ne_zero (pow_ne_zero 8 (eta_ne_zero τ.im_pos))
    (Function.Periodic.qParam_ne_zero (h := 3) (τ : ℂ))

/-- The regularized actual gamma value satisfies the analytic counterpart of
`gammaDenominator_mul_gammaIntegralNumerator`. -/
theorem qParam_three_mul_gamma₂_mul_eulerFunction (τ : UpperHalfPlane) :
    (Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ) *
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8 = E₄ τ := by
  calc
    (Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ) *
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8 =
        gamma₂ τ * (Function.Periodic.qParam 3 (τ : ℂ) *
          eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8) := by ring
    _ = (E₄ τ / eta (τ : ℂ) ^ 8) * eta (τ : ℂ) ^ 8 := by
      rw [← eta_pow_eight_eq_qParam_three_mul_eulerFunction]
      rfl
    _ = E₄ τ := div_mul_cancel₀ _ (pow_ne_zero 8 (eta_ne_zero τ.im_pos))

theorem qParam_three_mul_gamma₂_eq_div_eulerFunction (τ : UpperHalfPlane) :
    Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ =
      E₄ τ / eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8 := by
  exact (eq_div_iff (eulerFunction_qParam_one_pow_eight_ne_zero τ)).mpr
    (qParam_three_mul_gamma₂_mul_eulerFunction τ)

private theorem gamma_qParam_mdifferentiable (h : ℝ) :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam h (τ : ℂ)) :=
  (Function.Periodic.differentiable_qParam (h := h)).mdifferentiable.comp mdifferentiable_coe

private theorem gamma_qParam_one_periodic :
    Function.Periodic ((fun τ : UpperHalfPlane => Function.Periodic.qParam 1 (τ : ℂ)) ∘
      UpperHalfPlane.ofComplex) 1 := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro τ
  simp [Function.Periodic.qParam, UpperHalfPlane.coe_vadd, mul_add, Complex.exp_add]

private theorem gammaDenominator_periodic :
    Function.Periodic ((fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8) ∘
        UpperHalfPlane.ofComplex) 1 := by
  intro z
  exact congrArg (fun q : ℂ => eulerFunction q ^ 8) (gamma_qParam_one_periodic z)

private theorem gammaDenominator_mdifferentiable :
    MDiff (fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8) := by
  have hη : MDiff (fun τ : UpperHalfPlane => eta (τ : ℂ)) :=
    fun τ => (differentiableAt_eta_of_mem_upperHalfPlaneSet τ.im_pos).mdifferentiableAt.comp
      τ τ.mdifferentiable_coe
  have hfun : (fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8) =
      fun τ : UpperHalfPlane => eta (τ : ℂ) ^ 8 / Function.Periodic.qParam 3 (τ : ℂ) :=
    funext eulerFunction_qParam_one_pow_eight_eq_eta_div_qParam_three
  rw [hfun]
  exact (hη.pow 8).div (gamma_qParam_mdifferentiable 3)
    (fun τ => Function.Periodic.qParam_ne_zero (h := 3) (τ : ℂ))

/-- The analytic gamma denominator tends to one through its locally uniformly
convergent Euler product. -/
theorem tendsto_eulerFunction_qParam_one_pow_eight :
    Tendsto (fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8) atImInfty (𝓝 1) := by
  let G : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - q ^ (n + 1))
  have hG : ContinuousAt G 0 :=
    (differentiableOn_tprod_one_sub_pow.differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simp))).continuousAt
  have ht := (hG.tendsto.comp (qParam_tendsto_atImInfty one_pos)).pow 8
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      G (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8) atImInfty (𝓝 1) := by
    simpa [G] using ht
  convert hlim using 1
  funext τ
  rw [eulerFunction_eq_tprod (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)]

/-- The principal coefficient of the actual width-three gamma regularization is one. -/
theorem tendsto_qParam_three_mul_gamma₂ :
    Tendsto (fun τ : UpperHalfPlane => Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ)
      atImInfty (𝓝 1) := by
  have hE : Tendsto (E₄ : UpperHalfPlane → ℂ) atImInfty (𝓝 1) := by
    simpa using EisensteinSeries.tendsto_E_atImInfty (k := 4)
  have ht := hE.div tendsto_eulerFunction_qParam_one_pow_eight
    (by norm_num : (1 : ℂ) ≠ 0)
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      E₄ τ / eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8)
      atImInfty (𝓝 1) := by
    change Tendsto (fun τ : UpperHalfPlane =>
      E₄ τ / eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8)
      atImInfty (𝓝 ((1 : ℂ) / 1)) at ht
    simpa only [div_one] using ht
  simpa only [qParam_three_mul_gamma₂_eq_div_eulerFunction] using hlim

/-- The actual width-three regularization is periodic with width one. -/
theorem periodic_qParam_three_mul_gamma₂ :
    Function.Periodic ((fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ) ∘ UpperHalfPlane.ofComplex) 1 := by
  have hE : Function.Periodic (E₄ ∘ UpperHalfPlane.ofComplex) 1 := by
    simpa only [Complex.ofReal_one] using
      SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL
  intro z
  simpa only [Function.comp_apply, Pi.div_apply,
    qParam_three_mul_gamma₂_eq_div_eulerFunction] using
    (hE.div gammaDenominator_periodic) z

theorem mdifferentiable_qParam_three_mul_gamma₂ :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ) :=
  (gamma_qParam_mdifferentiable 3).mul mdifferentiable_gamma₂

private theorem gammaDenominator_analyticAt_cuspFunction :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8)) 0 :=
  analyticAt_cuspFunction_zero one_pos gammaDenominator_periodic
    gammaDenominator_mdifferentiable (tendsto_eulerFunction_qParam_one_pow_eight.isBigO_one ℝ)

private theorem regularizedGamma_analyticAt_cuspFunction :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ)) 0 :=
  analyticAt_cuspFunction_zero one_pos periodic_qParam_three_mul_gamma₂
    mdifferentiable_qParam_three_mul_gamma₂ (tendsto_qParam_three_mul_gamma₂.isBigO_one ℝ)

/-- The actual analytic Euler denominator has the full integer pentagonal expansion. -/
theorem qExpansion_eulerFunction_qParam_one_pow_eight_eq_map_int :
    qExpansion 1 (fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8) =
      PowerSeries.map (Int.castRingHom ℂ) gammaDenominatorIntegralQExpansion := by
  have hmap : PowerSeries.map (Int.castRingHom ℂ) gammaDenominatorIntegralQExpansion =
      (PowerSeries.pentagonalSeries ℂ) ^ 8 := by
    simp only [gammaDenominatorIntegralQExpansion, map_pow, PowerSeries.map_pentagonalSeries]
  rw [hmap]
  ext m
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique_unbundled one_pos
    (fun τ => eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8)
    (fun n => ((PowerSeries.pentagonalSeries ℂ) ^ 8).coeff n)
    gammaDenominator_analyticAt_cuspFunction
    (fun τ => PowerSeries.hasSum_pentagonalSeries_pow 8
      (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)) m

/-- The complete q-expansion of the actual width-three regularization of gamma
is the complex image of the integer numerator. -/
theorem qExpansion_qParam_three_mul_gamma₂_eq_map_int :
    qExpansion 1 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ) =
      PowerSeries.map (Int.castRingHom ℂ) gammaIntegralNumerator := by
  have hU : PowerSeries.map (Int.castRingHom ℂ) gammaDenominatorIntegralQExpansion ≠ 0 := by
    intro h
    have hc := congrArg (fun P : PowerSeries ℂ => P.coeff 0) h
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      gammaDenominatorIntegralQExpansion_constantCoeff] at hc
    norm_num at hc
  apply mul_right_cancel₀ hU
  have hmul := UpperHalfPlane.qExpansion_mul regularizedGamma_analyticAt_cuspFunction
    gammaDenominator_analyticAt_cuspFunction
  have hfun : (fun τ : UpperHalfPlane => Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ) *
      (fun τ : UpperHalfPlane => eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 8) =
      (E₄ : UpperHalfPlane → ℂ) := by
    funext τ
    exact qParam_three_mul_gamma₂_mul_eulerFunction τ
  rw [hfun, qExpansion_eulerFunction_qParam_one_pow_eight_eq_map_int] at hmul
  have hformal := congrArg (PowerSeries.map (Int.castRingHom ℂ))
    gammaDenominator_mul_gammaIntegralNumerator
  rw [map_mul, ← qExpansion_E₄_eq_map_int] at hformal
  exact hmul.symm.trans (hformal.symm.trans (mul_comm _ _))

/-- The full integer series converges to the actual gamma regularization at
every upper-half-plane point, not merely in a neighborhood of the cusp. -/
theorem hasSum_gammaIntegralNumerator (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (gammaIntegralNumerator.coeff n : ℂ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ) := by
  have h := τ.hasSum_qExpansion one_pos periodic_qParam_three_mul_gamma₂
    mdifferentiable_qParam_three_mul_gamma₂ (tendsto_qParam_three_mul_gamma₂.isBigO_one ℝ)
  rw [qExpansion_qParam_three_mul_gamma₂_eq_map_int] at h
  simpa only [PowerSeries.coeff_map, smul_eq_mul, Int.coe_castRingHom] using h

theorem qExpansion_qParam_three_mul_gamma₂_constantCoeff :
    (qExpansion 1 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 3 (τ : ℂ) * gamma₂ τ)).constantCoeff = 1 := by
  rw [qExpansion_qParam_three_mul_gamma₂_eq_map_int,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, gammaIntegralNumerator_constantCoeff, map_one]

end ModularForm
