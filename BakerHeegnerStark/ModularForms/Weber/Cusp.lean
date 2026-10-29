/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.QExpansion
import BakerHeegnerStark.ModularForms.Weber.Bounds

/-!
# The Weber square at every cusp

For every integral modular matrix `g`, the actual function
`qParam 24 τ * weberF (g • τ)^2` is periodic of width twenty-four, holomorphic
on the upper half-plane, and bounded at infinity. Its actual cusp function
is analytic at zero. The unregularized Weber-square cusp function is therefore
meromorphic, with a punctured analytic numerator divided by the q-coordinate.

The uniform bound follows from the actual Weber cubic and the principal part
of `j`. No CM, squarefreeness, class-number, or CM field-membership hypothesis
is used. Together with `ModularForms/Weber/Modularity.lean` and `ModularForms/Weber/QExpansion.lean`, this
supplies the transformation, cusp, and rational-series data for the remaining
arithmetic CM evaluation argument, not that argument itself.
-/

open scoped Topology Manifold MatrixGroups
open UpperHalfPlane Filter Asymptotics
namespace ModularForm

private theorem weber_cusp_qParam_twentyFour_pow (z : ℂ) :
    Function.Periodic.qParam 24 z ^ 24 = Function.Periodic.qParam 1 z := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- One actual width-twenty-four q-factor bounds the Weber square at every cusp. -/
theorem isBoundedAtImInfty_qParam_twentyFour_mul_weberF_sq_smul (g : SL(2, ℤ)) :
    IsBoundedAtImInfty (fun τ : UpperHalfPlane => Function.Periodic.qParam 24 (τ : ℂ) *
      weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2) := by
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      ‖Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ‖) atImInfty (𝓝 (1 : ℝ)) := by
    simpa using tendsto_qParam_mul_jInvariant.norm
  have hnear := Metric.tendsto_nhds.mp hlim 1 (by norm_num : (0 : ℝ) < 1)
  apply IsBigO.of_pow (n := 24) (by decide)
  apply IsBigO.of_bound 1040
  filter_upwards [hnear] with τ hτ
  simp only [Pi.pow_apply, Pi.one_apply, norm_pow, one_pow, norm_one, mul_one]
  have hJ : ‖Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ‖ ≤ 2 := by
    have hh := (abs_lt.mp (show |‖Function.Periodic.qParam 1 (τ : ℂ) *
      jInvariant τ‖ - 1| < 1 by simpa only [Real.dist_eq] using hτ)).2
    linarith
  have hF := norm_weberF_sq_smul_pow_24_le g τ
  have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ≤ 1 :=
    (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos).le
  have hqpow : ‖Function.Periodic.qParam 24 (τ : ℂ)‖ ^ 24 =
      ‖Function.Periodic.qParam 1 (τ : ℂ)‖ := by
    rw [← norm_pow, weber_cusp_qParam_twentyFour_pow]
  rw [norm_mul, mul_pow, hqpow]
  have hmul := mul_le_mul_of_nonneg_left hF
    (norm_nonneg (Function.Periodic.qParam 1 (τ : ℂ)))
  rw [norm_mul] at hJ
  nlinarith


/-- The regularized Weber square has width twenty-four after every modular transform. -/
theorem periodic_qParam_twentyFour_mul_weberF_sq_smul (g : SL(2, ℤ)) :
    Function.Periodic ((fun τ : UpperHalfPlane => Function.Periodic.qParam 24 (τ : ℂ) *
      weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2) ∘ UpperHalfPlane.ofComplex) 24 := by
  have hq : Function.Periodic ((fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ)) ∘ UpperHalfPlane.ofComplex) 24 := by
    apply UpperHalfPlane.periodic_comp_ofComplex
    intro τ
    simp [Function.Periodic.qParam, UpperHalfPlane.coe_vadd, mul_add, add_div, Complex.exp_add]
  have hf : Function.Periodic ((fun τ : UpperHalfPlane =>
      weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2) ∘ UpperHalfPlane.ofComplex) 24 := by
    apply UpperHalfPlane.periodic_comp_ofComplex
    intro τ
    have hT := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (24 : ℤ) 24 dvd_rfl
    have hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24))
        (ModularGroup.T ^ (24 : ℤ)) = 1 := CongruenceSubgroup.Gamma_mem'.mp hT
    have hact := weberF_sq_smul_of_mod_twenty_four_eq
      (g * ModularGroup.T ^ (24 : ℤ)) g (by rw [map_mul, hred, mul_one]) τ
    norm_num only
    simpa only [mul_smul, UpperHalfPlane.modular_T_zpow_smul, Int.cast_ofNat] using hact
  exact hq.mul hf

/-- The regularized Weber square is holomorphic after every modular transform. -/
theorem mdifferentiable_qParam_twentyFour_mul_weberF_sq_smul (g : SL(2, ℤ)) :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam 24 (τ : ℂ) *
      weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2) := by
  have hq : MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam 24 (τ : ℂ)) :=
    (Function.Periodic.differentiable_qParam (h := 24)).mdifferentiable.comp mdifferentiable_coe
  have hW : MDiff (fun τ : UpperHalfPlane => weberF (τ : ℂ)) :=
    fun τ => (analyticOnNhd_weberF (τ : ℂ) τ.im_pos).differentiableAt.mdifferentiableAt.comp
      τ τ.mdifferentiable_coe
  have hg : MDiff (fun τ : UpperHalfPlane => g • τ) := by
    simpa using UpperHalfPlane.mdifferentiable_smul
      (g := (g : GL (Fin 2) ℝ)) (by simp)
  exact hq.mul ((hW.pow 2).comp hg)

/-- The actual regularized cusp function is analytic at zero at every cusp. -/
theorem analyticAt_cuspFunction_regularized_weberF_sq_smul (g : SL(2, ℤ)) :
    AnalyticAt ℂ (cuspFunction 24 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) *
        weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2)) 0 :=
  analyticAt_cuspFunction_zero (by norm_num)
    (periodic_qParam_twentyFour_mul_weberF_sq_smul g)
    (mdifferentiable_qParam_twentyFour_mul_weberF_sq_smul g)
    (isBoundedAtImInfty_qParam_twentyFour_mul_weberF_sq_smul g)

/-- The actual unregularized Weber-square cusp function is meromorphic at every cusp. -/
theorem meromorphicAt_cuspFunction_weberF_sq_smul (g : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction 24 (fun τ : UpperHalfPlane =>
      weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2)) 0 := by
  apply UpperHalfPlane.meromorphicAt_cuspFunction_of_regularization
    (by norm_num : (0 : ℝ) < 24) _ 1
  simpa only [pow_one] using analyticAt_cuspFunction_regularized_weberF_sq_smul g

end ModularForm
