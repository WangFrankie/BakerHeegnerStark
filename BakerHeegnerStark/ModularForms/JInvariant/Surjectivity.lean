/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.QExpansion.Integral
import BakerHeegnerStark.ModularForms.JInvariant.Polynomial

/-!
# Surjectivity of the Analytic j-Invariant

If a complex value is omitted, the reciprocal of its difference from `j` is
holomorphic and modular invariant, with limit zero at the cusp. The proved
polynomial representation at degree zero makes this reciprocal constant,
contradicting its nonvanishing. This uses no complex multiplication theorem
or modular polynomial hypothesis.
-/

open UpperHalfPlane Polynomial Filter Asymptotics
open scoped MatrixGroups Manifold Topology

namespace ModularForm

/-- The reciprocal of `j-x` tends to zero at the cusp, for every complex `x`.
Possible zeros away from the cusp do not affect this limit. -/
theorem tendsto_inv_jInvariant_sub (x : ℂ) :
    Tendsto (fun τ : UpperHalfPlane => (jInvariant τ - x)⁻¹) atImInfty (𝓝 0) := by
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have hdenom := tendsto_qParam_mul_jInvariant.sub (hq.mul_const x)
  have hquot : Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 (τ : ℂ) /
        (Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ -
          Function.Periodic.qParam 1 (τ : ℂ) * x)) atImInfty (𝓝 0) := by
    have h := hq.div hdenom (by simp)
    change Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 (τ : ℂ) /
        (Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ -
          Function.Periodic.qParam 1 (τ : ℂ) * x))
      atImInfty (𝓝 ((0 : ℂ) / (1 - 0 * x))) at h
    simpa only [zero_div] using h
  convert hquot using 1
  funext τ
  rw [← mul_sub, div_mul_eq_div_div,
    div_self (Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ)), one_div]

/-- Every complex number is an actual analytic j-value. -/
theorem jInvariant_surjective : Function.Surjective jInvariant := by
  classical
  intro x
  by_contra hx
  have hneq (τ : UpperHalfPlane) : jInvariant τ ≠ x := fun h => hx ⟨τ, h⟩
  let φ : SlashInvariantForm 𝒮ℒ 0 :=
    { toFun := fun τ => (jInvariant τ - x)⁻¹
      slash_action_eq' := by
        intro γ hγ
        obtain ⟨γ, rfl⟩ := hγ
        change ((fun τ : UpperHalfPlane => (jInvariant τ - x)⁻¹) ∣[(0 : ℤ)] γ) =
          (fun τ : UpperHalfPlane => (jInvariant τ - x)⁻¹)
        funext τ
        simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one, jInvariant_smul] }
  have hφ : MDiff (φ : UpperHalfPlane → ℂ) := by
    change MDiff (fun τ : UpperHalfPlane => (jInvariant τ - x)⁻¹)
    have hsub : MDiff (fun τ : UpperHalfPlane => jInvariant τ - x) :=
      mdifferentiable_jInvariant.sub mdifferentiable_const
    exact hsub.inv (fun τ => sub_ne_zero.mpr (hneq τ))
  have hgrowth : (φ : UpperHalfPlane → ℂ) =O[atImInfty]
      (fun τ => jInvariant τ ^ 0) := by
    change (fun τ : UpperHalfPlane => (jInvariant τ - x)⁻¹) =O[atImInfty] _
    simpa only [pow_zero] using (tendsto_inv_jInvariant_sub x).isBigO_one ℂ
  obtain ⟨P, hdegree, hrep⟩ := exists_polynomial_jInvariant_of_isBigO φ hφ 0 hgrowth
  have hconst (τ : UpperHalfPlane) : (jInvariant τ - x)⁻¹ = P.coeff 0 := by
    have h := hrep τ
    rw [eq_C_of_natDegree_le_zero hdegree, eval_C] at h
    exact h
  have hlimc : Tendsto (fun τ : UpperHalfPlane => (jInvariant τ - x)⁻¹)
      atImInfty (𝓝 (P.coeff 0)) := by
    simpa only [hconst] using (tendsto_const_nhds : Tendsto
      (fun _ : UpperHalfPlane => P.coeff 0) atImInfty (𝓝 (P.coeff 0)))
  have hzero : P.coeff 0 = 0 :=
    tendsto_nhds_unique hlimc (tendsto_inv_jInvariant_sub x)
  exact inv_ne_zero (sub_ne_zero.mpr (hneq (UpperHalfPlane.ofComplex Complex.I)))
    ((hconst (UpperHalfPlane.ofComplex Complex.I)).trans hzero)

end ModularForm
