/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.JInvariant.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Polynomial Expressions in the Analytic j-Invariant

A level-one modular form of weight `12n`, divided by `Δⁿ`, is a polynomial in
`j` of degree at most `n`. Subtract its constant term times `E₄^(3n)`, divide
the remaining cusp form by `Δ`, and induct on `n`. This uses mathlib's existing
level-one weight-zero constancy and cusp-form/discriminant equivalence.
For a holomorphic weight-zero form with growth `O(jⁿ)`, multiplication by `Δⁿ`
is proved bounded at all cusps, giving a modular form of weight `12n` and hence
the polynomial representation. A separate regularization hypothesis is not needed.

This proves the polynomial-structure step needed for general modular
polynomials. It does not yet show that symmetric functions of level-N
translates of `j` have the necessary modularity, cusp bounds, or integral q-expansions.
-/

open Polynomial EisensteinSeries UpperHalfPlane Asymptotics
open scoped MatrixGroups Manifold ModularForm

namespace ModularForm

/-- A form of weight `12n` is `Δⁿ` times a polynomial in `j` of degree at most
`n`. This is independent of complex multiplication and of general modular
polynomials. -/
theorem exists_polynomial_jInvariant (n : ℕ) (f : ModularForm 𝒮ℒ (12 * (n : ℤ))) :
    ∃ P : ℂ[X], P.natDegree ≤ n ∧
      ∀ τ : UpperHalfPlane, f τ = discriminant τ ^ n * P.eval (jInvariant τ) := by
  induction n with
  | zero =>
    change ModularForm 𝒮ℒ 0 at f
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const f
    refine ⟨C c, by simp, ?_⟩
    intro τ
    simpa using congrFun hc τ
  | succ n ih =>
    let E : ModularForm 𝒮ℒ (12 * ((n + 1 : ℕ) : ℤ)) :=
      ModularForm.mcast (by push_cast; ring) (E₄.pow (3 * (n + 1)))
    have hEzero : (qExpansion 1 E).coeff 0 = 1 := by
      have hpow : qExpansion 1 E = (qExpansion 1 E₄) ^ (3 * (n + 1)) := by
        exact ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ _
      rw [hpow, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        E_qExpansion_coeff_zero _ ⟨2, rfl⟩, one_pow]
    let c := (qExpansion 1 f).coeff 0
    let g := f - c • E
    have hg : (qExpansion 1 g).coeff 0 = 0 := by
      have hq : qExpansion 1 g = qExpansion 1 f - c • qExpansion 1 E := by
        change qExpansion 1 ((f : UpperHalfPlane → ℂ) -
          ((c • E : ModularForm 𝒮ℒ (12 * ((n + 1 : ℕ) : ℤ))) : UpperHalfPlane → ℂ)) = _
        rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL f (c • E)]
        change qExpansion 1 f - qExpansion 1 (c • (E : UpperHalfPlane → ℂ)) = _
        rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c E]
      rw [hq, map_sub, PowerSeries.coeff_smul, hEzero]
      simp [c]
    let F : CuspForm 𝒮ℒ (12 * ((n + 1 : ℕ) : ℤ)) := toCuspForm g hg
    let G : ModularForm 𝒮ℒ (12 * (n : ℤ)) :=
      ModularForm.mcast (by push_cast; ring) (CuspForm.discriminantEquiv F)
    obtain ⟨P, hP, hGP⟩ := ih G
    refine ⟨P + C c * X ^ (n + 1), ?_, ?_⟩
    · apply natDegree_add_le_of_degree_le (hP.trans (by omega))
      exact natDegree_mul_le.trans (by simp)
    · intro τ
      have hG : discriminant τ * G τ = f τ - c * E τ := by
        change discriminant τ * (CuspForm.discriminantEquiv F) τ = _
        rw [discriminant_mul_discriminantEquiv_apply]
        rfl
      have hJ : jInvariant τ * discriminant τ = E₄ τ ^ 3 := by
        rw [jInvariant]
        exact div_mul_cancel₀ _ (discriminant_ne_zero τ)
      have hE : E τ = discriminant τ ^ (n + 1) * jInvariant τ ^ (n + 1) := by
        simp only [E, coe_mcast, coe_pow, Pi.pow_apply]
        rw [pow_mul, ← hJ, mul_pow]
        ring
      rw [hGP τ, hE] at hG
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      rw [pow_succ]
      linear_combination -hG

/-- A function whose product with `Δⁿ` is a weight `12n` level-one modular form
is a polynomial in `j` of degree at most `n`. The regularization is a genuine
analytic hypothesis; no cusp-bound theorem is silently assumed here. -/
theorem exists_polynomial_jInvariant_of_discriminant_regularization
    (φ : UpperHalfPlane → ℂ) (n : ℕ) (f : ModularForm 𝒮ℒ (12 * (n : ℤ)))
    (hf : ∀ τ, f τ = discriminant τ ^ n * φ τ) :
    ∃ P : ℂ[X], P.natDegree ≤ n ∧ ∀ τ, φ τ = P.eval (jInvariant τ) := by
  obtain ⟨P, hP, hPf⟩ := exists_polynomial_jInvariant n f
  refine ⟨P, hP, fun τ => ?_⟩
  exact mul_left_cancel₀ (pow_ne_zero n (discriminant_ne_zero τ))
    ((hf τ).symm.trans (hPf τ))

/-- A holomorphic weight-zero level-one function growing at most like `jⁿ`
becomes a genuine weight `12n` modular form after multiplication by `Δⁿ`.
In particular, boundedness at all cusps is proved, not assumed separately. -/
theorem exists_discriminant_regularization_of_isBigO_jInvariant
    (φ : SlashInvariantForm 𝒮ℒ 0) (hφ : MDiff (φ : UpperHalfPlane → ℂ)) (n : ℕ)
    (hgrowth : (φ : UpperHalfPlane → ℂ) =O[atImInfty] (fun τ => jInvariant τ ^ n)) :
    ∃ f : ModularForm 𝒮ℒ (12 * (n : ℤ)),
      ∀ τ, f τ = discriminant τ ^ n * φ τ := by
  let d : ModularForm 𝒮ℒ (12 * (n : ℤ)) :=
    ModularForm.mcast (by ring) ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow n)
  have hd : (d : UpperHalfPlane → ℂ) = fun τ => discriminant τ ^ n := by
    funext τ
    simp only [d, coe_mcast, coe_pow, Pi.pow_apply]
    rfl
  have hslash (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) :
      (fun τ => discriminant τ ^ n * φ τ) ∣[12 * (n : ℤ)] γ =
        fun τ => discriminant τ ^ n * φ τ := by
    have h := (d.toSlashInvariantForm.mul φ).slash_action_eq' γ hγ
    change ((d : UpperHalfPlane → ℂ) * (φ : UpperHalfPlane → ℂ)) ∣[12 * (n : ℤ) + 0] γ =
      (d : UpperHalfPlane → ℂ) * (φ : UpperHalfPlane → ℂ) at h
    rw [add_zero, hd] at h
    change (fun τ => discriminant τ ^ n * φ τ) ∣[12 * (n : ℤ)] γ =
      (fun τ => discriminant τ ^ n * φ τ) at h
    exact h
  have hmajorant : (fun τ => discriminant τ ^ n * jInvariant τ ^ n) =O[atImInfty]
      (fun _ : UpperHalfPlane => (1 : ℂ)) := by
    have h := (ModularFormClass.tendsto_atImInfty (E₄.pow (3 * n))
      one_pos one_mem_strictPeriods_SL).isBigO_one ℂ
    have heq : (E₄.pow (3 * n) : UpperHalfPlane → ℂ) =
        fun τ => discriminant τ ^ n * jInvariant τ ^ n := by
      funext τ
      simp only [coe_pow, Pi.pow_apply]
      have hJ : jInvariant τ * discriminant τ = E₄ τ ^ 3 := by
        rw [jInvariant]
        exact div_mul_cancel₀ _ (discriminant_ne_zero τ)
      rw [pow_mul, ← hJ, mul_pow]
      ring
    rw [heq] at h
    exact h
  have hb := ((isBigO_refl (fun τ : UpperHalfPlane => discriminant τ ^ n) atImInfty).mul
    hgrowth).trans hmajorant
  have hbounded : IsBoundedAtImInfty (fun τ => discriminant τ ^ n * φ τ) := by
    change (fun τ => discriminant τ ^ n * φ τ) =O[atImInfty]
      (fun _ : UpperHalfPlane => (1 : ℝ))
    exact (isBigO_one_iff ℝ).mpr ((isBigO_one_iff ℂ).mp hb)
  refine ⟨{ toFun := fun τ => discriminant τ ^ n * φ τ
            slash_action_eq' := hslash
            holo' := ?_
            bdd_at_cusps' := ?_ }, fun _ => rfl⟩
  · have h := d.holo'.mul hφ
    change MDiff ((d : UpperHalfPlane → ℂ) * (φ : UpperHalfPlane → ℂ)) at h
    rw [hd] at h
    exact h
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SL_slash _ γ, hslash γ ⟨γ, rfl⟩]
    exact hbounded

/-- A holomorphic level-one modular function with growth `O(jⁿ)` is a
polynomial in `j` of degree at most `n`. Cusp regularization is derived from
the growth estimate, rather than supplied as a further hypothesis. -/
theorem exists_polynomial_jInvariant_of_isBigO
    (φ : SlashInvariantForm 𝒮ℒ 0) (hφ : MDiff (φ : UpperHalfPlane → ℂ)) (n : ℕ)
    (hgrowth : (φ : UpperHalfPlane → ℂ) =O[atImInfty] (fun τ => jInvariant τ ^ n)) :
    ∃ P : ℂ[X], P.natDegree ≤ n ∧ ∀ τ, φ τ = P.eval (jInvariant τ) := by
  obtain ⟨f, hf⟩ := exists_discriminant_regularization_of_isBigO_jInvariant φ hφ n hgrowth
  exact exists_polynomial_jInvariant_of_discriminant_regularization φ n f hf

end ModularForm
