/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.Branches
import BakerHeegnerStark.ModularForms.Weber.BranchQExpansion
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The function space of the three Weber squares

The complete analytic q-expansions distinguish the three actual functions over
`ℂ`. Consequently their span over `ℚ(zeta48²)` has canonical, unique coefficients.
Transporting coefficient automorphisms through this basis defines an action on
that actual function space. This coefficient action is not an assertion about
Galois automorphisms of evaluated CM values.
-/

open BakerHeegnerStark UpperHalfPlane Filter Complex Module
open scoped Topology Manifold ModularForm MatrixGroups

noncomputable section
namespace ModularForm

/-- The common cusp regularization of an actual Weber-square branch. -/
def regularizedWeberSquareBranch (i : Fin 3) (τ : UpperHalfPlane) : ℂ :=
  Function.Periodic.qParam 24 (τ : ℂ) * weberSquareBranch i τ

/-- The complete integer series of each common-width regularization. -/
def weberSquareBranchIntegralQExpansion (i : Fin 3) : PowerSeries ℤ :=
  ![weberSquareIntegralQExpansion, weberF₁SquareIntegralQExpansion,
    weberF₂SquareIntegralQExpansion] i

private theorem regularizedWeberSquareBranch_analytic (i : Fin 3) :
    AnalyticAt ℂ (cuspFunction 24 (regularizedWeberSquareBranch i)) 0 := by
  fin_cases i
  · apply analyticAt_cuspFunction_zero (by norm_num : (0 : ℝ) < 24)
      (by convert periodic_qParam_twentyFour_mul_weberF_sq.nat_mul 12 using 1; norm_num)
      mdifferentiable_qParam_twentyFour_mul_weberF_sq
      (tendsto_qParam_twentyFour_mul_weberF_sq.isBigO_one ℝ)
  · apply analyticAt_cuspFunction_zero (by norm_num : (0 : ℝ) < 24)
      (by convert periodic_qParam_twentyFour_mul_weberF₁_sq.nat_mul 12 using 1; norm_num)
      mdifferentiable_qParam_twentyFour_mul_weberF₁_sq
      (tendsto_qParam_twentyFour_mul_weberF₁_sq.isBigO_one ℝ)
  · exact analyticAt_cuspFunction_zero (by norm_num : (0 : ℝ) < 24)
      periodic_qParam_twentyFour_mul_weberF₂_sq
      mdifferentiable_qParam_twentyFour_mul_weberF₂_sq
      (tendsto_qParam_twentyFour_mul_weberF₂_sq.isBigO_one ℝ)

/-- The q-expansions used below are the entire previously identified series. -/
theorem qExpansion_regularizedWeberSquareBranch (i : Fin 3) :
    qExpansion 24 (regularizedWeberSquareBranch i) =
      PowerSeries.map (Int.castRingHom ℂ) (weberSquareBranchIntegralQExpansion i) := by
  fin_cases i
  · exact qExpansion_twentyFour_regularized_weberF_sq_eq_map_int
  · exact qExpansion_twentyFour_regularized_weberF₁_sq_eq_map_int
  · exact qExpansion_twentyFour_regularized_weberF₂_sq_eq_map_int

/-- Original and first branches have no degree-three term in the common parameter. -/
theorem weberSquareIntegralQExpansion_coeff_three :
    weberSquareIntegralQExpansion.coeff 3 = 0 :=
  PowerSeries.coeff_expand_of_not_dvd 12 (by decide) _ (by decide)

theorem weberF₁SquareIntegralQExpansion_coeff_three :
    weberF₁SquareIntegralQExpansion.coeff 3 = 0 :=
  PowerSeries.coeff_expand_of_not_dvd 12 (by decide) _ (by decide)

/-- The second branch has no degree-twelve term in the common parameter. -/
theorem weberF₂SquareIntegralQExpansion_coeff_twelve :
    weberF₂SquareIntegralQExpansion.coeff 12 = 0 := by
  rw [weberF₂SquareIntegralQExpansion, mul_assoc, PowerSeries.coeff_ofNat_mul]
  change 2 * (PowerSeries.X ^ 3 *
    PowerSeries.expand 24 (by decide) weberF₂SquareIntegralNumerator).coeff (9 + 3) = 0
  rw [PowerSeries.coeff_X_pow_mul,
    PowerSeries.coeff_expand_of_not_dvd 24 (by decide) _ (by decide), mul_zero]

private theorem regularizedWeberSquareBranch_smul_analytic (a : ℂ) (i : Fin 3) :
    AnalyticAt ℂ (cuspFunction 24 (a • regularizedWeberSquareBranch i)) 0 := by
  rw [UpperHalfPlane.cuspFunction_smul (regularizedWeberSquareBranch_analytic i).continuousAt]
  exact (regularizedWeberSquareBranch_analytic i).const_smul

private theorem qExpansion_regularizedWeberSquareBranch_linearCombination (c : Fin 3 → ℂ) :
    qExpansion 24 (c 0 • regularizedWeberSquareBranch 0 +
      c 1 • regularizedWeberSquareBranch 1 + c 2 • regularizedWeberSquareBranch 2) =
      c 0 • PowerSeries.map (Int.castRingHom ℂ) weberSquareIntegralQExpansion +
      c 1 • PowerSeries.map (Int.castRingHom ℂ) weberF₁SquareIntegralQExpansion +
      c 2 • PowerSeries.map (Int.castRingHom ℂ) weberF₂SquareIntegralQExpansion := by
  have h01 : AnalyticAt ℂ (cuspFunction 24
      (c 0 • regularizedWeberSquareBranch 0 + c 1 • regularizedWeberSquareBranch 1)) 0 := by
    rw [UpperHalfPlane.cuspFunction_add
      (regularizedWeberSquareBranch_smul_analytic (c 0) 0).continuousAt
      (regularizedWeberSquareBranch_smul_analytic (c 1) 1).continuousAt]
    exact (regularizedWeberSquareBranch_smul_analytic (c 0) 0).add
      (regularizedWeberSquareBranch_smul_analytic (c 1) 1)
  rw [UpperHalfPlane.qExpansion_add h01
      (regularizedWeberSquareBranch_smul_analytic (c 2) 2),
    UpperHalfPlane.qExpansion_add
      (regularizedWeberSquareBranch_smul_analytic (c 0) 0)
      (regularizedWeberSquareBranch_smul_analytic (c 1) 1)]
  simp only [UpperHalfPlane.qExpansion_smul (regularizedWeberSquareBranch_analytic _),
    qExpansion_regularizedWeberSquareBranch]
  rfl

/-- The three actual functions are complex-linearly independent: their full
q-expansions give the independent coefficient equations in degrees `0, 3, 12`. -/
theorem linearIndependent_weberSquareBranch : LinearIndependent ℂ weberSquareBranch := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hreg : c 0 • regularizedWeberSquareBranch 0 +
      c 1 • regularizedWeberSquareBranch 1 + c 2 • regularizedWeberSquareBranch 2 = 0 := by
    funext τ
    have h := congrFun hc τ
    simp only [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at h
    change c 0 * (Function.Periodic.qParam 24 (τ : ℂ) * weberSquareBranch 0 τ) +
      c 1 * (Function.Periodic.qParam 24 (τ : ℂ) * weberSquareBranch 1 τ) +
      c 2 * (Function.Periodic.qParam 24 (τ : ℂ) * weberSquareBranch 2 τ) = 0
    linear_combination Function.Periodic.qParam 24 (τ : ℂ) * h
  have hs := qExpansion_regularizedWeberSquareBranch_linearCombination c
  rw [hreg, UpperHalfPlane.qExpansion_zero] at hs
  have h0 := congrArg (fun P : PowerSeries ℂ => P.coeff 0) hs
  have h3 := congrArg (fun P : PowerSeries ℂ => P.coeff 3) hs
  have h12 := congrArg (fun P : PowerSeries ℂ => P.coeff 12) hs
  simp only [map_add, PowerSeries.coeff_smul, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, map_zero,
    weberSquareIntegralQExpansion_constantCoeff, weberF₁SquareIntegralQExpansion_constantCoeff,
    weberF₂SquareIntegralQExpansion_constantCoeff, Int.coe_castRingHom,
    Int.cast_one, smul_eq_mul, mul_one, mul_zero, add_zero] at h0
  simp only [map_add, PowerSeries.coeff_smul, PowerSeries.coeff_map, map_zero,
    weberSquareIntegralQExpansion_coeff_three, weberF₁SquareIntegralQExpansion_coeff_three,
    weberF₂SquareIntegralQExpansion_coeff_three, Int.coe_castRingHom,
    Int.cast_ofNat, smul_eq_mul, mul_zero, zero_add] at h3
  simp only [map_add, PowerSeries.coeff_smul, PowerSeries.coeff_map, map_zero,
    weberSquareIntegralQExpansion_coeff_twelve, weberF₁SquareIntegralQExpansion_coeff_twelve,
    weberF₂SquareIntegralQExpansion_coeff_twelve, Int.coe_castRingHom,
    Int.cast_ofNat, Int.cast_neg, smul_eq_mul, mul_zero, add_zero] at h12
  have hc0 : c 0 = 0 := by linear_combination -1 / 4 * h12 - 1 / 2 * h0
  have hc1 : c 1 = 0 := by linear_combination 1 / 4 * h12 - 1 / 2 * h0
  have hc2 : c 2 = 0 := by linear_combination -1 / 2 * h3
  fin_cases i <;> assumption

/-- The actual subfield of `ℂ` generated by the modular phase `zeta48²`. -/
def weberBranchCoefficientField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {zeta48 ^ 2}

/-- The modular phase regarded as an element of the actual coefficient field. -/
def weberBranchPhase : weberBranchCoefficientField :=
  ⟨zeta48 ^ 2, IntermediateField.mem_adjoin_simple_self ℚ _⟩

@[simp]
theorem coe_weberBranchPhase : (weberBranchPhase : ℂ) = zeta48 ^ 2 := rfl

@[simp]
theorem coe_weberBranchPhase_zpow (k : ℤ) :
    ((weberBranchPhase ^ k : weberBranchCoefficientField) : ℂ) = (zeta48 ^ 2) ^ k := by
  change algebraMap weberBranchCoefficientField ℂ (weberBranchPhase ^ k) = _
  rw [map_zpow₀]
  rfl

/-- The span consists of actual complex-valued functions, not formal tuples. -/
def weberBranchSpace : Submodule weberBranchCoefficientField (UpperHalfPlane → ℂ) :=
  Submodule.span weberBranchCoefficientField (Set.range weberSquareBranch)

theorem linearIndependent_weberSquareBranch_coefficientField :
    LinearIndependent weberBranchCoefficientField weberSquareBranch :=
  linearIndependent_weberSquareBranch.restrict_scalars' weberBranchCoefficientField

/-- The actual branches form a basis of their concrete function span. -/
def weberBranchBasis : Basis (Fin 3) weberBranchCoefficientField weberBranchSpace :=
  Basis.span linearIndependent_weberSquareBranch_coefficientField

@[simp]
theorem coe_weberBranchBasis (i : Fin 3) :
    (weberBranchBasis i : UpperHalfPlane → ℂ) = weberSquareBranch i :=
  Basis.coe_span_apply _ _

/-- Canonical coefficients identify the three-dimensional tuple space with the
actual function span; injectivity follows from the analytic independence proof. -/
def weberBranchCoefficientEquiv :
    (Fin 3 → weberBranchCoefficientField) ≃ₗ[weberBranchCoefficientField] weberBranchSpace :=
  weberBranchBasis.equivFun.symm

/-- Evaluation of the canonical coefficient equivalence is the finite function sum. -/
theorem weberBranchCoefficientEquiv_apply (c : Fin 3 → weberBranchCoefficientField)
    (τ : UpperHalfPlane) :
    (weberBranchCoefficientEquiv c : UpperHalfPlane → ℂ) τ =
      ∑ i : Fin 3, (c i : ℂ) * weberSquareBranch i τ := by
  simp [weberBranchCoefficientEquiv, Basis.equivFun_symm_apply, Finset.sum_apply,
    IntermediateField.smul_def, smul_eq_mul]

/-- Every actual function in the span has the displayed canonical expansion. -/
theorem weberBranchSpace_eval (f : weberBranchSpace) (τ : UpperHalfPlane) :
    (f : UpperHalfPlane → ℂ) τ =
      ∑ i : Fin 3, (weberBranchCoefficientEquiv.symm f i : ℂ) *
        weberSquareBranch i τ := by
  simpa only [LinearEquiv.apply_symm_apply] using
    weberBranchCoefficientEquiv_apply (weberBranchCoefficientEquiv.symm f) τ

/-- These coefficients are unique as coefficients of actual functions. -/
theorem weberBranchSpace_existsUnique_coefficients (f : weberBranchSpace) :
    ∃! c : Fin 3 → weberBranchCoefficientField, ∀ τ : UpperHalfPlane,
      (f : UpperHalfPlane → ℂ) τ =
        ∑ i : Fin 3, (c i : ℂ) * weberSquareBranch i τ := by
  refine ⟨weberBranchCoefficientEquiv.symm f, weberBranchSpace_eval f, ?_⟩
  intro c hc
  apply weberBranchCoefficientEquiv.injective
  apply Subtype.ext
  funext τ
  rw [weberBranchCoefficientEquiv_apply, LinearEquiv.apply_symm_apply]
  exact (hc τ).symm

/-- Coefficient automorphisms act on the actual function span via its canonical
basis. This is a rational-linear equivalence, not pointwise Galois action on
complex or CM values, and it uses no passage of an automorphism through a series. -/
def weberBranchCoefficientAction
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField) :
    weberBranchSpace ≃ₗ[ℚ] weberBranchSpace :=
  (weberBranchCoefficientEquiv.symm.restrictScalars ℚ).trans
    ((LinearEquiv.piCongrRight fun _ : Fin 3 => σ.toLinearEquiv).trans
      (weberBranchCoefficientEquiv.restrictScalars ℚ))

theorem weberBranchCoefficientAction_apply
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (f : weberBranchSpace) :
    weberBranchCoefficientAction σ f =
      weberBranchCoefficientEquiv (fun i => σ (weberBranchCoefficientEquiv.symm f i)) :=
  rfl

@[simp]
theorem weberBranchCoefficientAction_coefficients
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (f : weberBranchSpace) (i : Fin 3) :
    weberBranchCoefficientEquiv.symm (weberBranchCoefficientAction σ f) i =
      σ (weberBranchCoefficientEquiv.symm f i) := by
  rw [weberBranchCoefficientAction_apply, LinearEquiv.symm_apply_apply]

/-- The coefficient action has this finite-sum evaluation formula. -/
theorem weberBranchCoefficientAction_eval
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (f : weberBranchSpace) (τ : UpperHalfPlane) :
    (weberBranchCoefficientAction σ f : UpperHalfPlane → ℂ) τ =
      ∑ i : Fin 3, (σ (weberBranchCoefficientEquiv.symm f i) : ℂ) *
        weberSquareBranch i τ := by
  rw [weberBranchCoefficientAction_apply, weberBranchCoefficientEquiv_apply]

/-- The rational-linear action is semilinear for the actual coefficient field. -/
theorem weberBranchCoefficientAction_smul
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (a : weberBranchCoefficientField) (f : weberBranchSpace) :
    weberBranchCoefficientAction σ (a • f) = σ a • weberBranchCoefficientAction σ f := by
  apply weberBranchCoefficientEquiv.symm.injective
  ext i
  simp only [weberBranchCoefficientAction_coefficients, map_smul, Pi.smul_apply,
    smul_eq_mul, map_mul]

@[simp]
theorem weberBranchCoefficientAction_one (f : weberBranchSpace) :
    weberBranchCoefficientAction (1 : weberBranchCoefficientField ≃ₐ[ℚ]
      weberBranchCoefficientField) f = f := by
  apply weberBranchCoefficientEquiv.symm.injective
  ext i
  simp

/-- Composition is the actual composition of coefficient-field automorphisms. -/
theorem weberBranchCoefficientAction_mul
    (σ ρ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (f : weberBranchSpace) :
    weberBranchCoefficientAction (σ * ρ) f =
      weberBranchCoefficientAction σ (weberBranchCoefficientAction ρ f) := by
  apply weberBranchCoefficientEquiv.symm.injective
  ext i
  simp

/-- Every actual basis branch is fixed by coefficient action. -/
@[simp]
theorem weberBranchCoefficientAction_basis
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField) (i : Fin 3) :
    weberBranchCoefficientAction σ (weberBranchBasis i) = weberBranchBasis i := by
  apply weberBranchCoefficientEquiv.symm.injective
  ext j
  rw [weberBranchCoefficientAction_coefficients]
  simp [weberBranchCoefficientEquiv, Basis.equivFun_self, apply_ite]

/-- Every integral modular transform of every branch belongs to the actual span. -/
theorem weberSquareBranch_smul_mem_weberBranchSpace (g : SL(2, ℤ)) (i : Fin 3) :
    (fun τ : UpperHalfPlane => weberSquareBranch i (g • τ)) ∈ weberBranchSpace := by
  obtain ⟨e, k, h⟩ := exists_weberSquareBranch_smul g
  have hfun : (fun τ : UpperHalfPlane => weberSquareBranch i (g • τ)) =
      (weberBranchPhase ^ k i) • weberSquareBranch (e i) := by
    funext τ
    simpa only [Pi.smul_apply, Algebra.smul_def, IntermediateField.algebraMap_apply,
      coe_weberBranchPhase_zpow] using h i τ
  rw [hfun]
  exact weberBranchSpace.smul_mem _ (Submodule.subset_span (Set.mem_range_self _))

/-- An actual modularly transformed function, now regarded as an element of the span. -/
def weberBranchModularTransform (g : SL(2, ℤ)) (i : Fin 3) : weberBranchSpace :=
  ⟨fun τ => weberSquareBranch i (g • τ),
    weberSquareBranch_smul_mem_weberBranchSpace g i⟩

/-- The existing analytic modular law gives the monomial formula in the concrete span. -/
theorem exists_weberBranchModularTransform_monomial (g : SL(2, ℤ)) :
    ∃ (e : Equiv.Perm (Fin 3)) (k : Fin 3 → ℤ), ∀ i,
      weberBranchModularTransform g i = (weberBranchPhase ^ k i) • weberBranchBasis (e i) := by
  obtain ⟨e, k, h⟩ := exists_weberSquareBranch_smul g
  refine ⟨e, k, fun i => ?_⟩
  apply Subtype.ext
  funext τ
  simpa only [weberBranchModularTransform, Submodule.coe_smul, coe_weberBranchBasis,
    Pi.smul_apply, Algebra.smul_def, IntermediateField.algebraMap_apply,
    coe_weberBranchPhase_zpow] using h i τ

/-- Coefficient action on a modular transform acts on its actual monomial phase,
while leaving the actual basis branch fixed. -/
theorem exists_weberBranchModularTransform_coefficientAction (g : SL(2, ℤ)) :
    ∃ (e : Equiv.Perm (Fin 3)) (k : Fin 3 → ℤ),
      ∀ (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField) i,
        weberBranchCoefficientAction σ (weberBranchModularTransform g i) =
          ((σ weberBranchPhase) ^ k i) • weberBranchBasis (e i) := by
  obtain ⟨e, k, h⟩ := exists_weberBranchModularTransform_monomial g
  refine ⟨e, k, fun σ i => ?_⟩
  rw [h i, weberBranchCoefficientAction_smul, weberBranchCoefficientAction_basis, map_zpow₀]

end ModularForm
end
