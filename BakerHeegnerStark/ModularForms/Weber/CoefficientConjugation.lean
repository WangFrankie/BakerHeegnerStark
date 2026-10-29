/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.BranchSpace
import BakerHeegnerStark.ComplexMultiplication.Residues
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Actual coefficient conjugation of Weber modular transforms

The actual primitive phase defines the cyclotomic character of the actual
coefficient field. Conjugating an integral modular transformation by its
character diagonal is realized, up to a central unit modulo twenty-four, by
an integral modular transformation whose action on the three actual functions
is precisely coefficient conjugation. This concerns the canonical coefficients
of functions, not Galois action on values at CM points.
-/

open BakerHeegnerStark UpperHalfPlane Complex Module
open scoped MatrixGroups

noncomputable section
namespace ModularForm

/-- The actual modular phase is a primitive twenty-fourth root in its actual field. -/
theorem isPrimitiveRoot_weberBranchPhase : IsPrimitiveRoot weberBranchPhase 24 := by
  apply (IsPrimitiveRoot.map_iff_of_injective
    (FaithfulSMul.algebraMap_injective weberBranchCoefficientField ℂ)).mp
  change IsPrimitiveRoot (zeta48 ^ 2) 24
  rw [zeta48_sq]
  exact Complex.isPrimitiveRoot_exp 24 (by norm_num)

/-- The cyclotomic character of the actual Weber coefficient field. -/
def weberBranchCyclotomicCharacter :
    (weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField) →* (ZMod 24)ˣ :=
  isPrimitiveRoot_weberBranchPhase.autToPow ℚ

/-- The character records the image of the actual primitive phase. -/
theorem weberBranchCyclotomicCharacter_spec
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField) :
    weberBranchPhase ^ (weberBranchCyclotomicCharacter σ : ZMod 24).val =
      σ weberBranchPhase :=
  isPrimitiveRoot_weberBranchPhase.autToPow_spec ℚ σ

/-- The actual diagonal `diag(1, δ)` over the composite residue ring. -/
def weberCoefficientDiagonal (δ : (ZMod 24)ˣ) : GL (Fin 2) (ZMod 24) where
  val := !![1, 0; 0, (δ : ZMod 24)]
  inv := !![1, 0; 0, (↑(δ⁻¹) : ZMod 24)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem coe_weberCoefficientDiagonal (δ : (ZMod 24)ˣ) :
    (weberCoefficientDiagonal δ : Matrix (Fin 2) (Fin 2) (ZMod 24)) =
      !![1, 0; 0, (δ : ZMod 24)] := rfl

/-- Actual modular substitution on the concrete Weber function span. -/
def weberSubstitution (g : SL(2, ℤ)) :
    weberBranchSpace →ₗ[weberBranchCoefficientField] weberBranchSpace :=
  weberBranchBasis.constr weberBranchCoefficientField (weberBranchModularTransform g)

@[simp] private theorem weberSubstitution_basis (g : SL(2, ℤ)) (i : Fin 3) :
    weberSubstitution g (weberBranchBasis i) = weberBranchModularTransform g i :=
  weberBranchBasis.constr_basis _ _ _

/-- Substitution evaluates at the actual modularly transformed point. -/
theorem weberSubstitution_eval (g : SL(2, ℤ)) (f : weberBranchSpace)
    (τ : UpperHalfPlane) :
    (weberSubstitution g f : UpperHalfPlane → ℂ) τ = (f : UpperHalfPlane → ℂ) (g • τ) := by
  rw [weberSubstitution, Basis.constr_apply_fintype]
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, IntermediateField.smul_def, smul_eq_mul,
    weberBranchModularTransform, weberBranchCoefficientEquiv, LinearEquiv.symm_symm,
    Basis.equivFun_apply] using (weberBranchSpace_eval f (g • τ)).symm

@[simp] private theorem weberSubstitution_one (f : weberBranchSpace) :
    weberSubstitution 1 f = f := by
  apply Subtype.ext
  funext τ
  simp only [weberSubstitution_eval, one_smul]

private theorem weberSubstitution_mul (g h : SL(2, ℤ)) (f : weberBranchSpace) :
    weberSubstitution (g * h) f = weberSubstitution h (weberSubstitution g f) := by
  apply Subtype.ext
  funext τ
  simp only [weberSubstitution_eval, mul_smul]

@[simp] private theorem weberSubstitution_inv_cancel (g : SL(2, ℤ))
    (f : weberBranchSpace) : weberSubstitution g⁻¹ (weberSubstitution g f) = f := by
  rw [← weberSubstitution_mul, mul_inv_cancel, weberSubstitution_one]

@[simp] private theorem weberSubstitution_cancel_inv (g : SL(2, ℤ))
    (f : weberBranchSpace) : weberSubstitution g (weberSubstitution g⁻¹ f) = f := by
  rw [← weberSubstitution_mul, inv_mul_cancel, weberSubstitution_one]

/-- Equality on the canonical branches gives the full semilinear substitution law. -/
theorem coefficientAction_substitution_of_basis
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (g h : SL(2, ℤ))
    (hbase : ∀ i, weberBranchCoefficientAction σ (weberBranchModularTransform g i) =
      weberBranchModularTransform h i) (f : weberBranchSpace) :
    weberBranchCoefficientAction σ (weberSubstitution g f) =
      weberSubstitution h (weberBranchCoefficientAction σ f) := by
  rw [← weberBranchBasis.sum_repr f]
  simp only [map_sum, map_smul, weberSubstitution_basis,
    weberBranchCoefficientAction_smul, weberBranchCoefficientAction_basis, hbase]

private def weberTranslationExponent (i : Fin 3) : ℤ := if i = 2 then 2 else -1

private theorem weberTranslationExponent_swap (i : Fin 3) :
    weberTranslationExponent (Equiv.swap 0 1 i) = weberTranslationExponent i := by
  fin_cases i <;> decide

private theorem weberBranchModularTransform_S (i : Fin 3) :
    weberBranchModularTransform ModularGroup.S i =
      weberBranchBasis (Equiv.swap 1 2 i) := by
  apply Subtype.ext
  funext τ
  simpa only [weberBranchModularTransform, coe_weberBranchBasis] using
    weberSquareBranch_S i τ

private theorem weberBranchModularTransform_T (i : Fin 3) :
    weberBranchModularTransform ModularGroup.T i =
      (weberBranchPhase ^ weberTranslationExponent i) •
        weberBranchBasis (Equiv.swap 0 1 i) := by
  apply Subtype.ext
  funext τ
  simpa only [weberBranchModularTransform, Submodule.coe_smul, coe_weberBranchBasis,
    Pi.smul_apply, IntermediateField.smul_def, smul_eq_mul,
    coe_weberBranchPhase_zpow, weberTranslationExponent] using weberSquareBranch_T i τ

private theorem weberSubstitution_T_sq (i : Fin 3) :
    weberSubstitution (ModularGroup.T ^ 2) (weberBranchBasis i) =
      (weberBranchPhase ^ (2 * weberTranslationExponent i)) • weberBranchBasis i := by
  rw [pow_two, weberSubstitution_mul, weberSubstitution_basis,
    weberBranchModularTransform_T, map_smul, weberSubstitution_basis,
    weberBranchModularTransform_T, weberTranslationExponent_swap, smul_smul,
    ← zpow_add₀ (isPrimitiveRoot_weberBranchPhase.ne_zero (by norm_num))]
  simp only [Equiv.swap_apply_self]
  congr 2
  ring

private theorem weberSubstitution_T_sq_pow (k : ℕ) (i : Fin 3) :
    weberSubstitution ((ModularGroup.T ^ 2) ^ k) (weberBranchBasis i) =
      (weberBranchPhase ^ ((2 * (k : ℤ)) * weberTranslationExponent i)) •
        weberBranchBasis i := by
  induction k with
  | zero =>
      simp only [pow_zero, weberSubstitution_one, Nat.cast_zero, mul_zero, zero_mul,
        zpow_zero, one_smul]
  | succ k hk =>
      rw [pow_succ, weberSubstitution_mul, hk, map_smul,
        weberSubstitution_T_sq, smul_smul,
        ← zpow_add₀ (isPrimitiveRoot_weberBranchPhase.ne_zero (by norm_num))]
      congr 2
      push_cast
      ring

private theorem weberBranchModularTransform_T_odd (n : ℕ) (hn : Odd n) (i : Fin 3) :
    weberBranchModularTransform (ModularGroup.T ^ n) i =
      (weberBranchPhase ^ ((n : ℤ) * weberTranslationExponent i)) •
        weberBranchBasis (Equiv.swap 0 1 i) := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add, pow_mul, pow_one,
    ← weberSubstitution_basis, weberSubstitution_mul, weberSubstitution_T_sq_pow,
    map_smul, weberSubstitution_basis, weberBranchModularTransform_T, smul_smul,
    ← zpow_add₀ (isPrimitiveRoot_weberBranchPhase.ne_zero (by norm_num))]
  congr 2
  push_cast
  ring

private theorem zmod_twenty_four_unit_val_odd (δ : (ZMod 24)ˣ) :
    Odd (δ : ZMod 24).val :=
  ((ZMod.val_coe_unit_coprime δ).of_dvd_right (by decide : 2 ∣ 24)).odd_of_right

private theorem coefficientAction_S
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField) (i : Fin 3) :
    weberBranchCoefficientAction σ (weberBranchModularTransform ModularGroup.S i) =
      weberBranchModularTransform ModularGroup.S i := by
  simp only [weberBranchModularTransform_S, weberBranchCoefficientAction_basis]

private theorem coefficientAction_T
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField) (i : Fin 3) :
    weberBranchCoefficientAction σ (weberBranchModularTransform ModularGroup.T i) =
      weberBranchModularTransform
        (ModularGroup.T ^ (weberBranchCyclotomicCharacter σ : ZMod 24).val) i := by
  rw [weberBranchModularTransform_T, weberBranchCoefficientAction_smul,
    weberBranchCoefficientAction_basis, map_zpow₀,
    ← weberBranchCyclotomicCharacter_spec,
    weberBranchModularTransform_T_odd _
      (zmod_twenty_four_unit_val_odd (weberBranchCyclotomicCharacter σ))]
  rw [← zpow_natCast, ← zpow_mul]

private def weberConjugatedReduction (δ : (ZMod 24)ˣ) :
    SL(2, ℤ) →* GL (Fin 2) (ZMod 24) :=
  (MulAut.conj (weberCoefficientDiagonal δ)).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.mapGL (ZMod 24))

private theorem weberConjugatedReduction_S (δ : (ZMod 24)ˣ) :
    Matrix.SpecialLinearGroup.mapGL (ZMod 24) ModularGroup.S =
      Matrix.GeneralLinearGroup.scalar (Fin 2) δ *
        weberConjugatedReduction δ ModularGroup.S := by
  have hδ : (δ : ZMod 24) * (δ : ZMod 24) = 1 := by
    simpa only [pow_two] using zmod_twenty_four_unit_sq δ
  apply Units.ext
  change (ModularGroup.S.1.map (Int.castRingHom (ZMod 24))) =
    Matrix.scalar (Fin 2) (δ : ZMod 24) *
      (!![1, 0; 0, (δ : ZMod 24)] *
        (ModularGroup.S.1.map (Int.castRingHom (ZMod 24))) *
        !![1, 0; 0, (↑(δ⁻¹) : ZMod 24)])
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.scalar, hδ]

private theorem weberConjugatedReduction_T (δ : (ZMod 24)ˣ) :
    Matrix.SpecialLinearGroup.mapGL (ZMod 24)
        (ModularGroup.T ^ (δ : ZMod 24).val) =
      weberConjugatedReduction δ ModularGroup.T := by
  have hδ : (δ : ZMod 24) * (δ : ZMod 24) = 1 := by
    simpa only [pow_two] using zmod_twenty_four_unit_sq δ
  have hi : (↑(δ⁻¹) : ZMod 24) = (δ : ZMod 24) :=
    Units.inv_eq_of_mul_eq_one_left hδ
  apply Units.ext
  change ((ModularGroup.T ^ (δ : ZMod 24).val).1.map (Int.castRingHom (ZMod 24))) =
    !![1, 0; 0, (δ : ZMod 24)] *
      (ModularGroup.T.1.map (Int.castRingHom (ZMod 24))) *
      !![1, 0; 0, (↑(δ⁻¹) : ZMod 24)]
  rw [← zpow_natCast, ModularGroup.coe_T_zpow, ModularGroup.coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hi, hδ]

private theorem exists_weberCoefficientConjugation_all
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (g : SL(2, ℤ)) :
    ∃ (h : SL(2, ℤ)) (u : (ZMod 24)ˣ),
      Matrix.SpecialLinearGroup.mapGL (ZMod 24) h =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          weberConjugatedReduction (weberBranchCyclotomicCharacter σ) g ∧
      ∀ f : weberBranchSpace,
        weberBranchCoefficientAction σ (weberSubstitution g f) =
          weberSubstitution h (weberBranchCoefficientAction σ f) := by
  have hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ⟨ModularGroup.S, weberBranchCyclotomicCharacter σ,
          weberConjugatedReduction_S _, coefficientAction_substitution_of_basis
            σ _ _ (coefficientAction_S σ)⟩
      · refine ⟨ModularGroup.T ^ (weberBranchCyclotomicCharacter σ : ZMod 24).val,
          1, ?_, coefficientAction_substitution_of_basis σ _ _ (coefficientAction_T σ)⟩
        simpa only [map_one, one_mul] using
          weberConjugatedReduction_T (weberBranchCyclotomicCharacter σ)
  | one =>
      refine ⟨1, 1, ?_, ?_⟩
      · simp only [map_one, mul_one]
      · intro f
        simp only [weberSubstitution_one]
  | mul a b _ _ ha hb =>
      obtain ⟨a', u, hu, hfa⟩ := ha
      obtain ⟨b', v, hv, hfb⟩ := hb
      refine ⟨a' * b', u * v, ?_, ?_⟩
      · rw [map_mul, hu, hv, map_mul, map_mul]
        rw [mul_assoc, ← mul_assoc
          (weberConjugatedReduction (weberBranchCyclotomicCharacter σ) a),
          ← Matrix.GeneralLinearGroup.scalar_commute]
        simp only [mul_assoc]
      · intro f
        rw [weberSubstitution_mul, hfb, hfa, weberSubstitution_mul]
  | inv a _ ha =>
      obtain ⟨a', u, hu, hfa⟩ := ha
      refine ⟨a'⁻¹, u⁻¹, ?_, ?_⟩
      · rw [map_inv, hu, mul_inv_rev, ← map_inv, ← map_inv]
        exact (Matrix.GeneralLinearGroup.scalar_commute _ _).symm
      · intro f
        have hf := congrArg (weberSubstitution a'⁻¹) (hfa (weberSubstitution a⁻¹ f))
        simpa only [weberSubstitution_cancel_inv, weberSubstitution_inv_cancel] using hf.symm

/-- Actual coefficient conjugation of every integral modular transform is realized
by an integral transformation with the character-diagonal conjugate reduction,
up to a central unit. The equality is in the actual function span. -/
theorem exists_weberBranchCoefficientConjugation
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (g : SL(2, ℤ)) :
    ∃ (h : SL(2, ℤ)) (u : (ZMod 24)ˣ),
      Matrix.SpecialLinearGroup.mapGL (ZMod 24) h =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          weberCoefficientDiagonal (weberBranchCyclotomicCharacter σ) *
          Matrix.SpecialLinearGroup.mapGL (ZMod 24) g *
          (weberCoefficientDiagonal (weberBranchCyclotomicCharacter σ))⁻¹ ∧
      ∀ i : Fin 3,
        weberBranchCoefficientAction σ (weberBranchModularTransform g i) =
          weberBranchModularTransform h i := by
  obtain ⟨h, u, hu, hf⟩ := exists_weberCoefficientConjugation_all σ g
  refine ⟨h, u, ?_, ?_⟩
  · simpa only [weberConjugatedReduction, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc] using hu
  · intro i
    simpa only [weberSubstitution_basis, weberBranchCoefficientAction_basis] using
      hf (weberBranchBasis i)

end ModularForm
end
