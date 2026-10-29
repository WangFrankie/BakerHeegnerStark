/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.PhaseField
import BakerHeegnerStark.ModularForms.Weber.ResidueBranches
import BakerHeegnerStark.ComplexMultiplication.CyclicNeighbors.Data

/-!
# The actual finite coupled Weber orbit

The index pairs an automorphism of the actual phase field with an attained
integral modular residue. A single permutation under integral modular
substitution reindexes both the actual Weber function and the full tuple of
neighboring values. The attached matrix uses the right-normalized convention
`r * diag(1, χ(σ))`. Its transformation law retains the actual central-unit
ambiguity. No compatibility of Galois action with CM evaluation is asserted.
-/

open BakerHeegnerStark
open scoped MatrixGroups

noncomputable section
namespace ModularForm

/-- An honest finite index: phase-field automorphisms and attained modular residues. -/
abbrev weberJointIndex :=
  (weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField) ×
    weberModularResidueGroup

instance instFintypeWeberJointIndex : Fintype weberJointIndex := Fintype.ofFinite _

/-- The actual coefficient-conjugated Weber-square branch in its function space. -/
def weberJointBranch (p : weberJointIndex) : weberBranchSpace :=
  weberBranchCoefficientAction p.1 (weberBranchResidueTransform p.2 0)

/-- The right-normalized matrix attached to the same branch index. -/
def weberJointMatrix (p : weberJointIndex) : GL (Fin 2) (ZMod 24) :=
  (p.2 : GL (Fin 2) (ZMod 24)) *
    weberCoefficientDiagonal (weberBranchCyclotomicCharacter p.1)

private theorem unit_twentyFour_inv (u : (ZMod 24)ˣ) : u⁻¹ = u := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  simpa only [Units.val_mul, Units.val_one, pow_two] using zmod_twenty_four_unit_sq u

/-- Every actual character diagonal squares to the identity. -/
theorem weberCoefficientDiagonal_sq (u : (ZMod 24)ˣ) :
    weberCoefficientDiagonal u ^ 2 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two,
      show (u : ZMod 24) * (u : ZMod 24) = 1 by
        simpa only [pow_two] using zmod_twenty_four_unit_sq u]

/-- Inversion does not change a level-twenty-four character diagonal. -/
@[simp]
theorem weberCoefficientDiagonal_inv (u : (ZMod 24)ˣ) :
    (weberCoefficientDiagonal u)⁻¹ = weberCoefficientDiagonal u :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using weberCoefficientDiagonal_sq u)

private theorem coefficientAction_inv_cancel
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (f : weberBranchSpace) :
    weberBranchCoefficientAction σ⁻¹ (weberBranchCoefficientAction σ f) = f := by
  rw [← weberBranchCoefficientAction_mul, inv_mul_cancel, weberBranchCoefficientAction_one]

/-- The inverse-character conjugate supplies the correct right-substitution
transformation, on every function in the actual Weber span. -/
private theorem exists_weberJointConjugate
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (g : SL(2, ℤ)) :
    ∃ (k : SL(2, ℤ)) (u : (ZMod 24)ˣ),
      Matrix.SpecialLinearGroup.mapGL (ZMod 24) k =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          weberCoefficientDiagonal (weberBranchCyclotomicCharacter σ) *
          Matrix.SpecialLinearGroup.mapGL (ZMod 24) g *
          weberCoefficientDiagonal (weberBranchCyclotomicCharacter σ) ∧
      ∀ f : weberBranchSpace,
        weberSubstitution g (weberBranchCoefficientAction σ f) =
          weberBranchCoefficientAction σ (weberSubstitution k f) := by
  obtain ⟨k, u, hk, hbase⟩ := exists_weberBranchCoefficientConjugation σ⁻¹ g
  refine ⟨k, u, ?_, ?_⟩
  · simpa only [map_inv, unit_twentyFour_inv, weberCoefficientDiagonal_inv] using hk
  · intro f
    have h := coefficientAction_substitution_of_basis σ⁻¹ g k hbase
      (weberBranchCoefficientAction σ f)
    rw [coefficientAction_inv_cancel] at h
    apply (weberBranchCoefficientAction σ⁻¹).injective
    rw [h, coefficientAction_inv_cancel]

private theorem weberSubstitution_residue (r : weberModularResidueGroup)
    (g : SL(2, ℤ)) (i : Fin 3) :
    weberSubstitution g (weberBranchResidueTransform r i) =
      weberBranchResidueTransform (r * weberModularResidueReduction g) i := by
  apply Subtype.ext
  funext τ
  rw [weberSubstitution_eval, weberBranchResidueTransform_smul]

/-- A single finite-index permutation simultaneously reindexes the actual Weber
functions and all the actual neighboring data. The same permutation also has
the displayed projective matrix witness; no full-`GL₂` lift is assumed. -/
theorem exists_weberJoint_modular_reindex (g : SL(2, ℤ)) :
    ∃ e : Equiv.Perm weberJointIndex, ∀ p : weberJointIndex,
      (∀ τ : UpperHalfPlane,
        (weberJointBranch p : UpperHalfPlane → ℂ) (g • τ) =
          (weberJointBranch (e p) : UpperHalfPlane → ℂ) τ) ∧
      (∀ τ : UpperHalfPlane,
        cyclicNeighborData (weberJointMatrix p) (g • τ) =
          cyclicNeighborData (weberJointMatrix (e p)) τ) ∧
      ∃ u : (ZMod 24)ˣ,
        weberJointMatrix (e p) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) u * weberJointMatrix p *
            Matrix.SpecialLinearGroup.mapGL (ZMod 24) g := by
  classical
  choose k u hk hf using fun σ => exists_weberJointConjugate σ g
  let e : Equiv.Perm weberJointIndex :=
    { toFun := fun p => (p.1, p.2 * weberModularResidueReduction (k p.1))
      invFun := fun p => (p.1, p.2 * (weberModularResidueReduction (k p.1))⁻¹)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  have hmatrix (p : weberJointIndex) :
      weberJointMatrix (e p) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (u p.1) * weberJointMatrix p *
          Matrix.SpecialLinearGroup.mapGL (ZMod 24) g := by
    change ((p.2 : GL (Fin 2) (ZMod 24)) *
      Matrix.SpecialLinearGroup.mapGL (ZMod 24) (k p.1)) *
        weberCoefficientDiagonal (weberBranchCyclotomicCharacter p.1) = _
    rw [hk]
    let D := weberCoefficientDiagonal (weberBranchCyclotomicCharacter p.1)
    let A := Matrix.SpecialLinearGroup.mapGL (ZMod 24) g
    let r := (p.2 : GL (Fin 2) (ZMod 24))
    let U := Matrix.GeneralLinearGroup.scalar (Fin 2) (u p.1)
    change (r * (U * D * A * D)) * D = U * (r * D) * A
    calc
      (r * (U * D * A * D)) * D = (r * U) * D * A * (D * D) := by
        simp only [mul_assoc]
      _ = (U * r) * D * A := by
        rw [← Matrix.GeneralLinearGroup.scalar_commute (u p.1) r,
          ← pow_two, weberCoefficientDiagonal_sq, mul_one]
      _ = U * (r * D) * A := by simp only [mul_assoc]
  refine ⟨e, fun p => ⟨?_, ?_, u p.1, hmatrix p⟩⟩
  · intro τ
    change (weberBranchCoefficientAction p.1 (weberBranchResidueTransform p.2 0) :
      UpperHalfPlane → ℂ) (g • τ) = _
    rw [← weberSubstitution_eval, hf, weberSubstitution_residue]
    rfl
  · intro τ
    rw [cyclicNeighborData_smul, hmatrix, mul_assoc,
      Matrix.GeneralLinearGroup.scalar_commute,
      cyclicNeighborData_mul_scalar]

end ModularForm
