/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.BranchSpace
import BakerHeegnerStark.ComplexMultiplication.Weber.Action
import BakerHeegnerStark.ComplexMultiplication.Residues

/-!
# Actual Weber branches indexed by modular residues

Scalar units modulo twenty-four fix the actual Weber square by the proved
normalized CM-unit transformation law. Translation and inversion then give the
same assertion for all three actual branches. Thus projectively equal reductions
have equal transforms as elements of the concrete Weber function space.

The residue index is only the subgroup range of integral modular reduction in
`GL₂(ℤ/24ℤ)`, not the whole general linear group. This is a finite subgroup of a
finite ambient group. Choosing an actual integral preimage defines its branch
transforms independently of the choice and gives the actual right-substitution
law. None of these statements asserts Galois compatibility of CM evaluation.
-/

open scoped MatrixGroups

namespace ModularForm
noncomputable section

private theorem weberF_sq_smul_of_scalar_reduction (g : SL(2, ℤ)) (u : (ZMod 24)ˣ)
    (hg : Matrix.SpecialLinearGroup.mapGL (ZMod 24) g =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u) (τ : UpperHalfPlane) :
    weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2 = weberF (τ : ℂ) ^ 2 := by
  have hn : ((u : ZMod 24) ^ 2 + 11 * 0 ^ 2) * 1 = 1 := by
    simpa using BakerHeegnerStark.zmod_twenty_four_unit_sq u
  apply weberF_sq_smul_of_cm_unit_reduction g 11 u 0 1 hn (Or.inl rfl) _ τ
  have hm := congrArg (fun A : GL (Fin 2) (ZMod 24) =>
    (A : Matrix (Fin 2) (Fin 2) (ZMod 24))) hg
  apply Subtype.ext
  ext i j
  have he := congrFun₂ hm i j
  fin_cases i <;> fin_cases j
  all_goals simpa [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.map,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar,
    weberCMUnitMatrixTwentyFour] using he

private theorem weberSquareBranch_zero_eq_of_projective_reduction
    (g h : SL(2, ℤ)) (u : (ZMod 24)ˣ)
    (hmod : Matrix.SpecialLinearGroup.mapGL (ZMod 24) h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u *
        Matrix.SpecialLinearGroup.mapGL (ZMod 24) g) (τ : UpperHalfPlane) :
    weberSquareBranch 0 (h • τ) = weberSquareBranch 0 (g • τ) := by
  have hk : Matrix.SpecialLinearGroup.mapGL (ZMod 24) (h * g⁻¹) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    rw [map_mul, map_inv, hmod, mul_assoc, mul_inv_cancel, mul_one]
  simpa [weberSquareBranch, mul_smul] using
    weberF_sq_smul_of_scalar_reduction (h * g⁻¹) u hk (g • τ)

/-- Projectively equal reductions give equal actual transforms of every branch.
The proof uses actual scalar invariance and the analytic `T` and `S` laws, not
merely finiteness of the possible phases. -/
theorem weberBranchModularTransform_eq_of_projective_reduction
    (g h : SL(2, ℤ)) (u : (ZMod 24)ˣ)
    (hmod : Matrix.SpecialLinearGroup.mapGL (ZMod 24) h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u *
        Matrix.SpecialLinearGroup.mapGL (ZMod 24) g) (i : Fin 3) :
    weberBranchModularTransform h i = weberBranchModularTransform g i := by
  apply Subtype.ext
  funext τ
  change weberSquareBranch i (h • τ) = weberSquareBranch i (g • τ)
  have hzero (a : SL(2, ℤ)) :
      weberSquareBranch 0 ((a * h) • τ) = weberSquareBranch 0 ((a * g) • τ) := by
    apply weberSquareBranch_zero_eq_of_projective_reduction (a * g) (a * h) u
    rw [map_mul, map_mul, hmod, ← mul_assoc,
      ← Matrix.GeneralLinearGroup.scalar_commute u
        (Matrix.SpecialLinearGroup.mapGL (ZMod 24) a), mul_assoc]
  have hphase : (zeta48 ^ 2 : ℂ) ^ (-1 : ℤ) ≠ 0 :=
    zpow_ne_zero _ (pow_ne_zero _ zeta48_ne_zero)
  fin_cases i
  · exact weberSquareBranch_zero_eq_of_projective_reduction g h u hmod τ
  · have he := hzero ModularGroup.T
    simp only [mul_smul, weberSquareBranch_T,
      show (0 : Fin 3) ≠ 2 by decide, ite_false, Equiv.swap_apply_left] at he
    exact mul_left_cancel₀ hphase he
  · have he := hzero (ModularGroup.T * ModularGroup.S)
    simp only [mul_smul, weberSquareBranch_T, weberSquareBranch_S,
      show (0 : Fin 3) ≠ 2 by decide, ite_false, Equiv.swap_apply_left] at he
    exact mul_left_cancel₀ hphase he

/-- Equal level-twenty-four reductions give equality in the actual function space. -/
theorem weberBranchModularTransform_eq_of_reduction
    (g h : SL(2, ℤ))
    (hmod : Matrix.SpecialLinearGroup.mapGL (ZMod 24) h =
      Matrix.SpecialLinearGroup.mapGL (ZMod 24) g) (i : Fin 3) :
    weberBranchModularTransform h i = weberBranchModularTransform g i := by
  apply weberBranchModularTransform_eq_of_projective_reduction g h 1
  simpa using hmod

/-- The finite subgroup of `GL₂(ℤ/24ℤ)` actually reached by integral modular
reduction. No surjectivity onto the ambient general linear group is assumed. -/
def weberModularResidueGroup : Subgroup (GL (Fin 2) (ZMod 24)) :=
  (Matrix.SpecialLinearGroup.mapGL (R := ℤ) (ZMod 24)).range

/-- Integral modular reduction with its honest subgroup-range codomain. -/
def weberModularResidueReduction : SL(2, ℤ) →* weberModularResidueGroup :=
  (Matrix.SpecialLinearGroup.mapGL (ZMod 24)).rangeRestrict

/-- A chosen actual integral lift of a residue in the subgroup range. -/
def weberModularResidueLift (r : weberModularResidueGroup) : SL(2, ℤ) :=
  Classical.choose r.property

@[simp]
theorem mapGL_weberModularResidueLift (r : weberModularResidueGroup) :
    Matrix.SpecialLinearGroup.mapGL (ZMod 24) (weberModularResidueLift r) = r :=
  Classical.choose_spec r.property

/-- The actual transformed branch indexed by an attained modular residue. -/
def weberBranchResidueTransform (r : weberModularResidueGroup) (i : Fin 3) :
    weberBranchSpace :=
  weberBranchModularTransform (weberModularResidueLift r) i

/-- Every actual integral preimage gives the same element of the concrete space. -/
theorem weberBranchResidueTransform_eq_of_lift (r : weberModularResidueGroup)
    (g : SL(2, ℤ))
    (hg : Matrix.SpecialLinearGroup.mapGL (ZMod 24) g = r) (i : Fin 3) :
    weberBranchResidueTransform r i = weberBranchModularTransform g i := by
  apply weberBranchModularTransform_eq_of_reduction
  exact (mapGL_weberModularResidueLift r).trans hg.symm

@[simp]
theorem weberBranchResidueTransform_reduction (g : SL(2, ℤ)) (i : Fin 3) :
    weberBranchResidueTransform (weberModularResidueReduction g) i =
      weberBranchModularTransform g i := by
  apply weberBranchResidueTransform_eq_of_lift
  rfl

/-- The residue transform evaluates to the actual branch at any integral lift. -/
theorem weberBranchResidueTransform_eval_of_lift (r : weberModularResidueGroup)
    (g : SL(2, ℤ))
    (hg : Matrix.SpecialLinearGroup.mapGL (ZMod 24) g = r)
    (i : Fin 3) (τ : UpperHalfPlane) :
    (weberBranchResidueTransform r i : UpperHalfPlane → ℂ) τ =
      weberSquareBranch i (g • τ) := by
  rw [weberBranchResidueTransform_eq_of_lift r g hg i]
  rfl

/-- Scalar-related attained residues give equal actual branch functions. -/
theorem weberBranchResidueTransform_eq_of_projective
    (r s : weberModularResidueGroup) (u : (ZMod 24)ˣ)
    (hrs : (s : GL (Fin 2) (ZMod 24)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u * (r : GL (Fin 2) (ZMod 24)))
    (i : Fin 3) :
    weberBranchResidueTransform s i = weberBranchResidueTransform r i := by
  apply weberBranchModularTransform_eq_of_projective_reduction
      (weberModularResidueLift r) (weberModularResidueLift s) u
  simpa only [mapGL_weberModularResidueLift] using hrs

/-- Substituting an actual integral modular transformation on the right multiplies
the attained residue on the right, for each of the three actual functions. -/
theorem weberBranchResidueTransform_smul (r : weberModularResidueGroup)
    (h : SL(2, ℤ)) (i : Fin 3) (τ : UpperHalfPlane) :
    (weberBranchResidueTransform r i : UpperHalfPlane → ℂ) (h • τ) =
      (weberBranchResidueTransform (r * weberModularResidueReduction h) i :
        UpperHalfPlane → ℂ) τ := by
  rw [weberBranchResidueTransform_eval_of_lift
    (r * weberModularResidueReduction h) (weberModularResidueLift r * h)]
  · change weberSquareBranch i (weberModularResidueLift r • (h • τ)) =
      weberSquareBranch i ((weberModularResidueLift r * h) • τ)
    rw [mul_smul]
  · rw [map_mul, mapGL_weberModularResidueLift]
    rfl

end
end ModularForm
