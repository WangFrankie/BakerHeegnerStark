/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Weber.JointPolynomial
import BakerHeegnerStark.ComplexMultiplication.Gamma.Values
import BakerHeegnerStark.FieldTheory.AlgebraicOrbit
import QNFMathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# CM specialization of the actual Weber joint polynomial

Genuine CRT lifting realizes every conjugate of the full neighboring tuple by
an invertible level-twenty-four matrix. Separating the complete tuples in the
joint product then detects the CM centralizer. Its right-normalized integral
lift fixes the actual Weber branch. Consequently explicit fixedness of the
joint polynomial implies actual Weber-square field membership; no reciprocity
placeholder, algebraicity of the ambient complex extension, or continuity of
an arbitrary field automorphism is used.
-/

open scoped MatrixGroups BigOperators IntermediateField
open ModularForm

noncomputable section
namespace BakerHeegnerStark

private def crtMatrix (A₃ : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (A₈ : Matrix (Fin 2) (Fin 2) (ZMod 8)) : Matrix (Fin 2) (Fin 2) (ZMod 24) :=
  fun i j => (ZMod.chineseRemainder (by decide : Nat.Coprime 3 8)).symm (A₃ i j, A₈ i j)

private theorem crtMatrix_mod_three (A₃ : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (A₈ : Matrix (Fin 2) (Fin 2) (ZMod 8)) :
    (crtMatrix A₃ A₈).map (ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3)) = A₃ := by
  ext i j
  exact congrArg Prod.fst
    ((ZMod.chineseRemainder (by decide : Nat.Coprime 3 8)).apply_symm_apply (A₃ i j, A₈ i j))

private theorem crtMatrix_mod_eight (A₃ : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (A₈ : Matrix (Fin 2) (Fin 2) (ZMod 8)) :
    (crtMatrix A₃ A₈).map (ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)) = A₈ := by
  ext i j
  exact congrArg Prod.snd
    ((ZMod.chineseRemainder (by decide : Nat.Coprime 3 8)).apply_symm_apply (A₃ i j, A₈ i j))

private theorem matrix_eq_of_mod_three_eight
    (A B : Matrix (Fin 2) (Fin 2) (ZMod 24))
    (h₃ : A.map (ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3)) =
      B.map (ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3)))
    (h₈ : A.map (ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)) =
      B.map (ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8))) : A = B := by
  ext i j
  exact (zmod_twenty_four_eq_iff_reductions _ _).mpr
    ⟨congrFun₂ h₃ i j, congrFun₂ h₈ i j⟩

/-- Arbitrary invertible matrices at levels three and eight lift simultaneously
through the genuine reduction maps, with an entrywise CRT-lifted inverse. -/
theorem exists_GL_twenty_four_of_mod_three_eight
    (G₃ : GL (Fin 2) (ZMod 3)) (G₈ : GL (Fin 2) (ZMod 8)) :
    ∃ B : GL (Fin 2) (ZMod 24),
      Matrix.GeneralLinearGroup.map (ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3)) B = G₃ ∧
      Matrix.GeneralLinearGroup.map (ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)) B = G₈ := by
  let A := crtMatrix (G₃ : Matrix (Fin 2) (Fin 2) (ZMod 3)) G₈
  let I := crtMatrix G₃.inv G₈.inv
  have hAI : A * I = 1 := by
    apply matrix_eq_of_mod_three_eight
    · simpa only [Matrix.map_mul, A, I, crtMatrix_mod_three, map_zero, map_one,
        Matrix.map_one] using G₃.val_inv
    · simpa only [Matrix.map_mul, A, I, crtMatrix_mod_eight, map_zero, map_one,
        Matrix.map_one] using G₈.val_inv
  have hIA : I * A = 1 := by
    apply matrix_eq_of_mod_three_eight
    · simpa only [Matrix.map_mul, A, I, crtMatrix_mod_three, map_zero, map_one,
        Matrix.map_one] using G₃.inv_val
    · simpa only [Matrix.map_mul, A, I, crtMatrix_mod_eight, map_zero, map_one,
        Matrix.map_one] using G₈.inv_val
  refine ⟨⟨A, I, hAI, hIA⟩, ?_, ?_⟩
  · apply Units.ext
    exact crtMatrix_mod_three _ _
  · apply Units.ext
    exact crtMatrix_mod_eight _ _

/-- Every actual conjugate of the complete neighboring tuple is represented by
a genuine `GL₂(ℤ/24ℤ)` matrix. The local torsion matrices are lifted after the
ordered-period anti-involution; no global torsion-surjectivity claim is needed. -/
theorem exists_cyclicNeighborData_eq_galois (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮jInvariant τ⟯] ℂ) :
    ∃ B : GL (Fin 2) (ZMod 24),
      cyclicNeighborData B τ = fun i => σ (cyclicNeighborData 1 τ i) := by
  classical
  obtain ⟨B, h₃, h₈⟩ := exists_GL_twenty_four_of_mod_three_eight
    (periodCoordinateGL (jInvariantCurveTorsionGaloisMatrix τ 3 (by decide) σ))
    (periodCoordinateGL (jInvariantCurveTorsionGaloisMatrix τ 8 (by decide) σ))
  refine ⟨B, ?_⟩
  funext i
  rcases i with t | t
  · change jInvariant (cyclicSublatticePoint (cyclicNeighborPerm (Or.inl rfl) B t).val τ) =
      σ (jInvariant (cyclicSublatticePoint (cyclicNeighborPerm (Or.inl rfl) 1 t).val τ))
    rw [cyclicNeighborPerm_one]
    rw [cyclicNeighborPerm, h₃, periodCoordinateGL_involutive]
    exact (jInvariant_cyclicSublatticePoint_galois (Or.inl rfl) τ σ t).symm
  · change jInvariant (cyclicSublatticePoint (cyclicNeighborPerm (Or.inr rfl) B t).val τ) =
      σ (jInvariant (cyclicSublatticePoint (cyclicNeighborPerm (Or.inr rfl) 1 t).val τ))
    rw [cyclicNeighborPerm_one]
    rw [cyclicNeighborPerm, h₈, periodCoordinateGL_involutive]
    exact (jInvariant_cyclicSublatticePoint_galois (Or.inr rfl) τ σ t).symm

/-- The finite rational-power weighting commutes with actual field automorphisms
whenever the whole neighboring tuple has the displayed conjugate values. -/
theorem cyclicNeighborWeighted_eq_galois_of_data (a : ℕ) (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮jInvariant τ⟯] ℂ) (B : GL (Fin 2) (ZMod 24))
    (hB : cyclicNeighborData B τ = fun i => σ (cyclicNeighborData 1 τ i)) :
    cyclicNeighborWeighted a B τ = σ (cyclicNeighborWeighted a 1 τ) := by
  simp only [cyclicNeighborWeighted, hB, map_sum, map_mul, map_pow, map_natCast]

end BakerHeegnerStark

namespace ModularForm

/-- The base paired index is the actual Weber-square branch. -/
theorem weberJointBranch_one : weberJointBranch (1, 1) = weberBranchBasis 0 := by
  rw [weberJointBranch, weberBranchCoefficientAction_one]
  rw [weberBranchResidueTransform_eq_of_lift 1 1 (by simp) 0]
  apply Subtype.ext
  funext τ
  simp [weberBranchModularTransform, coe_weberBranchBasis]

/-- The base paired index has the identity neighboring-data matrix. -/
@[simp] theorem weberJointMatrix_one : weberJointMatrix (1, 1) = 1 := by
  simp only [weberJointMatrix, map_one, OneMemClass.coe_one, one_mul]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weberCoefficientDiagonal]

/-- The determinant of the actual right-normalized joint matrix is its
coefficient character, not a scalar chosen from an unrelated lift. -/
theorem det_weberJointMatrix (p : weberJointIndex) :
    (weberJointMatrix p).det = weberBranchCyclotomicCharacter p.1 := by
  rw [weberJointMatrix, map_mul, ← mapGL_weberModularResidueLift p.2,
    Matrix.SpecialLinearGroup.det_mapGL, one_mul]
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

/-- Right normalization removes precisely the coefficient diagonal and recovers
the actual attained integral residue. -/
theorem specialLinearPart_weberJointMatrix (p : weberJointIndex) :
    (weberJointMatrix p).specialLinearPart =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) (weberModularResidueLift p.2) := by
  have hfactor := Matrix.GeneralLinearGroup.specialLinearPart_mul_diagonal_det
    (weberJointMatrix p)
  rw [det_weberJointMatrix] at hfactor
  have hunits :
      ((weberJointMatrix p).specialLinearPart : GL (Fin 2) (ZMod 24)) *
          weberCoefficientDiagonal (weberBranchCyclotomicCharacter p.1) =
        (p.2 : GL (Fin 2) (ZMod 24)) *
          weberCoefficientDiagonal (weberBranchCyclotomicCharacter p.1) := by
    apply Units.ext
    exact hfactor
  apply Matrix.SpecialLinearGroup.toGL_injective
  change ((weberJointMatrix p).specialLinearPart : GL (Fin 2) (ZMod 24)) =
    Matrix.SpecialLinearGroup.mapGL (ZMod 24) (weberModularResidueLift p.2)
  exact (mul_right_cancel hunits).trans (mapGL_weberModularResidueLift p.2).symm

/-- An actual joint matrix in the eligible CM commutant has the base Weber
branch as an entire analytic function. Its integral residue is normalized on
the right, using the supplied unit inverse determinant. -/
theorem weberJointBranch_eq_base_of_commute_CM (p : weberJointIndex) (m : ZMod 24)
    (hm : m = 11 ∨ m = 19)
    (hcomm : Commute (weberJointMatrix p : Matrix (Fin 2) (Fin 2) (ZMod 24))
      !![0, -m; 1, 0]) :
    weberJointBranch p = weberBranchBasis 0 := by
  have hr : weberBranchResidueTransform p.2 0 = weberBranchBasis 0 := by
    apply Subtype.ext
    funext τ
    rw [weberBranchResidueTransform_eval_of_lift p.2 (weberModularResidueLift p.2)
      (mapGL_weberModularResidueLift p.2) 0 τ, coe_weberBranchBasis]
    exact weberF_sq_smul_of_cm_centralizer_reduction (weberModularResidueLift p.2) m
      (weberJointMatrix p) hcomm hm (specialLinearPart_weberJointMatrix p).symm τ
  simp only [weberJointBranch, hr, weberBranchCoefficientAction_basis]

end ModularForm

namespace BakerHeegnerStark

/-- Explicit fixedness of the genuine formal joint product forces the actual
Weber square into the singular-modulus field. The fixed-field argument is over
the CM compositum inside `ℂ`; reality descent then removes the period. -/
theorem weberF_sq_sqrtPoint_mem_adjoin_of_jointPolynomial_fixed
    {m : ℕ} (hm : 0 < m) (hm8 : m % 8 = 3) (hm3 : ¬ 3 ∣ m)
    (hfixed : ∀ (a : ℕ) (σ : ℂ ≃ₐ[ℚ⟮jInvariant (sqrtPoint m)⟯] ℂ),
      σ (sqrtPoint m : ℂ) = (sqrtPoint m : ℂ) →
      (weberJointPolynomial a (sqrtPoint m)).map (Polynomial.mapRingHom σ.toRingHom) =
        weberJointPolynomial a (sqrtPoint m)) :
    weberF ((Real.sqrt m : ℂ) * Complex.I) ^ 2 ∈ ℚ⟮jInvariant (sqrtPoint m)⟯ := by
  classical
  let τ := sqrtPoint m
  let K := ℚ⟮jInvariant τ⟯
  let M := K⟮(τ : ℂ)⟯
  have hquad : (τ : ℂ) ^ 2 = -(m : ℂ) := by
    linear_combination sqrtPoint_quadratic hm
  have hm9 : 9 < m := by
    have h3 : m % 3 ≠ 0 := by
      intro hz
      exact hm3 (Nat.dvd_of_mod_eq_zero hz)
    omega
  obtain ⟨a, ha⟩ := exists_nat_cyclicNeighborWeighted_eq_iff τ
  have hmem : weberF (τ : ℂ) ^ 2 ∈ M := by
    obtain ⟨x, hx⟩ := (exists_algebraMap_eq_iff_forall_algEquiv
      (K := M) (weberF (τ : ℂ) ^ 2)).mpr (by
      intro σ
      let σK : ℂ ≃ₐ[K] ℂ := σ.restrictScalars K
      have hτ : σK (τ : ℂ) = (τ : ℂ) := by
        exact σ.commutes ⟨(τ : ℂ), IntermediateField.mem_adjoin_simple_self K _⟩
      obtain ⟨p, hpF, hpW⟩ := exists_jointOrbit_pair_of_map_eq σK.toRingHom
        (fun p : weberJointIndex => (weberJointBranch p : UpperHalfPlane → ℂ) τ)
        (fun p : weberJointIndex => cyclicNeighborWeighted a (weberJointMatrix p) τ)
        (hfixed a σK hτ) (1, 1)
      rw [weberJointBranch_one, coe_weberBranchBasis] at hpF
      rw [weberJointMatrix_one] at hpW
      obtain ⟨B, hB⟩ := exists_cyclicNeighborData_eq_galois τ σK
      have hweighted : cyclicNeighborWeighted a (weberJointMatrix p) τ =
          cyclicNeighborWeighted a B τ :=
        hpW.symm.trans (cyclicNeighborWeighted_eq_galois_of_data a τ σK B hB).symm
      have hdata : cyclicNeighborData (weberJointMatrix p) τ =
          fun i => σK (cyclicNeighborData 1 τ i) :=
        ((ha _ _).mp hweighted).trans hB
      have hcomm := cyclicNeighborData_galois_eq_imp_commute_CM τ m hquad hm9 hm8 σK hτ
        (weberJointMatrix p) hdata
      rw [weberJointBranch_eq_base_of_commute_CM p (m : ZMod 24)
        (weberParameter_mod_twentyFour hm8 hm3) hcomm, coe_weberBranchBasis] at hpF
      exact hpF)
    exact hx ▸ x.property
  apply (weberF_sq_mem_cmAdjoin_iff hm).mp
  simpa only [τ, K, M, coe_sqrtPoint hm] using hmem

end BakerHeegnerStark
