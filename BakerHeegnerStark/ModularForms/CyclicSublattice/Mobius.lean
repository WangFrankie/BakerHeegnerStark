/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.CyclicSublattice.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Matrix Relations and Actual Cyclic-Sublattice Points

A positive upper-triangular integral matrix acts on the upper half-plane by
its cyclic-sublattice transformation. Consequently an integral matrix
relation with left and right special-linear factors gives the corresponding
relation between the actual points and their actual j-invariants.
-/

open Matrix UpperHalfPlane ModularForm
open scoped MatrixGroups

noncomputable section

namespace BakerHeegnerStark

private def cyclicSublatticeIntegralMatrix (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(t.1 : ℤ), (t.2.1 : ℤ); 0, (t.2.2 : ℤ)]

private theorem cyclicSublatticeRealMatrix_det_pos {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) :
    0 < ((cyclicSublatticeIntegralMatrix t).map (Int.castRingHom ℝ)).det := by
  simpa [cyclicSublatticeIntegralMatrix, Matrix.det_fin_two] using
    mul_pos (Nat.cast_pos.mpr ha : 0 < (t.1 : ℝ))
      (Nat.cast_pos.mpr hd : 0 < (t.2.2 : ℝ))

private def cyclicSublatticeGL (t : ℕ × ℕ × ℕ)
    (ha : 0 < t.1) (hd : 0 < t.2.2) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero
    ((cyclicSublatticeIntegralMatrix t).map (Int.castRingHom ℝ))
    (ne_of_gt (cyclicSublatticeRealMatrix_det_pos ha hd))

private theorem cyclicSublatticeGL_det_pos {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) :
    0 < (cyclicSublatticeGL t ha hd).det.val :=
  cyclicSublatticeRealMatrix_det_pos ha hd

private theorem cyclicSublatticeGL_smul {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) (τ : UpperHalfPlane) :
    cyclicSublatticeGL t ha hd • τ = cyclicSublatticePoint t τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (cyclicSublatticeGL_det_pos ha hd),
    cyclicSublatticePoint_coe ha hd]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, cyclicSublatticeGL,
    cyclicSublatticeIntegralMatrix]

/-- A matrix relation with special-linear factors is a relation between the
actual cyclic-sublattice points in the upper half-plane. -/
theorem cyclicSublatticePoint_of_matrix_relation
    (t u : ℕ × ℕ × ℕ)
    (haT : 0 < t.1) (hdT : 0 < t.2.2)
    (haU : 0 < u.1) (hdU : 0 < u.2.2)
    (γ κ : SL(2, ℤ))
    (h : (!![(u.1 : ℤ), (u.2.1 : ℤ); 0, (u.2.2 : ℤ)] :
        Matrix (Fin 2) (Fin 2) ℤ) =
      (κ : Matrix (Fin 2) (Fin 2) ℤ) *
        (!![(t.1 : ℤ), (t.2.1 : ℤ); 0, (t.2.2 : ℤ)] :
          Matrix (Fin 2) (Fin 2) ℤ) *
        (γ : Matrix (Fin 2) (Fin 2) ℤ))
    (τ : UpperHalfPlane) :
    cyclicSublatticePoint u τ = κ • cyclicSublatticePoint t (γ • τ) := by
  have hGL : cyclicSublatticeGL u haU hdU =
      SpecialLinearGroup.mapGL ℝ κ * cyclicSublatticeGL t haT hdT *
        SpecialLinearGroup.mapGL ℝ γ := by
    apply Units.ext
    change (cyclicSublatticeIntegralMatrix u).map (Int.castRingHom ℝ) =
      ((κ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) *
        (cyclicSublatticeIntegralMatrix t).map (Int.castRingHom ℝ)) *
        (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A.map (Int.castRingHom ℝ)) h
  rw [← cyclicSublatticeGL_smul haU hdU, hGL, mul_smul, mul_smul]
  change SpecialLinearGroup.mapGL ℝ κ •
      (cyclicSublatticeGL t haT hdT • (γ • τ)) = _
  rw [cyclicSublatticeGL_smul haT hdT]
  rfl

/-- Special-linear matrix relations identify the actual j-values of the
corresponding cyclic-sublattice transforms. -/
theorem jInvariant_cyclicSublatticePoint_of_matrix_relation
    (t u : ℕ × ℕ × ℕ)
    (haT : 0 < t.1) (hdT : 0 < t.2.2)
    (haU : 0 < u.1) (hdU : 0 < u.2.2)
    (γ κ : SL(2, ℤ))
    (h : (!![(u.1 : ℤ), (u.2.1 : ℤ); 0, (u.2.2 : ℤ)] :
        Matrix (Fin 2) (Fin 2) ℤ) =
      (κ : Matrix (Fin 2) (Fin 2) ℤ) *
        (!![(t.1 : ℤ), (t.2.1 : ℤ); 0, (t.2.2 : ℤ)] :
          Matrix (Fin 2) (Fin 2) ℤ) *
        (γ : Matrix (Fin 2) (Fin 2) ℤ))
    (τ : UpperHalfPlane) :
    jInvariant (cyclicSublatticePoint u τ) =
      jInvariant (cyclicSublatticePoint t (γ • τ)) := by
  rw [cyclicSublatticePoint_of_matrix_relation t u haT hdT haU hdU γ κ h τ,
    ModularForm.jInvariant_smul]

end BakerHeegnerStark
