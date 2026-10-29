/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticCurves.JInvariant.Uniformization
import BakerHeegnerStark.EllipticFunctions.Uniformization.TorsionMatrix

/-!
# Actual Galois matrices in the specified j-model torsion coordinates

Coefficient automorphisms of `ℂ/ℚ(j(τ))` act on the actual complex torsion
points of `jInvariantCurve τ`. Conjugating this action through the same chosen
complex normalization as `JInvariantPoint` gives an action on period-curve
torsion and its matrix in the specified ordered division-point coordinates.
The existing torsion matrix representation supplies the linearization at
every positive level, including composite levels.

The transported action is not obtained by applying the automorphism directly
to the period curve's lattice invariants `g₂,g₃`. No field of definition for
the chosen complex change, CM compatibility, or Galois descent assertion is
used or claimed here.
-/

open scoped IntermediateField Matrix MatrixGroups

namespace BakerHeegnerStark

variable [DecidableEq ℂ]

/-- The actual j-model coefficient action, transported to period-curve torsion
through the fixed complex point normalization. This is not a coefficient
Galois action on the period curve's lattice invariants. -/
noncomputable def jInvariantPeriodCurveTorsionGaloisAut (τ : UpperHalfPlane) (N : ℕ) :
    (ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) →*
      Multiplicative (AddAut (PeriodCurveTorsion τ N)) :=
  (AddEquiv.toMultiplicative
    (AddAut.congr (jInvariantCurveTorsionEquiv τ N).symm)).toMonoidHom.comp
      (weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N)

/-- The transported action conjugates the actual coefficient map on j-model torsion. -/
@[simp]
theorem jInvariantPeriodCurveTorsionGaloisAut_apply (τ : UpperHalfPlane) (N : ℕ)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) (P : PeriodCurveTorsion τ N) :
    (jInvariantPeriodCurveTorsionGaloisAut τ N σ).toAdd P =
      (jInvariantCurveTorsionEquiv τ N).symm
        ((weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd
          (jInvariantCurveTorsionEquiv τ N P)) := rfl

/-- The genuine coefficient Galois representation in the specified ordered
coordinates of the actual j-generated model's complex `N`-torsion. -/
noncomputable def jInvariantCurveTorsionGaloisMatrix
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) :
    (ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) →* GL (Fin 2) (ZMod N) :=
  (periodCurveTorsionAutMatrix τ N hN).comp
    (jInvariantPeriodCurveTorsionGaloisAut τ N)

/-- Matrix multiplication gives the coordinates of the actual coefficient Galois image. -/
theorem jInvariantCurveTorsionGaloisMatrix_mulVec
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) (x : Fin 2 → ZMod N) :
    (jInvariantCurveTorsionGaloisMatrix τ N hN σ :
        Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x =
      (jInvariantCurveTorsionCoordinatesEquiv τ N hN).symm
        ((weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd
          (jInvariantCurveTorsionCoordinatesEquiv τ N hN x)) := by
  exact periodCurveTorsionAutMatrix_mulVec τ N hN
    (jInvariantPeriodCurveTorsionGaloisAut τ N σ) x

/-- Coordinates of the actual coefficient Galois image of an arbitrary j-model torsion point. -/
theorem jInvariantCurveTorsionGaloisMatrix_apply
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (P : WeierstrassTorsion (jInvariantCurve τ).toAffine ℂ N) :
    (jInvariantCurveTorsionCoordinatesEquiv τ N hN).symm
        ((weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd P) =
      (jInvariantCurveTorsionGaloisMatrix τ N hN σ :
        Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ
          (jInvariantCurveTorsionCoordinatesEquiv τ N hN).symm P := by
  simpa only [AddEquiv.apply_symm_apply] using
    (jInvariantCurveTorsionGaloisMatrix_mulVec τ N hN σ
      ((jInvariantCurveTorsionCoordinatesEquiv τ N hN).symm P)).symm

/-- The matrix kernel consists exactly of coefficient automorphisms fixing
all actual complex `N`-torsion points of the j-generated model. -/
theorem jInvariantCurveTorsionGaloisMatrix_eq_one_iff
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) :
    jInvariantCurveTorsionGaloisMatrix τ N hN σ = 1 ↔
      ∀ P : WeierstrassTorsion (jInvariantCurve τ).toAffine ℂ N,
        (weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd P = P := by
  constructor
  · intro h P
    apply (jInvariantCurveTorsionCoordinatesEquiv τ N hN).symm.injective
    rw [jInvariantCurveTorsionGaloisMatrix_apply, h]
    exact Matrix.one_mulVec _
  · intro h
    apply Units.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    rw [jInvariantCurveTorsionGaloisMatrix_mulVec, h]
    simp only [AddEquiv.symm_apply_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

/-- A residue vector is fixed exactly when its specified actual j-model
`N`-torsion point is fixed by the coefficient Galois action. -/
theorem jInvariantCurveTorsionGaloisMatrix_mulVec_eq_self_iff
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) (x : Fin 2 → ZMod N) :
    (jInvariantCurveTorsionGaloisMatrix τ N hN σ :
        Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x = x ↔
      (weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd
        (jInvariantCurveTorsionCoordinatesEquiv τ N hN x) =
          jInvariantCurveTorsionCoordinatesEquiv τ N hN x := by
  rw [jInvariantCurveTorsionGaloisMatrix_mulVec]
  constructor
  · intro h
    simpa only [AddEquiv.apply_symm_apply] using
      congrArg (jInvariantCurveTorsionCoordinatesEquiv τ N hN) h
  · intro h
    rw [h, AddEquiv.symm_apply_apply]

end BakerHeegnerStark
