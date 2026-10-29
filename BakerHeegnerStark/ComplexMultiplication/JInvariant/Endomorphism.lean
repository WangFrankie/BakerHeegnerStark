/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticCurves.JInvariant.Uniformization
import BakerHeegnerStark.EllipticCurves.JInvariant.Galois

/-!
# Quadratic-period multiplication on the j-generated model

The fixed actual complex normalization carries the proved CM point-group
endomorphism to the coefficient model. It is exactly multiplication of
the period argument by `τ`, satisfies its quadratic relation, and has
the specified companion matrix on every positive-level torsion subgroup.

For the genuine coefficient action, CM commutation is exactly matrix
centralization. `ComplexMultiplication/Galois.lean` proves actual commutation for positive
quadratic parameters and automorphisms fixing the period, by constructing
the analytic lift from finite coordinates. No algebraic curve-morphism
degree is asserted by this point-group model.
-/

open scoped IntermediateField Matrix
namespace BakerHeegnerStark

/-- Quadratic-period multiplication on the actual complex points of the j-generated coefficient model. -/
noncomputable def jInvariantCurveCMEnd [DecidableEq ℂ] (τ : UpperHalfPlane) (m : ℤ)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) :
    ((jInvariantCurve τ).baseChange ℂ).toAffine.Point →+
      ((jInvariantCurve τ).baseChange ℂ).toAffine.Point :=
  (jInvariantCurvePointEquiv τ).toAddMonoidHom.comp
    ((periodCurveCMEnd τ m hτ).comp (jInvariantCurvePointEquiv τ).symm.toAddMonoidHom)

/-- In the chosen actual normalization, the endomorphism is exactly `z ↦ τz`. -/
theorem jInvariantCurveCMEnd_periodPoint [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℤ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (z : ℂ) :
    jInvariantCurveCMEnd τ m hτ (jInvariantCurvePointEquiv τ (standardPeriodPoint τ z)) =
      jInvariantCurvePointEquiv τ (standardPeriodPoint τ ((τ : ℂ) * z)) := by
  change (jInvariantCurvePointEquiv τ) (periodCurveCMEnd τ m hτ
    ((jInvariantCurvePointEquiv τ).symm ((jInvariantCurvePointEquiv τ) (standardPeriodPoint τ z)))) = _
  rw [AddEquiv.symm_apply_apply, periodCurveCMEnd_standardPeriodPoint]

/-- The actual model point-group endomorphism satisfies its quadratic CM relation. -/
theorem jInvariantCurveCMEnd_sq [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℤ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    jInvariantCurveCMEnd τ m hτ (jInvariantCurveCMEnd τ m hτ P) = (-m) • P := by
  let e := jInvariantCurvePointEquiv τ
  change e (periodCurveCMEnd τ m hτ (e.symm (e (periodCurveCMEnd τ m hτ (e.symm P))))) = _
  rw [e.symm_apply_apply, periodCurveCMEnd_sq, map_zsmul, e.apply_symm_apply]

/-- The same actual quadratic-period multiplication on the model's torsion points. -/
noncomputable def jInvariantCurveTorsionCMEnd [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (m : ℤ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) :
    WeierstrassTorsion (jInvariantCurve τ).toAffine ℂ N →+
      WeierstrassTorsion (jInvariantCurve τ).toAffine ℂ N :=
  (jInvariantCurveTorsionEquiv τ N).toAddMonoidHom.comp
    ((periodCurveTorsionCMEnd τ N m hτ).comp
      (jInvariantCurveTorsionEquiv τ N).symm.toAddMonoidHom)

/-- The torsion endomorphism is the restriction of the actual model point-group endomorphism. -/
@[simp]
theorem jInvariantCurveTorsionCMEnd_val [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (m : ℤ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (P : WeierstrassTorsion (jInvariantCurve τ).toAffine ℂ N) :
    (jInvariantCurveTorsionCMEnd τ N m hτ P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) =
      jInvariantCurveCMEnd τ m hτ P := rfl

/-- Normalization intertwines the two actual torsion CM actions. -/
theorem jInvariantCurveTorsionCMEnd_equiv_apply [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (m : ℤ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (P : PeriodCurveTorsion τ N) :
    jInvariantCurveTorsionCMEnd τ N m hτ (jInvariantCurveTorsionEquiv τ N P) =
      jInvariantCurveTorsionEquiv τ N (periodCurveTorsionCMEnd τ N m hτ P) := by
  change (jInvariantCurveTorsionEquiv τ N) (periodCurveTorsionCMEnd τ N m hτ
    ((jInvariantCurveTorsionEquiv τ N).symm ((jInvariantCurveTorsionEquiv τ N) P))) = _
  rw [AddEquiv.symm_apply_apply]

/-- The specified level coordinates still carry the actual quadratic companion action. -/
theorem jInvariantCurveTorsionCMEnd_coordinates_apply [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) (m : ℤ)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (x : Fin 2 → ZMod N) :
    jInvariantCurveTorsionCMEnd τ N m hτ (jInvariantCurveTorsionCoordinatesEquiv τ N hN x) =
      jInvariantCurveTorsionCoordinatesEquiv τ N hN ![-(m : ZMod N) * x 1, x 0] := by
  change jInvariantCurveTorsionCMEnd τ N m hτ
    (jInvariantCurveTorsionEquiv τ N (periodCurveTorsionCoordinatesEquiv τ N hN x)) =
      jInvariantCurveTorsionEquiv τ N (periodCurveTorsionCoordinatesEquiv τ N hN _)
  rw [jInvariantCurveTorsionCMEnd_equiv_apply, periodCurveTorsionCMEnd_coordinates_apply]

/-- The actual j-generated model's torsion CM matrix, including composite levels. -/
theorem jInvariantCurveTorsionCMEnd_eq_matrix [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) (m : ℤ)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (x : Fin 2 → ZMod N) :
    (jInvariantCurveTorsionCoordinatesEquiv τ N hN).symm
        (jInvariantCurveTorsionCMEnd τ N m hτ (jInvariantCurveTorsionCoordinatesEquiv τ N hN x)) =
      (!![0, -(m : ZMod N); 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x := by
  rw [jInvariantCurveTorsionCMEnd_coordinates_apply, AddEquiv.symm_apply_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- For the genuine coefficient action, the CM-centralizer condition is exactly
commutation with the actual model torsion point-group endomorphism. -/
theorem jInvariantCurveTorsionGaloisMatrix_commute_iff [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) (m : ℤ)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) :
    Commute (jInvariantCurveTorsionGaloisMatrix τ N hN σ :
        Matrix (Fin 2) (Fin 2) (ZMod N)) !![0, -(m : ZMod N); 1, 0] ↔
      ∀ P, (weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd
          (jInvariantCurveTorsionCMEnd τ N m hτ P) =
        jInvariantCurveTorsionCMEnd τ N m hτ
          ((weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd P) := by
  let e := jInvariantCurveTorsionCoordinatesEquiv τ N hN
  let A : Matrix (Fin 2) (Fin 2) (ZMod N) := jInvariantCurveTorsionGaloisMatrix τ N hN σ
  let J : Matrix (Fin 2) (Fin 2) (ZMod N) := !![0, -(m : ZMod N); 1, 0]
  have hG : ∀ P, e.symm ((weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd P) =
      A *ᵥ e.symm P := jInvariantCurveTorsionGaloisMatrix_apply τ N hN σ
  have hC : ∀ P, e.symm (jInvariantCurveTorsionCMEnd τ N m hτ P) = J *ᵥ e.symm P := by
    intro P
    simpa only [e, J, AddEquiv.apply_symm_apply] using
      jInvariantCurveTorsionCMEnd_eq_matrix τ N hN m hτ (e.symm P)
  change Commute A J ↔ _
  constructor
  · intro h P
    apply e.symm.injective
    simp only [hG, hC, Matrix.mulVec_mulVec]
    exact congrArg (fun B => B *ᵥ e.symm P) h.eq
  · intro h
    change A * J = J * A
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    have hx := congrArg e.symm (h (e x))
    simpa only [hG, hC, AddEquiv.symm_apply_apply, Matrix.mulVec_mulVec] using hx

end BakerHeegnerStark
