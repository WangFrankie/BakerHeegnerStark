/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Uniformization.Point
import BakerHeegnerStark.EllipticCurves.Torsion
import Mathlib.Data.Matrix.Mul

/-!
# Actual period-curve torsion and quadratic-period multiplication

The proved additive uniformization restricts to the actual torsion
subgroups at every level, including zero. At positive levels the specified
ordered period basis gives the full residue coordinates and cardinality.

The curve has its actual complex lattice invariants as coefficients.
These complex point-group constructions do not assert an arithmetic
field of definition or an algebraic CM endomorphism over that field.
-/

open scoped Matrix

namespace BakerHeegnerStark

/-- The actual `N`-torsion subgroup of the standard complex period curve. -/
noncomputable def PeriodCurveTorsion [DecidableEq ℂ] (τ : UpperHalfPlane) (N : ℕ) :
    AddSubgroup (periodCurve (standardPeriodPair τ)).toAffine.Point :=
  AddSubgroup.torsionBy (periodCurve (standardPeriodPair τ)).toAffine.Point (N : ℤ)

/-- The proved uniformization restricted to actual torsion, including level zero. -/
noncomputable def periodCurveTorsionEquiv [DecidableEq ℂ] (τ : UpperHalfPlane) (N : ℕ) :
    PeriodTorsion (τ : ℂ) N ≃+ PeriodCurveTorsion τ N :=
  (standardPeriodTorusEquiv τ).torsionByEquiv (N : ℤ)

/-- The torsion restriction is the actual Weierstrass point map on underlying points. -/
@[simp]
theorem periodCurveTorsionEquiv_val [DecidableEq ℂ] (τ : UpperHalfPlane) (N : ℕ)
    (p : PeriodTorsion (τ : ℂ) N) :
    (periodCurveTorsionEquiv τ N p : (periodCurve (standardPeriodPair τ)).toAffine.Point) =
      standardPeriodTorusPoint τ (p : PeriodTorus (τ : ℂ)) := rfl

/-- The specified ordered level structure on the actual curve torsion. -/
noncomputable def periodCurveTorsionCoordinatesEquiv [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) :
    (Fin 2 → ZMod N) ≃+ PeriodCurveTorsion τ N :=
  (periodTorsionEquiv (τ : ℂ) (ne_of_gt τ.im_pos) N hN).trans
    (periodCurveTorsionEquiv τ N)

/-- The ordered residue coordinates retain the actual integer division-point formula. -/
theorem periodCurveTorsionCoordinatesEquiv_intCast [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    (periodCurveTorsionCoordinatesEquiv τ N hN ![(a : ZMod N), (b : ZMod N)] :
      (periodCurve (standardPeriodPair τ)).toAffine.Point) =
        standardPeriodPoint τ (((a : ℂ) + (b : ℂ) * (τ : ℂ)) / (N : ℂ)) := by
  change (periodCurveTorsionEquiv τ N
    (periodTorsionEquiv (τ : ℂ) (ne_of_gt τ.im_pos) N hN
      ![(a : ZMod N), (b : ZMod N)]) :
      (periodCurve (standardPeriodPair τ)).toAffine.Point) = _
  rw [periodTorsionEquiv_intCast]
  rfl

/-- The actual complex curve has exactly `N²` torsion points at every positive level. -/
theorem nat_card_periodCurveTorsion [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) :
    Nat.card (PeriodCurveTorsion τ N) = N ^ 2 := by
  calc
    Nat.card (PeriodCurveTorsion τ N) = Nat.card (PeriodTorsion (τ : ℂ) N) :=
      Nat.card_congr (periodCurveTorsionEquiv τ N).symm.toEquiv
    _ = N ^ 2 := nat_card_periodTorsion (τ : ℂ) (ne_of_gt τ.im_pos) N hN

/-- Multiplication by the quadratic period on the actual complex curve point group. -/
noncomputable def periodCurveCMEnd [DecidableEq ℂ] (τ : UpperHalfPlane) (m : ℤ)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) :
    (periodCurve (standardPeriodPair τ)).toAffine.Point →+
      (periodCurve (standardPeriodPair τ)).toAffine.Point :=
  (standardPeriodTorusEquiv τ).toAddMonoidHom.comp
    ((periodTorusCMEnd (τ : ℂ) m hτ).toAddMonoidHom.comp
      (standardPeriodTorusEquiv τ).symm.toAddMonoidHom)

/-- This group endomorphism is actual multiplication of the complex argument by `τ`. -/
theorem periodCurveCMEnd_standardPeriodPoint [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℤ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (z : ℂ) :
    periodCurveCMEnd τ m hτ (standardPeriodPoint τ z) =
      standardPeriodPoint τ ((τ : ℂ) * z) := by
  let e := standardPeriodTorusEquiv τ
  have he : e ((periodModule (τ : ℂ)).mkQ z) = standardPeriodPoint τ z := rfl
  change e (periodTorusCMEnd (τ : ℂ) m hτ (e.symm (standardPeriodPoint τ z))) = _
  rw [← he, e.symm_apply_apply]
  rfl

/-- The actual curve point-group endomorphism satisfies its quadratic CM equation. -/
theorem periodCurveCMEnd_sq [DecidableEq ℂ] (τ : UpperHalfPlane) (m : ℤ)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (P : (periodCurve (standardPeriodPair τ)).toAffine.Point) :
    periodCurveCMEnd τ m hτ (periodCurveCMEnd τ m hτ P) = (-m) • P := by
  let e := standardPeriodTorusEquiv τ
  let c := periodTorusCMEnd (τ : ℂ) m hτ
  have hc : c (c (e.symm P)) = (-m) • e.symm P := by
    have h := congrArg (fun f : PeriodTorus (τ : ℂ) →ₗ[ℤ] PeriodTorus (τ : ℂ) =>
      f (e.symm P)) (periodTorusCMEnd_sq (τ : ℂ) m hτ)
    simpa only [c, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] using h
  change e (c (e.symm (e (c (e.symm P))))) = _
  rw [e.symm_apply_apply, hc, map_zsmul, e.apply_symm_apply]

/-- Quadratic-period multiplication restricts to actual curve torsion. -/
noncomputable def periodCurveTorsionCMEnd [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (m : ℤ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) :
    PeriodCurveTorsion τ N →+ PeriodCurveTorsion τ N where
  toFun P := ⟨periodCurveCMEnd τ m hτ P, by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp P.property, map_zero]⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' P Q := by apply Subtype.ext; exact map_add _ _ _

/-- The actual torsion uniformization intertwines quadratic-period multiplication. -/
theorem periodCurveTorsionCMEnd_equiv_apply [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (m : ℤ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (p : PeriodTorsion (τ : ℂ) N) :
    periodCurveTorsionCMEnd τ N m hτ (periodCurveTorsionEquiv τ N p) =
      periodCurveTorsionEquiv τ N (periodTorsionCMEnd (τ : ℂ) N m hτ p) := by
  apply Subtype.ext
  change (standardPeriodTorusEquiv τ) (periodTorusCMEnd (τ : ℂ) m hτ
    ((standardPeriodTorusEquiv τ).symm ((standardPeriodTorusEquiv τ) p))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- Quadratic-period multiplication has the specified companion coordinates on actual curve torsion. -/
theorem periodCurveTorsionCMEnd_coordinates_apply [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) (m : ℤ)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (x : Fin 2 → ZMod N) :
    periodCurveTorsionCMEnd τ N m hτ (periodCurveTorsionCoordinatesEquiv τ N hN x) =
      periodCurveTorsionCoordinatesEquiv τ N hN ![-(m : ZMod N) * x 1, x 0] := by
  change periodCurveTorsionCMEnd τ N m hτ
    (periodCurveTorsionEquiv τ N (periodTorsionEquiv (τ : ℂ) (ne_of_gt τ.im_pos) N hN x)) =
      periodCurveTorsionEquiv τ N (periodTorsionEquiv (τ : ℂ) (ne_of_gt τ.im_pos) N hN _)
  rw [periodCurveTorsionCMEnd_equiv_apply, periodTorsionCMEnd_equiv_apply]

/-- The actual curve torsion CM action is the quadratic companion matrix, also at composite levels. -/
theorem periodCurveTorsionCMEnd_eq_matrix [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) (m : ℤ)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (x : Fin 2 → ZMod N) :
    (periodCurveTorsionCoordinatesEquiv τ N hN).symm
        (periodCurveTorsionCMEnd τ N m hτ (periodCurveTorsionCoordinatesEquiv τ N hN x)) =
      (!![0, -(m : ZMod N); 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x := by
  rw [periodCurveTorsionCMEnd_coordinates_apply, AddEquiv.symm_apply_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end BakerHeegnerStark