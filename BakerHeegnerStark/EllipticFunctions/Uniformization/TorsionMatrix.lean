/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Uniformization.Torsion
import BakerHeegnerStark.EllipticFunctions.PeriodTorus.TorsionMatrix

/-!
# Matrices of actual period-curve torsion automorphisms

The proved torsion uniformization transports the existing period-torus
matrix representation to the actual complex curve torsion. In the specified
ordered division-point coordinates this gives the full automorphism group
`GL₂(ℤ/Nℤ)` at every positive level, including composite levels.

Commutation with the actual quadratic-period point-group endomorphism is
exactly centralization of its companion matrix. Any two compatible torsion
automorphisms therefore commute. These are statements about actual complex
point groups, not arithmetic Galois actions or algebraic CM morphisms.
-/

open scoped Matrix MatrixGroups

namespace BakerHeegnerStark

variable [DecidableEq ℂ]

/-- Conjugation through the actual torsion uniformization, with composition as multiplication. -/
noncomputable def periodCurveTorsionAutEquiv (τ : UpperHalfPlane) (N : ℕ) :
    Multiplicative (AddAut (PeriodCurveTorsion τ N)) ≃*
      Multiplicative (AddAut (PeriodTorsion (τ : ℂ) N)) :=
  AddEquiv.toMultiplicative (AddAut.congr (periodCurveTorsionEquiv τ N).symm)

/-- The conjugated automorphism acts on actual period-torus torsion points. -/
@[simp]
theorem periodCurveTorsionAutEquiv_apply (τ : UpperHalfPlane) (N : ℕ)
    (u : Multiplicative (AddAut (PeriodCurveTorsion τ N)))
    (p : PeriodTorsion (τ : ℂ) N) :
    (periodCurveTorsionAutEquiv τ N u).toAdd p =
      (periodCurveTorsionEquiv τ N).symm (u.toAdd (periodCurveTorsionEquiv τ N p)) := rfl

/-- The matrix representation of actual curve torsion automorphisms in the specified period basis. -/
noncomputable def periodCurveTorsionAutMatrix (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) :
    Multiplicative (AddAut (PeriodCurveTorsion τ N)) →* GL (Fin 2) (ZMod N) :=
  (periodTorsionAutMatrix (τ : ℂ) (ne_of_gt τ.im_pos) N hN).comp
    (periodCurveTorsionAutEquiv τ N).toMonoidHom

/-- The matrix acts in the specified actual curve division-point coordinates. -/
theorem periodCurveTorsionAutMatrix_mulVec (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N)
    (u : Multiplicative (AddAut (PeriodCurveTorsion τ N))) (x : Fin 2 → ZMod N) :
    (periodCurveTorsionAutMatrix τ N hN u : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x =
      (periodCurveTorsionCoordinatesEquiv τ N hN).symm
        (u.toAdd (periodCurveTorsionCoordinatesEquiv τ N hN x)) := by
  exact periodTorsionAutMatrix_mulVec (τ : ℂ) (ne_of_gt τ.im_pos) N hN
    (periodCurveTorsionAutEquiv τ N u) x

/-- Coordinates of the image of an arbitrary actual curve torsion point. -/
theorem periodCurveTorsionAutMatrix_apply (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N)
    (u : Multiplicative (AddAut (PeriodCurveTorsion τ N))) (P : PeriodCurveTorsion τ N) :
    (periodCurveTorsionCoordinatesEquiv τ N hN).symm (u.toAdd P) =
      (periodCurveTorsionAutMatrix τ N hN u : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ
        (periodCurveTorsionCoordinatesEquiv τ N hN).symm P := by
  simpa only [AddEquiv.apply_symm_apply] using
    (periodCurveTorsionAutMatrix_mulVec τ N hN u
      ((periodCurveTorsionCoordinatesEquiv τ N hN).symm P)).symm

/-- Every invertible residue matrix represents exactly one actual curve torsion automorphism. -/
theorem periodCurveTorsionAutMatrix_bijective (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) :
    Function.Bijective (periodCurveTorsionAutMatrix τ N hN) :=
  (periodTorsionAutMatrix_bijective (τ : ℂ) (ne_of_gt τ.im_pos) N hN).comp
    (periodCurveTorsionAutEquiv τ N).bijective

/-- The full group isomorphism for actual curve torsion in the specified period coordinates. -/
noncomputable def periodCurveTorsionAutMatrixEquiv (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) :
    Multiplicative (AddAut (PeriodCurveTorsion τ N)) ≃* GL (Fin 2) (ZMod N) :=
  MulEquiv.ofBijective (periodCurveTorsionAutMatrix τ N hN)
    (periodCurveTorsionAutMatrix_bijective τ N hN)

/-- Torsion uniformization preserves and reflects commutation with quadratic-period multiplication. -/
theorem periodCurveTorsionAutEquiv_cm_commute_iff (τ : UpperHalfPlane) (N : ℕ)
    (m : ℤ) (hquad : (τ : ℂ) ^ 2 = -(m : ℂ))
    (u : Multiplicative (AddAut (PeriodCurveTorsion τ N))) :
    (∀ p, (periodCurveTorsionAutEquiv τ N u).toAdd
        (periodTorsionCMEnd (τ : ℂ) N m hquad p) =
      periodTorsionCMEnd (τ : ℂ) N m hquad ((periodCurveTorsionAutEquiv τ N u).toAdd p)) ↔
      ∀ P, u.toAdd (periodCurveTorsionCMEnd τ N m hquad P) =
        periodCurveTorsionCMEnd τ N m hquad (u.toAdd P) := by
  let e := periodCurveTorsionEquiv τ N
  have hC (P : PeriodCurveTorsion τ N) :
      e.symm (periodCurveTorsionCMEnd τ N m hquad P) =
        periodTorsionCMEnd (τ : ℂ) N m hquad (e.symm P) := by
    apply e.injective
    rw [e.apply_symm_apply, ← periodCurveTorsionCMEnd_equiv_apply, e.apply_symm_apply]
  simp only [periodCurveTorsionAutEquiv_apply]
  constructor
  · intro h P
    obtain ⟨p, rfl⟩ := e.surjective P
    apply e.symm.injective
    rw [hC, periodCurveTorsionCMEnd_equiv_apply]
    exact h p
  · intro h p
    have hp := congrArg e.symm (h (e p))
    rw [periodCurveTorsionCMEnd_equiv_apply, hC] at hp
    exact hp

/-- Actual curve CM compatibility is exactly centralization of the quadratic companion matrix. -/
theorem periodCurveTorsionAutMatrix_commute_iff (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N)
    (m : ℤ) (hquad : (τ : ℂ) ^ 2 = -(m : ℂ))
    (u : Multiplicative (AddAut (PeriodCurveTorsion τ N))) :
    Commute (periodCurveTorsionAutMatrix τ N hN u : Matrix (Fin 2) (Fin 2) (ZMod N))
        !![0, -(m : ZMod N); 1, 0] ↔
      ∀ P, u.toAdd (periodCurveTorsionCMEnd τ N m hquad P) =
        periodCurveTorsionCMEnd τ N m hquad (u.toAdd P) := by
  change Commute (periodTorsionAutMatrix (τ : ℂ) (ne_of_gt τ.im_pos) N hN
    (periodCurveTorsionAutEquiv τ N u) : Matrix (Fin 2) (Fin 2) (ZMod N)) _ ↔ _
  rw [periodTorsionAutMatrix_commute_iff]
  exact periodCurveTorsionAutEquiv_cm_commute_iff τ N m hquad u

/-- Actual curve torsion automorphisms commuting with quadratic-period multiplication commute. -/
theorem periodCurveTorsionCMEnd_commuting_auts_commute (τ : UpperHalfPlane)
    (N : ℕ) (hN : 0 < N) (m : ℤ) (hquad : (τ : ℂ) ^ 2 = -(m : ℂ))
    (u v : Multiplicative (AddAut (PeriodCurveTorsion τ N)))
    (hu : ∀ P, u.toAdd (periodCurveTorsionCMEnd τ N m hquad P) =
      periodCurveTorsionCMEnd τ N m hquad (u.toAdd P))
    (hv : ∀ P, v.toAdd (periodCurveTorsionCMEnd τ N m hquad P) =
      periodCurveTorsionCMEnd τ N m hquad (v.toAdd P)) : Commute u v := by
  change u * v = v * u
  apply (periodCurveTorsionAutEquiv τ N).injective
  rw [map_mul, map_mul]
  exact (periodTorsionCMEnd_commuting_auts_commute (τ : ℂ) (ne_of_gt τ.im_pos)
    N hN m hquad (periodCurveTorsionAutEquiv τ N u) (periodCurveTorsionAutEquiv τ N v)
    ((periodCurveTorsionAutEquiv_cm_commute_iff τ N m hquad u).mpr hu)
    ((periodCurveTorsionAutEquiv_cm_commute_iff τ N m hquad v).mpr hv)).eq

end BakerHeegnerStark
