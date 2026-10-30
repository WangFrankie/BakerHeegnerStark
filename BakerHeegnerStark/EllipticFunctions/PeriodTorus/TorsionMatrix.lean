/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.PeriodTorus.Torsion
import QNFMathlib.Algebra.QuadraticAlgebra.Matrix
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.End

/-!
# Matrices of actual period-torus torsion automorphisms

The specified division-point coordinates identify additive automorphisms of
the actual period-torus `N`-torsion with `GL₂(ℤ/Nℤ)`, for every positive level.
An additive map between these residue modules is automatically `ZMod N`-linear;
no field or prime-level hypothesis is used.

Mathlib gives `AddAut` an additive group law for composition. The standard
`Multiplicative` tag makes the matrix representation a multiplicative group
homomorphism, with the rightmost automorphism acting first.

Commuting with the actual quadratic CM endomorphism is equivalent to
centralizing `[[0,-m],[1,0]]`. Consequently any two CM-compatible torsion
automorphisms commute. This does not assert that a number-field Galois
automorphism acts on this analytic torus or respects its CM multiplication.
-/

open scoped Matrix MatrixGroups
namespace BakerHeegnerStark

/-- The matrix representation of actual torsion automorphisms in the specified period basis. -/
noncomputable def periodTorsionAutMatrix (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) : Multiplicative (AddAut (PeriodTorsion τ N)) →* GL (Fin 2) (ZMod N) := by
  let e := periodTorsionEquiv τ hτ N hN
  let φ : Multiplicative (AddAut (PeriodTorsion τ N)) →* ((Fin 2 → ZMod N) ≃ₗ[ZMod N] (Fin 2 → ZMod N)) :=
    { toFun := fun u =>
        { e.trans (u.toAdd.trans e.symm) with
          map_smul' := ZMod.map_smul (e.trans (u.toAdd.trans e.symm)) }
      map_one' := by ext x; simp
      map_mul' := by intro u v; ext x; simp }
  exact Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod N) (Fin 2 → ZMod N)).symm.toMonoidHom.comp φ)

/-- The represented matrix acts by conjugating the actual torsion automorphism. -/
theorem periodTorsionAutMatrix_mulVec (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) (u : Multiplicative (AddAut (PeriodTorsion τ N))) (x : Fin 2 → ZMod N) :
    (periodTorsionAutMatrix τ hτ N hN u : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x =
      (periodTorsionEquiv τ hτ N hN).symm (u.toAdd (periodTorsionEquiv τ hτ N hN x)) := by
  dsimp only [periodTorsionAutMatrix, MonoidHom.comp_apply]
  change (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod N)
    (Matrix.GeneralLinearGroup.toLin.symm _) :
    (Fin 2 → ZMod N) →ₗ[ZMod N] (Fin 2 → ZMod N)) x = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- Coordinates of the image of an arbitrary actual torsion point. -/
theorem periodTorsionAutMatrix_apply (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) (u : Multiplicative (AddAut (PeriodTorsion τ N)))
    (p : PeriodTorsion τ N) :
    (periodTorsionEquiv τ hτ N hN).symm (u.toAdd p) =
      (periodTorsionAutMatrix τ hτ N hN u : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ
        (periodTorsionEquiv τ hτ N hN).symm p := by
  simpa only [AddEquiv.apply_symm_apply] using
    (periodTorsionAutMatrix_mulVec τ hτ N hN u ((periodTorsionEquiv τ hτ N hN).symm p)).symm

/-- Every invertible residue matrix represents exactly one actual torsion automorphism. -/
theorem periodTorsionAutMatrix_bijective (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) : Function.Bijective (periodTorsionAutMatrix τ hτ N hN) := by
  let e := periodTorsionEquiv τ hτ N hN
  constructor
  · intro u v h
    change u.toAdd = v.toAdd
    apply AddEquiv.ext
    intro p
    apply (periodTorsionEquiv τ hτ N hN).symm.injective
    rw [periodTorsionAutMatrix_apply, periodTorsionAutMatrix_apply, h]
  · intro A
    let L := (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.toAddEquiv
    let u := e.symm.trans (L.trans e)
    refine ⟨Multiplicative.ofAdd u, ?_⟩
    apply Units.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    rw [periodTorsionAutMatrix_mulVec]
    change e.symm (e (L (e.symm (e x)))) = (A : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x
    rw [e.symm_apply_apply, e.symm_apply_apply]
    rfl

/-- The full group isomorphism between actual torsion automorphisms and invertible matrices. -/
noncomputable def periodTorsionAutMatrixEquiv (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) : Multiplicative (AddAut (PeriodTorsion τ N)) ≃* GL (Fin 2) (ZMod N) :=
  MulEquiv.ofBijective (periodTorsionAutMatrix τ hτ N hN)
    (periodTorsionAutMatrix_bijective τ hτ N hN)

/-- Actual CM compatibility is exactly centralization of the quadratic companion matrix. -/
theorem periodTorsionAutMatrix_commute_iff (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) (m : ℤ) (hm : τ ^ 2 = -(m : ℂ))
    (u : Multiplicative (AddAut (PeriodTorsion τ N))) :
    Commute (periodTorsionAutMatrix τ hτ N hN u : Matrix (Fin 2) (Fin 2) (ZMod N))
        !![0, -(m : ZMod N); 1, 0] ↔
      ∀ p, u.toAdd (periodTorsionCMEnd τ N m hm p) =
        periodTorsionCMEnd τ N m hm (u.toAdd p) := by
  let e := periodTorsionEquiv τ hτ N hN
  let A : Matrix (Fin 2) (Fin 2) (ZMod N) := periodTorsionAutMatrix τ hτ N hN u
  let J : Matrix (Fin 2) (Fin 2) (ZMod N) := !![0, -(m : ZMod N); 1, 0]
  have hU : ∀ p, e.symm (u.toAdd p) = A *ᵥ e.symm p :=
    periodTorsionAutMatrix_apply τ hτ N hN u
  have hC : ∀ p, e.symm (periodTorsionCMEnd τ N m hm p) = J *ᵥ e.symm p := by
    intro p
    simpa only [e, J, AddEquiv.apply_symm_apply] using
      periodTorsionCMEnd_eq_matrix τ hτ N hN m hm (e.symm p)
  change Commute A J ↔ _
  constructor
  · intro h p
    apply e.symm.injective
    simp only [hU, hC, Matrix.mulVec_mulVec]
    exact congrArg (fun B => B *ᵥ e.symm p) h.eq
  · intro h
    change A * J = J * A
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    have hx := congrArg e.symm (h (e x))
    simpa only [hU, hC, AddEquiv.symm_apply_apply, Matrix.mulVec_mulVec] using hx

/-- Actual torsion automorphisms commuting with quadratic CM multiplication commute with each other. -/
theorem periodTorsionCMEnd_commuting_auts_commute (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) (m : ℤ) (hm : τ ^ 2 = -(m : ℂ))
    (u v : Multiplicative (AddAut (PeriodTorsion τ N)))
    (hu : ∀ p, u.toAdd (periodTorsionCMEnd τ N m hm p) =
      periodTorsionCMEnd τ N m hm (u.toAdd p))
    (hv : ∀ p, v.toAdd (periodTorsionCMEnd τ N m hm p) =
      periodTorsionCMEnd τ N m hm (v.toAdd p)) : Commute u v := by
  change u * v = v * u
  apply (periodTorsionAutMatrix_bijective τ hτ N hN).injective
  rw [map_mul, map_mul]
  apply Units.ext
  exact (QuadraticAlgebra.commute_of_commute_leftMulMatrix_omega
    (a := -(m : ZMod N)) (b := 0)
    (by simpa [QuadraticAlgebra.leftMulMatrix_eq] using
      ((periodTorsionAutMatrix_commute_iff τ hτ N hN m hm u).mpr hu))
    (by simpa [QuadraticAlgebra.leftMulMatrix_eq] using
      ((periodTorsionAutMatrix_commute_iff τ hτ N hN m hm v).mpr hv))).eq

end BakerHeegnerStark
