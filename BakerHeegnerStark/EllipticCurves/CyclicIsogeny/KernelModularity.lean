/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticCurves.CyclicIsogeny.KernelAction
import BakerHeegnerStark.ModularForms.ModularPolynomial.Modularity
import QNFMathlib.Algebra.QuadraticAlgebra.Matrix

/-!
# Modular right action in the prescribed cyclic-kernel coordinates

The ordered periods use column coordinates `(1, τ)`. An integral fractional-linear
matrix therefore acts on kernel labels by the diagonal-swapped anti-involution,
not by its original matrix. We identify the full residue kernel with the column
image of this matrix at every positive level, and then connect the actual
level-three and level-eight kernel action to the Hermite right permutation and
its transformed j-values. The anti-involution preserves the CM commutant.
-/

open scoped MatrixGroups

namespace BakerHeegnerStark

/-- The ordered-period coordinate matrix: swap the diagonal, not the off-diagonal. -/
def periodCoordinateMatrix {R : Type*} (A : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R := !![A 1 1, A 0 1; A 1 0, A 0 0]

@[simp] theorem periodCoordinateMatrix_one {R : Type*} [CommRing R] :
    periodCoordinateMatrix (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [periodCoordinateMatrix]

/-- Ordered-period coordinates reverse multiplication. -/
theorem periodCoordinateMatrix_mul {R : Type*} [CommRing R]
    (A B : Matrix (Fin 2) (Fin 2) R) :
    periodCoordinateMatrix (A * B) = periodCoordinateMatrix B * periodCoordinateMatrix A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodCoordinateMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] theorem periodCoordinateMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) :
    periodCoordinateMatrix (A.map f) = (periodCoordinateMatrix A).map f := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem periodCoordinateMatrix_involutive {R : Type*}
    (A : Matrix (Fin 2) (Fin 2) R) :
    periodCoordinateMatrix (periodCoordinateMatrix A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The same anti-involution on actual unit matrices, with its supplied inverse. -/
def periodCoordinateGL {R : Type*} [CommRing R] (A : GL (Fin 2) R) : GL (Fin 2) R :=
  ⟨periodCoordinateMatrix (A : Matrix (Fin 2) (Fin 2) R),
    periodCoordinateMatrix ((A⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R), by
      rw [← periodCoordinateMatrix_mul]
      have h := congrArg (fun B : GL (Fin 2) R => (B : Matrix (Fin 2) (Fin 2) R))
        (inv_mul_cancel A)
      change ((A⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) *
        (A : Matrix (Fin 2) (Fin 2) R) = 1 at h
      rw [h, periodCoordinateMatrix_one], by
      rw [← periodCoordinateMatrix_mul]
      have h := congrArg (fun B : GL (Fin 2) R => (B : Matrix (Fin 2) (Fin 2) R))
        (mul_inv_cancel A)
      change (A : Matrix (Fin 2) (Fin 2) R) *
        ((A⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = 1 at h
      rw [h, periodCoordinateMatrix_one]⟩

@[simp] theorem periodCoordinateGL_coe {R : Type*} [CommRing R] (A : GL (Fin 2) R) :
    (periodCoordinateGL A : Matrix (Fin 2) (Fin 2) R) =
      periodCoordinateMatrix (A : Matrix (Fin 2) (Fin 2) R) := rfl

@[simp] theorem periodCoordinateGL_one {R : Type*} [CommRing R] :
    periodCoordinateGL (1 : GL (Fin 2) R) = 1 := by
  apply Units.ext
  exact periodCoordinateMatrix_one

theorem periodCoordinateGL_mul {R : Type*} [CommRing R] (A B : GL (Fin 2) R) :
    periodCoordinateGL (A * B) = periodCoordinateGL B * periodCoordinateGL A := by
  apply Units.ext
  exact periodCoordinateMatrix_mul _ _

@[simp] theorem periodCoordinateGL_involutive {R : Type*} [CommRing R]
    (A : GL (Fin 2) R) : periodCoordinateGL (periodCoordinateGL A) = A := by
  apply Units.ext
  exact periodCoordinateMatrix_involutive _

/-- The coordinate anti-involution preserves the actual CM commutant. -/
theorem periodCoordinateGL_commute_CM_iff {R : Type*} [CommRing R]
    (m : R) (A : GL (Fin 2) R) :
    Commute (periodCoordinateGL A : Matrix (Fin 2) (Fin 2) R) !![0, -m; 1, 0] ↔
      Commute (A : Matrix (Fin 2) (Fin 2) R) !![0, -m; 1, 0] := by
  have hgen :
      Algebra.leftMulMatrix (QuadraticAlgebra.basis (-m) 0) QuadraticAlgebra.omega =
        !![0, -m; 1, 0] := by
    simp [QuadraticAlgebra.leftMulMatrix_eq]
  simp only [← hgen, QuadraticAlgebra.commute_leftMulMatrix_omega_iff, zero_mul, add_zero]
  change (A 0 1 = -m * A 1 0 ∧ A 0 0 = A 1 1) ↔
    (A 0 1 = -m * A 1 0 ∧ A 1 1 = A 0 0)
  exact and_congr Iff.rfl eq_comm

/-- The complete cyclic residue kernel is the column image of its Hermite
matrix in the prescribed ordered-period coordinates, for every positive level. -/
theorem cyclicResidueKernel_eq_image_columns {N : ℕ} [NeZero N] (hN : 0 < N)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    cyclicResidueKernel N t.val = Finset.univ.image
      (periodCoordinateMatrix ((cyclicSublatticeMatrix t).val.map
        (Int.castRingHom (ZMod N)))).mulVec := by
  classical
  let M := periodCoordinateMatrix ((cyclicSublatticeMatrix t).val.map (Int.castRingHom (ZMod N)))
  have hM (r s : ℕ) : M.mulVec ![(r : ZMod N), (s : ZMod N)] =
      ![((t.val.2.2 * r + t.val.2.1 * s : ℕ) : ZMod N), ((t.val.1 * s : ℕ) : ZMod N)] := by
    ext i
    fin_cases i <;>
      simp [M, periodCoordinateMatrix, cyclicSublatticeMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, Nat.cast_add, Nat.cast_mul]
  ext w
  constructor
  · intro hw
    obtain ⟨⟨r, s⟩, _, he⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨![(r : ZMod N), (s : ZMod N)],
      Finset.mem_univ _, (hM r s).trans he⟩
  · intro hw
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
    have hv : v = ![((v 0).val : ZMod N), ((v 1).val : ZMod N)] := by
      ext i
      fin_cases i <;> simp
    have hMv : M.mulVec v =
        ![((t.val.2.2 * (v 0).val + t.val.2.1 * (v 1).val : ℕ) : ZMod N),
          ((t.val.1 * (v 1).val : ℕ) : ZMod N)] := by
      calc
        M.mulVec v = M.mulVec ![((v 0).val : ZMod N), ((v 1).val : ZMod N)] := congrArg M.mulVec hv
        _ = _ := hM _ _
    let e := jInvariantCurveTorsionCoordinatesEquiv UpperHalfPlane.I N hN
    have hp : (e (M.mulVec v) : ((jInvariantCurve UpperHalfPlane.I).baseChange ℂ).toAffine.Point) =
        jInvariantPeriodPoint UpperHalfPlane.I
          (cyclicIsogenyRepresentative t.val UpperHalfPlane.I (v 0).val (v 1).val) := by
      rw [hMv]
      exact cyclicIsogenyRepresentative_coordinates hN t.property UpperHalfPlane.I _ _
    have hmem : (e (M.mulVec v) : ((jInvariantCurve UpperHalfPlane.I).baseChange ℂ).toAffine.Point) ∈
        cyclicIsogenyKernel t.val UpperHalfPlane.I := by
      rw [hp]
      apply (cyclicIsogeny_eq_zero_iff hN t.property UpperHalfPlane.I _).mp
      rw [cyclicIsogeny_periodPoint, jInvariantPeriodPoint_eq_zero_iff,
        standardPeriodPair_lattice_eq_periodModule, cyclicIsogeny_mul_mem_iff hN t.property]
      exact (mem_cyclicIsogenyPeriodPair_iff hN t.property UpperHalfPlane.I _).mpr
        ⟨(v 0).val, (v 1).val, rfl⟩
    rw [cyclicIsogenyKernel_eq_coordinates_image hN t.property UpperHalfPlane.I] at hmem
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hmem
    have hue : u = M.mulVec v := e.injective (Subtype.ext he)
    exact hue ▸ hu

private theorem image_columns_mul_unit {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (M : Matrix (Fin 2) (Fin 2) R) (K : GL (Fin 2) R) :
    Finset.univ.image (M * (K : Matrix (Fin 2) (Fin 2) R)).mulVec =
      Finset.univ.image M.mulVec := by
  classical
  have hm : (M * (K : Matrix (Fin 2) (Fin 2) R)).mulVec =
      M.mulVec ∘ (K : Matrix (Fin 2) (Fin 2) R).mulVec := by
    funext v
    exact (Matrix.mulVec_mulVec v _ _).symm
  rw [hm, ← Finset.image_image]
  have hsur : Function.Surjective (K : Matrix (Fin 2) (Fin 2) R).mulVec :=
    (Matrix.GeneralLinearGroup.toLin K).toLinearEquiv.surjective
  rw [Finset.image_univ_of_surjective hsur]

private theorem kernelModularLevel_pos {N : ℕ} (hN : N = 3 ∨ N = 8) : 0 < N := by
  rcases hN with rfl | rfl <;> decide

/-- The actual right Hermite permutation acts on period coordinates by the
anti-involution of the reduced modular matrix, not by the original matrix. -/
theorem cyclicKernelAction_periodCoordinate_mapGL {N : ℕ} (hN : N = 3 ∨ N = 8)
    (g : SL(2, ℤ)) (t : {t // t ∈ cyclicSublatticeTriples N}) :
    cyclicKernelAction hN (periodCoordinateGL (Matrix.SpecialLinearGroup.mapGL (ZMod N) g)) t =
      cyclicSublatticeRightPerm (kernelModularLevel_pos hN) g t := by
  classical
  let hpos := kernelModularLevel_pos hN
  let : NeZero N := ⟨Nat.ne_of_gt hpos⟩
  obtain ⟨k, hk⟩ := exists_smul_eq_cyclicSublatticeRightPerm hpos g t
  have hk' : (k : Matrix (Fin 2) (Fin 2) ℤ) *
      ((cyclicSublatticeMatrix t).val * (g : Matrix (Fin 2) (Fin 2) ℤ)) =
      (cyclicSublatticeMatrix (cyclicSublatticeRightPerm hpos g t)).val := by
    exact congrArg Subtype.val hk
  have hrel :
      (periodCoordinateGL (Matrix.SpecialLinearGroup.mapGL (ZMod N) g) :
        Matrix (Fin 2) (Fin 2) (ZMod N)) *
        periodCoordinateMatrix ((cyclicSublatticeMatrix t).val.map (Int.castRingHom (ZMod N))) *
        (periodCoordinateGL (Matrix.SpecialLinearGroup.mapGL (ZMod N) k) :
          Matrix (Fin 2) (Fin 2) (ZMod N)) =
      periodCoordinateMatrix
        ((cyclicSublatticeMatrix (cyclicSublatticeRightPerm hpos g t)).val.map
          (Int.castRingHom (ZMod N))) := by
    have hd := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ =>
      periodCoordinateMatrix (A.map (Int.castRingHom (ZMod N)))) hk'
    change periodCoordinateMatrix ((g : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ (ZMod N))) *
        periodCoordinateMatrix ((cyclicSublatticeMatrix t).val.map (Int.castRingHom (ZMod N))) *
        periodCoordinateMatrix ((k : Matrix (Fin 2) (Fin 2) ℤ).map
          (algebraMap ℤ (ZMod N))) = _
    have hi : algebraMap ℤ (ZMod N) = Int.castRingHom (ZMod N) := Subsingleton.elim _ _
    rw [hi]
    simpa only [Matrix.map_mul, periodCoordinateMatrix_mul] using hd
  apply cyclicResidueKernel_injective hN
  change cyclicResidueKernel N
      (cyclicKernelAction hN (periodCoordinateGL (Matrix.SpecialLinearGroup.mapGL (ZMod N) g)) t).val =
    cyclicResidueKernel N (cyclicSublatticeRightPerm hpos g t).val
  rw [← cyclicKernelAction_spec, cyclicResidueKernel_eq_image_columns hpos t,
    cyclicResidueKernel_eq_image_columns hpos (cyclicSublatticeRightPerm hpos g t),
    Finset.image_image, ← hrel, image_columns_mul_unit]
  congr 1
  funext v
  exact Matrix.mulVec_mulVec v _ _

/-- The kernel-coordinate action gives the actual transformed cyclic j-value. -/
theorem jInvariant_cyclicKernelAction_periodCoordinate_mapGL {N : ℕ} (hN : N = 3 ∨ N = 8)
    (g : SL(2, ℤ)) (t : {t // t ∈ cyclicSublatticeTriples N}) (τ : UpperHalfPlane) :
    ModularForm.jInvariant
      (cyclicSublatticePoint
        (cyclicKernelAction hN (periodCoordinateGL (Matrix.SpecialLinearGroup.mapGL (ZMod N) g)) t).val τ) =
      ModularForm.jInvariant (cyclicSublatticePoint t.val (g • τ)) := by
  rw [cyclicKernelAction_periodCoordinate_mapGL]
  exact jInvariant_cyclicSublatticeRightPerm _ _ _ _

end BakerHeegnerStark
