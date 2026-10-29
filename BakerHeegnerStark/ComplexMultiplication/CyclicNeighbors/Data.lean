/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticCurves.CyclicIsogeny.KernelModularity
import BakerHeegnerStark.ComplexMultiplication.CyclicNeighbors.Separation
import BakerHeegnerStark.ComplexMultiplication.Residues
import BakerHeegnerStark.ComplexMultiplication.Galois
import BakerHeegnerStark.Algebra.Polynomial.Separating

/-!
# Joint cyclic-neighbor data in the actual residue coordinates

The full three/eight neighboring j-tuples have a simultaneous right modular
action, unchanged by central units. At quadratic periods in the stated range,
the actual neighboring-value separation detects their entire permutations.
A natural-number power weighting separates exactly the distinct tuples in the
finite matrix orbit. Matching an entire tuple with its genuine fixed-period
Galois conjugate forces its indexing matrix into the CM commutant, by the actual
torsion representation and projective CRT recovery. This last matching remains
an explicit hypothesis; no Weber conjugate or joint modular relation is assumed
to provide it automatically.
-/

open scoped MatrixGroups BigOperators IntermediateField
open ModularForm

noncomputable section
namespace BakerHeegnerStark

@[simp] theorem periodCoordinateGL_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : GL (Fin 2) R) :
    periodCoordinateGL (Matrix.GeneralLinearGroup.map f A) =
      Matrix.GeneralLinearGroup.map f (periodCoordinateGL A) := by
  apply Units.ext
  exact periodCoordinateMatrix_map f _

@[simp] theorem periodCoordinateGL_scalar {R : Type*} [CommRing R] (u : Rˣ) :
    periodCoordinateGL (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodCoordinateMatrix, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar]

private theorem cyclicResidueKernel_image_scalar {N : ℕ} [NeZero N] (hN : 0 < N)
    (t : {t // t ∈ cyclicSublatticeTriples N}) (u : (ZMod N)ˣ) :
    (cyclicResidueKernel N t.val).image
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec =
        cyclicResidueKernel N t.val := by
  classical
  let U := Matrix.GeneralLinearGroup.scalar (Fin 2) u
  let M := periodCoordinateMatrix ((cyclicSublatticeMatrix t).val.map (Int.castRingHom (ZMod N)))
  have hcomm : (U : Matrix (Fin 2) (Fin 2) (ZMod N)) * M =
      M * (U : Matrix (Fin 2) (Fin 2) (ZMod N)) :=
    Matrix.scalar_comm (u : ZMod N) (Commute.all _) M
  have hf : (U : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec ∘ M.mulVec =
      M.mulVec ∘ (U : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec := by
    funext v
    simp only [Function.comp_apply, Matrix.mulVec_mulVec, hcomm]
  simp only [cyclicResidueKernel_eq_image_columns hN t, Finset.image_image]
  change Finset.univ.image ((U : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec ∘ M.mulVec) =
    Finset.univ.image M.mulVec
  rw [hf, ← Finset.image_image]
  have hsur : Function.Surjective (U : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec :=
    (Matrix.GeneralLinearGroup.toLin U).toLinearEquiv.surjective
  rw [Finset.image_univ_of_surjective hsur]

/-- All unit scalars fix every actual level-three/eight kernel label. -/
theorem cyclicKernelAction_scalar {N : ℕ} (hN : N = 3 ∨ N = 8) (u : (ZMod N)ˣ) :
    cyclicKernelAction hN (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  classical
  have hpos : 0 < N := by rcases hN with rfl | rfl <;> decide
  let : NeZero N := ⟨Nat.ne_of_gt hpos⟩
  apply Equiv.ext
  intro t
  apply cyclicResidueKernel_injective hN
  change cyclicResidueKernel N
    (cyclicKernelAction hN (Matrix.GeneralLinearGroup.scalar (Fin 2) u) t).val =
      cyclicResidueKernel N t.val
  rw [← cyclicKernelAction_spec]
  exact cyclicResidueKernel_image_scalar hpos t u

private theorem cyclicNeighborLevel_dvd {N : ℕ} (hN : N = 3 ∨ N = 8) : N ∣ 24 := by
  rcases hN with rfl | rfl <;> decide

private theorem cyclicNeighborLevel_pos {N : ℕ} (hN : N = 3 ∨ N = 8) : 0 < N := by
  rcases hN with rfl | rfl <;> decide

/-- The actual right-action permutation of neighboring cyclic j-labels. -/
def cyclicNeighborPerm {N : ℕ} (hN : N = 3 ∨ N = 8)
    (A : GL (Fin 2) (ZMod 24)) : Equiv.Perm {t // t ∈ cyclicSublatticeTriples N} :=
  cyclicKernelAction hN (periodCoordinateGL (Matrix.GeneralLinearGroup.map
    (ZMod.castHom (cyclicNeighborLevel_dvd hN) (ZMod N)) A))

@[simp] theorem cyclicNeighborPerm_one {N : ℕ} (hN : N = 3 ∨ N = 8) :
    cyclicNeighborPerm hN 1 = 1 := by
  simp [cyclicNeighborPerm]

/-- Neighbor labels transform in the genuine right-action order. -/
theorem cyclicNeighborPerm_mul {N : ℕ} (hN : N = 3 ∨ N = 8)
    (A B : GL (Fin 2) (ZMod 24)) :
    cyclicNeighborPerm hN (A * B) = cyclicNeighborPerm hN B * cyclicNeighborPerm hN A := by
  simp only [cyclicNeighborPerm, map_mul, periodCoordinateGL_mul]

@[simp] theorem cyclicNeighborPerm_scalar {N : ℕ} (hN : N = 3 ∨ N = 8)
    (u : (ZMod 24)ˣ) :
    cyclicNeighborPerm hN (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  rw [cyclicNeighborPerm, Matrix.GeneralLinearGroup.map_scalar,
    periodCoordinateGL_scalar, cyclicKernelAction_scalar]

/-- Integral modular substitution is the already proved Hermite right action. -/
theorem cyclicNeighborPerm_mapGL {N : ℕ} (hN : N = 3 ∨ N = 8) (g : SL(2, ℤ)) :
    cyclicNeighborPerm hN (Matrix.SpecialLinearGroup.mapGL (ZMod 24) g) =
      cyclicSublatticeRightPerm (cyclicNeighborLevel_pos hN) g := by
  have hred : Matrix.GeneralLinearGroup.map
      (ZMod.castHom (cyclicNeighborLevel_dvd hN) (ZMod N))
      (Matrix.SpecialLinearGroup.mapGL (ZMod 24) g) =
      Matrix.SpecialLinearGroup.mapGL (ZMod N) g := by
    apply Units.ext
    ext i j
    change (ZMod.castHom (cyclicNeighborLevel_dvd hN) (ZMod N))
      (algebraMap ℤ (ZMod 24) (g i j)) = algebraMap ℤ (ZMod N) (g i j)
    have hf : (ZMod.castHom (cyclicNeighborLevel_dvd hN) (ZMod N)).comp
        (algebraMap ℤ (ZMod 24)) = algebraMap ℤ (ZMod N) := Subsingleton.elim _ _
    exact congrArg (fun f : ℤ →+* ZMod N => f (g i j)) hf
  rw [cyclicNeighborPerm, hred]
  exact Equiv.ext (cyclicKernelAction_periodCoordinate_mapGL hN g)

/-- The sixteen actual neighboring j-data coordinates, with their finite labels. -/
abbrev cyclicNeighborIndex :=
  {t // t ∈ cyclicSublatticeTriples 3} ⊕ {t // t ∈ cyclicSublatticeTriples 8}

/-- Actual analytic neighboring values indexed by a level-twenty-four matrix. -/
def cyclicNeighborData (A : GL (Fin 2) (ZMod 24)) (τ : UpperHalfPlane) :
    cyclicNeighborIndex → ℂ
  | .inl t => jInvariant (cyclicSublatticePoint (cyclicNeighborPerm (Or.inl rfl) A t).val τ)
  | .inr t => jInvariant (cyclicSublatticePoint (cyclicNeighborPerm (Or.inr rfl) A t).val τ)

/-- A common central scalar does not change any of the actual neighboring values. -/
theorem cyclicNeighborData_mul_scalar (A : GL (Fin 2) (ZMod 24)) (u : (ZMod 24)ˣ)
    (τ : UpperHalfPlane) :
    cyclicNeighborData (A * Matrix.GeneralLinearGroup.scalar (Fin 2) u) τ =
      cyclicNeighborData A τ := by
  funext i
  rcases i with t | t <;>
    simp only [cyclicNeighborData, cyclicNeighborPerm_mul, cyclicNeighborPerm_scalar,
      one_mul]

/-- All neighboring values obey simultaneous modular right substitution. -/
theorem cyclicNeighborData_smul (A : GL (Fin 2) (ZMod 24)) (g : SL(2, ℤ))
    (τ : UpperHalfPlane) :
    cyclicNeighborData A (g • τ) =
      cyclicNeighborData (A * Matrix.SpecialLinearGroup.mapGL (ZMod 24) g) τ := by
  funext i
  rcases i with t | t
  · change jInvariant (cyclicSublatticePoint (cyclicNeighborPerm (Or.inl rfl) A t).val (g • τ)) =
      jInvariant (cyclicSublatticePoint
        (cyclicNeighborPerm (Or.inl rfl) (A * Matrix.SpecialLinearGroup.mapGL (ZMod 24) g) t).val τ)
    rw [cyclicNeighborPerm_mul, Equiv.Perm.mul_apply, cyclicNeighborPerm_mapGL]
    exact (jInvariant_cyclicSublatticeRightPerm (by decide : 0 < 3) g
      (cyclicNeighborPerm (Or.inl rfl) A t) τ).symm
  · change jInvariant (cyclicSublatticePoint (cyclicNeighborPerm (Or.inr rfl) A t).val (g • τ)) =
      jInvariant (cyclicSublatticePoint
        (cyclicNeighborPerm (Or.inr rfl) (A * Matrix.SpecialLinearGroup.mapGL (ZMod 24) g) t).val τ)
    rw [cyclicNeighborPerm_mul, Equiv.Perm.mul_apply, cyclicNeighborPerm_mapGL]
    exact (jInvariant_cyclicSublatticeRightPerm (by decide : 0 < 8) g
      (cyclicNeighborPerm (Or.inr rfl) A t) τ).symm

/-- At the specified CM points, equality of actual data detects both full
permutations, not only a single chosen neighboring value. -/
theorem cyclicNeighborData_eq_iff_permutations (τ : UpperHalfPlane) (m : ℕ)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (hm : 9 < m) (hm8 : m % 8 = 3)
    (A B : GL (Fin 2) (ZMod 24)) :
    cyclicNeighborData A τ = cyclicNeighborData B τ ↔
      cyclicNeighborPerm (Or.inl rfl) A = cyclicNeighborPerm (Or.inl rfl) B ∧
      cyclicNeighborPerm (Or.inr rfl) A = cyclicNeighborPerm (Or.inr rfl) B := by
  constructor
  · intro he
    constructor
    · apply Equiv.ext
      intro t
      apply jInvariant_cyclicSublatticePoint_injective_three τ m hτ hm
      exact congrFun he (.inl t)
    · apply Equiv.ext
      intro t
      apply jInvariant_cyclicSublatticePoint_injective_eight τ m hτ (by omega) hm8
      exact congrFun he (.inr t)
  · rintro ⟨h3, h8⟩
    funext i
    rcases i with t | t <;> simp only [cyclicNeighborData, h3, h8]

/-- The rational-power weighting of all the actual neighboring coordinates. -/
def cyclicNeighborWeighted (a : ℕ) (A : GL (Fin 2) (ZMod 24)) (τ : UpperHalfPlane) : ℂ :=
  ∑ k : Fin (Fintype.card cyclicNeighborIndex),
    cyclicNeighborData A τ ((Fintype.equivFin cyclicNeighborIndex).symm k) * (a : ℂ) ^ k.val

/-- At any fixed point, one natural weight distinguishes precisely the distinct
full neighboring-data tuples in the finite matrix orbit. -/
theorem exists_nat_cyclicNeighborWeighted_eq_iff (τ : UpperHalfPlane) :
    ∃ a : ℕ, ∀ A B : GL (Fin 2) (ZMod 24),
      cyclicNeighborWeighted a A τ = cyclicNeighborWeighted a B τ ↔
        cyclicNeighborData A τ = cyclicNeighborData B τ := by
  classical
  obtain ⟨a, ha⟩ := exists_nat_weighted_sum_eq_iff
    (Fintype.card cyclicNeighborIndex) (fun A k =>
      cyclicNeighborData A τ ((Fintype.equivFin cyclicNeighborIndex).symm k))
  refine ⟨a, fun A B => ?_⟩
  rw [show cyclicNeighborWeighted a A τ = cyclicNeighborWeighted a B τ ↔
      (fun k => cyclicNeighborData A τ ((Fintype.equivFin cyclicNeighborIndex).symm k)) =
        (fun k => cyclicNeighborData B τ ((Fintype.equivFin cyclicNeighborIndex).symm k)) from ha A B]
  constructor
  · intro he
    funext i
    simpa only [Equiv.symm_apply_apply] using congrFun he ((Fintype.equivFin cyclicNeighborIndex) i)
  · intro he
    rw [he]

/-- The fixed natural weighting respects simultaneous modular right substitution. -/
theorem cyclicNeighborWeighted_smul (a : ℕ) (A : GL (Fin 2) (ZMod 24))
    (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    cyclicNeighborWeighted a A (g • τ) =
      cyclicNeighborWeighted a (A * Matrix.SpecialLinearGroup.mapGL (ZMod 24) g) τ := by
  simp only [cyclicNeighborWeighted, cyclicNeighborData_smul]

private theorem cyclicNeighborPerm_eq_galois_of_values [DecidableEq ℂ] {N : ℕ}
    (hN : N = 3 ∨ N = 8) (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮jInvariant τ⟯] ℂ) (A : GL (Fin 2) (ZMod 24))
    (hinj : Function.Injective (fun t : {t // t ∈ cyclicSublatticeTriples N} =>
      jInvariant (cyclicSublatticePoint t.val τ)))
    (hv : ∀ t : {t // t ∈ cyclicSublatticeTriples N},
      jInvariant (cyclicSublatticePoint (cyclicNeighborPerm hN A t).val τ) =
        σ (jInvariant (cyclicSublatticePoint t.val τ))) :
    cyclicNeighborPerm hN A = cyclicKernelPerm hN
      (jInvariantCurveTorsionGaloisMatrix τ N (cyclicNeighborLevel_pos hN) σ) := by
  apply Equiv.ext
  intro t
  apply hinj
  have hact (B : GL (Fin 2) (ZMod N)) : cyclicKernelAction hN B = cyclicKernelPerm hN B := rfl
  have hg := jInvariant_cyclicSublatticePoint_galois hN τ σ t
  rw [cyclicKernelGaloisAction_apply, hact] at hg
  exact (hv t).trans hg

/-- Matching every actual neighboring conjugate forces the indexing matrix to
centralize CM. The matching hypothesis is explicit: a joint modular relation
still has to supply it for a Weber conjugate. -/
theorem cyclicNeighborData_galois_eq_imp_commute_CM [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (hm : 9 < m) (hm8 : m % 8 = 3)
    (σ : ℂ ≃ₐ[ℚ⟮jInvariant τ⟯] ℂ) (hσ : σ (τ : ℂ) = (τ : ℂ))
    (A : GL (Fin 2) (ZMod 24))
    (hdata : cyclicNeighborData A τ = fun i => σ (cyclicNeighborData 1 τ i)) :
    Commute (A : Matrix (Fin 2) (Fin 2) (ZMod 24)) !![0, -(m : ZMod 24); 1, 0] := by
  let π3 := ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3)
  let π8 := ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)
  let A3 := periodCoordinateGL (Matrix.GeneralLinearGroup.map π3 A)
  let A8 := periodCoordinateGL (Matrix.GeneralLinearGroup.map π8 A)
  let G3 := jInvariantCurveTorsionGaloisMatrix τ 3 (by decide) σ
  let G8 := jInvariantCurveTorsionGaloisMatrix τ 8 (by decide) σ
  have hp3 : cyclicKernelPerm (Or.inl rfl) A3 = cyclicKernelPerm (Or.inl rfl) G3 := by
    apply cyclicNeighborPerm_eq_galois_of_values (Or.inl rfl) τ σ A
      (jInvariant_cyclicSublatticePoint_injective_three τ m hτ hm)
    intro t
    simpa [cyclicNeighborData, cyclicNeighborPerm_one] using congrFun hdata (.inl t)
  have hp8 : cyclicKernelPerm (Or.inr rfl) A8 = cyclicKernelPerm (Or.inr rfl) G8 := by
    apply cyclicNeighborPerm_eq_galois_of_values (Or.inr rfl) τ σ A
      (jInvariant_cyclicSublatticePoint_injective_eight τ m hτ (by omega) hm8)
    intro t
    simpa [cyclicNeighborData, cyclicNeighborPerm_one] using congrFun hdata (.inr t)
  obtain ⟨u3, hu3⟩ := cyclicKernelPerm_eq_imp_unit_smul (Or.inl rfl) A3 G3 hp3
  obtain ⟨u8, hu8⟩ := cyclicKernelPerm_eq_imp_unit_smul (Or.inr rfl) A8 G8 hp8
  apply (periodCoordinateGL_commute_CM_iff (m : ZMod 24) A).mp
  apply commute_CM_mod_twenty_four_of_projective_reductions (m : ZMod 24)
    (periodCoordinateGL A : Matrix (Fin 2) (Fin 2) (ZMod 24)) G3 G8 u3 u8
  · simpa only [map_natCast] using
      jInvariantCurveTorsionGaloisMatrix_commute_CM τ m (by omega) hτ σ hσ 3 (by decide)
  · simpa only [map_natCast] using
      jInvariantCurveTorsionGaloisMatrix_commute_CM τ m (by omega) hτ σ hσ 8 (by decide)
  · exact (periodCoordinateMatrix_map π3 (A : Matrix (Fin 2) (Fin 2) (ZMod 24))).symm.trans hu3
  · exact (periodCoordinateMatrix_map π8 (A : Matrix (Fin 2) (Fin 2) (ZMod 24))).symm.trans hu8

end BakerHeegnerStark
