/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.Basic
import BakerHeegnerStark.ModularForms.CyclicSublattice.Action
import BakerHeegnerStark.ModularForms.CyclicSublattice.Primitivity

/-!
# Cyclic Sublattices and Primitive Hermite Matrices

The actual finite set `C(N)` is identified with the primitive positive
upper-triangular representatives of determinant `N`. Primitivity means
that every natural common divisor of all integral entries is one.
-/

open Matrix
open scoped MatrixGroups

noncomputable section

namespace BakerHeegnerStark

/-- The upper-triangular integral matrix belonging to an actual member of `C(N)`. -/
def cyclicSublatticeMatrix {N : ℕ} (t : {t // t ∈ cyclicSublatticeTriples N}) :
    FixedDetMatrix (Fin 2) ℤ (N : ℤ) :=
  ⟨!![(t.1.1 : ℤ), (t.1.2.1 : ℤ); 0, (t.1.2.2 : ℤ)], by
    have had : t.1.1 * t.1.2.2 = N := (Finset.mem_filter.mp t.2).2.1
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) had
    simpa [Matrix.det_fin_two] using hcast⟩

/-- Primitive Hermite representatives of determinant `N`. -/
def primitiveHermiteMatrices (N : ℕ) : Set (FixedDetMatrix (Fin 2) ℤ (N : ℤ)) :=
  {A | A ∈ FixedDetMatrices.reps (N : ℤ) ∧
    ∀ c : ℕ, (∀ i j, (c : ℤ) ∣ A.1 i j) → c = 1}

/-- The three nonnegative coordinates of an upper-triangular representative. -/
def fixedDetMatrixTriple {N : ℕ} (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) : ℕ × ℕ × ℕ :=
  ((A.1 0 0).toNat, (A.1 0 1).toNat, (A.1 1 1).toNat)

/-- A cyclic-sublattice triple gives a primitive Hermite representative. -/
theorem cyclicSublatticeMatrix_mem_primitiveHermiteMatrices {N : ℕ} (hN : 0 < N)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    cyclicSublatticeMatrix t ∈ primitiveHermiteMatrices N := by
  obtain ⟨had, hbd, hcop⟩ := (mem_cyclicSublatticeTriples hN).mp t.2
  have hd : 0 < t.1.2.2 := by omega
  have ha : 0 < t.1.1 := by
    by_contra h
    have hz : t.1.1 = 0 := by omega
    simp [hz] at had
    omega
  refine ⟨?_, ?_⟩
  · change (0 : ℤ) = 0 ∧ 0 < (t.1.1 : ℤ) ∧ 0 ≤ (t.1.2.1 : ℤ) ∧
      |(t.1.2.1 : ℤ)| < |(t.1.2.2 : ℤ)|
    refine ⟨rfl, by exact_mod_cast ha, by positivity, ?_⟩
    have hbZ : (t.1.2.1 : ℤ) < (t.1.2.2 : ℤ) := by exact_mod_cast hbd
    simpa using hbZ
  · exact (gcd_eq_one_iff_dvd_triangular_entries _ _ _).mp hcop

/-- Nonnegative Hermite coordinates reconstruct the actual integral matrix. -/
theorem triangular_fixedDetMatrixTriple {N : ℕ} (hN : 0 < N)
    {A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)} (hA : A ∈ FixedDetMatrices.reps (N : ℤ)) :
    (!![((fixedDetMatrixTriple A).1 : ℤ), ((fixedDetMatrixTriple A).2.1 : ℤ);
      0, ((fixedDetMatrixTriple A).2.2 : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) = A.1 := by
  have hd := fixedDetMatrix_reps_lowerRight_pos (show (0 : ℤ) < N by exact_mod_cast hN) hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedDetMatrixTriple, Int.toNat_of_nonneg hA.2.1.le,
      Int.toNat_of_nonneg hA.2.2.1, Int.toNat_of_nonneg hd.le, hA.1]

/-- Every primitive positive Hermite matrix gives a member of the actual `C(N)`. -/
theorem fixedDetMatrixTriple_mem_cyclicSublatticeTriples {N : ℕ} (hN : 0 < N)
    {A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)} (hA : A ∈ primitiveHermiteMatrices N) :
    fixedDetMatrixTriple A ∈ cyclicSublatticeTriples N := by
  have htri := triangular_fixedDetMatrixTriple hN hA.1
  have hd := fixedDetMatrix_reps_lowerRight_pos (show (0 : ℤ) < N by exact_mod_cast hN) hA.1
  have hdet : ((fixedDetMatrixTriple A).1 : ℤ) *
      ((fixedDetMatrixTriple A).2.2 : ℤ) = (N : ℤ) := by
    have h := A.2
    rw [← htri, Matrix.det_fin_two] at h
    simpa using h
  have hbd : A.1 0 1 < A.1 1 1 := by
    simpa only [abs_of_nonneg hA.1.2.2.1, abs_of_pos hd] using hA.1.2.2.2
  have hbdZ : ((fixedDetMatrixTriple A).2.1 : ℤ) <
      ((fixedDetMatrixTriple A).2.2 : ℤ) := by
    simpa only [fixedDetMatrixTriple, Int.toNat_of_nonneg hA.1.2.2.1,
      Int.toNat_of_nonneg hd.le] using hbd
  apply (mem_cyclicSublatticeTriples hN).mpr
  refine ⟨by exact_mod_cast hdet, by exact_mod_cast hbdZ, ?_⟩
  apply (gcd_eq_one_iff_dvd_triangular_entries _ _ _).mpr
  intro c hc
  apply hA.2 c
  intro i j
  rw [← htri]
  exact hc i j

/-- The finite cyclic-sublattice triples are exactly the primitive Hermite
representatives, with both inverse identities on the actual matrices. -/
def cyclicSublatticeMatrixEquiv {N : ℕ} (hN : 0 < N) :
    {t // t ∈ cyclicSublatticeTriples N} ≃
      {A // A ∈ primitiveHermiteMatrices N} where
  toFun t := ⟨cyclicSublatticeMatrix t, cyclicSublatticeMatrix_mem_primitiveHermiteMatrices hN t⟩
  invFun A := ⟨fixedDetMatrixTriple A.1, fixedDetMatrixTriple_mem_cyclicSublatticeTriples hN A.2⟩
  left_inv t := by
    apply Subtype.ext
    simp [fixedDetMatrixTriple, cyclicSublatticeMatrix]
  right_inv A := by
    apply Subtype.ext
    apply FixedDetMatrices.ext'
    exact triangular_fixedDetMatrixTriple hN A.2.1

/-- Right multiplication preserves the fixed determinant. -/
def fixedDetMatrixRightMul {N : ℕ} (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ))
    (g : SL(2, ℤ)) : FixedDetMatrix (Fin 2) ℤ (N : ℤ) :=
  ⟨A.1 * (g : Matrix (Fin 2) (Fin 2) ℤ), by
    rw [Matrix.det_mul, A.2, g.2, mul_one]⟩

theorem fixedDetMatrixRightMul_one {N : ℕ} (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) :
    fixedDetMatrixRightMul A 1 = A := by
  apply FixedDetMatrices.ext'
  change A.1 * (1 : Matrix (Fin 2) (Fin 2) ℤ) = A.1
  exact Matrix.mul_one _

theorem fixedDetMatrixRightMul_mul {N : ℕ} (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ))
    (g h : SL(2, ℤ)) :
    fixedDetMatrixRightMul (fixedDetMatrixRightMul A g) h = fixedDetMatrixRightMul A (g * h) := by
  apply FixedDetMatrices.ext'
  exact Matrix.mul_assoc A.1 (g : Matrix (Fin 2) (Fin 2) ℤ) (h : Matrix (Fin 2) (Fin 2) ℤ)

theorem fixedDetMatrixRightMul_smul {N : ℕ} (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ))
    (g k : SL(2, ℤ)) :
    fixedDetMatrixRightMul (k • A) g = k • fixedDetMatrixRightMul A g := by
  apply FixedDetMatrices.ext'
  exact Matrix.mul_assoc (k : Matrix (Fin 2) (Fin 2) ℤ) A.1 (g : Matrix (Fin 2) (Fin 2) ℤ)

/-- The unique representative in a positive-determinant left orbit. -/
def fixedDetMatrixRepresentative {N : ℕ} (hN : 0 < N)
    (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) : FixedDetMatrix (Fin 2) ℤ (N : ℤ) :=
  Classical.choose ((existsUnique_fixedDetMatrix_rep
    (show (0 : ℤ) < N by exact_mod_cast hN) A).exists)

theorem fixedDetMatrixRepresentative_spec {N : ℕ} (hN : 0 < N)
    (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) :
    fixedDetMatrixRepresentative hN A ∈ FixedDetMatrices.reps (N : ℤ) ∧
      ∃ g : SL(2, ℤ), g • A = fixedDetMatrixRepresentative hN A :=
  Classical.choose_spec ((existsUnique_fixedDetMatrix_rep
    (show (0 : ℤ) < N by exact_mod_cast hN) A).exists)

theorem fixedDetMatrixRepresentative_eq_self {N : ℕ} (hN : 0 < N)
    {A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)} (hA : A ∈ FixedDetMatrices.reps (N : ℤ)) :
    fixedDetMatrixRepresentative hN A = A := by
  obtain ⟨hB, g, hg⟩ := fixedDetMatrixRepresentative_spec hN A
  exact (fixedDetMatrix_reps_smul_eq
    (show (0 : ℤ) < N by exact_mod_cast hN) hA hB hg).2.symm

theorem fixedDetMatrixRepresentative_smul {N : ℕ} (hN : 0 < N)
    (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) (g : SL(2, ℤ)) :
    fixedDetMatrixRepresentative hN (g • A) = fixedDetMatrixRepresentative hN A := by
  obtain ⟨hB, k, hk⟩ := fixedDetMatrixRepresentative_spec hN (g • A)
  obtain ⟨hA, h, hh⟩ := fixedDetMatrixRepresentative_spec hN A
  have horbit : (k * g * h⁻¹) • fixedDetMatrixRepresentative hN A =
      fixedDetMatrixRepresentative hN (g • A) := by
    rw [← hh, mul_smul, inv_smul_smul, mul_smul]
    exact hk
  exact (fixedDetMatrix_reps_smul_eq
    (show (0 : ℤ) < N by exact_mod_cast hN) hA hB horbit).2.symm

/-- Normalize a right special-linear translate; its entries remain primitive. -/
def primitiveHermiteRightMul {N : ℕ} (hN : 0 < N)
    (A : {A // A ∈ primitiveHermiteMatrices N}) (g : SL(2, ℤ)) :
    {A // A ∈ primitiveHermiteMatrices N} :=
  ⟨fixedDetMatrixRepresentative hN (fixedDetMatrixRightMul A.1 g), by
    obtain ⟨hB, k, hk⟩ := fixedDetMatrixRepresentative_spec hN (fixedDetMatrixRightMul A.1 g)
    refine ⟨hB, ?_⟩
    intro c hc
    apply A.2.2 c
    apply (dvd_entries_mul_specialLinearGroup_iff A.1.1 g (c : ℤ)).mp
    apply (dvd_entries_specialLinearGroup_mul_iff
      (fixedDetMatrixRightMul A.1 g).1 k (c : ℤ)).mp
    have hmat := congrArg Subtype.val hk
    rw [FixedDetMatrices.smul_coe] at hmat
    rw [hmat]
    exact hc⟩

theorem primitiveHermiteRightMul_one {N : ℕ} (hN : 0 < N)
    (A : {A // A ∈ primitiveHermiteMatrices N}) :
    primitiveHermiteRightMul hN A 1 = A := by
  apply Subtype.ext
  change fixedDetMatrixRepresentative hN (fixedDetMatrixRightMul A.1 1) = A.1
  rw [fixedDetMatrixRightMul_one]
  exact fixedDetMatrixRepresentative_eq_self hN A.2.1

theorem primitiveHermiteRightMul_mul {N : ℕ} (hN : 0 < N)
    (A : {A // A ∈ primitiveHermiteMatrices N}) (g h : SL(2, ℤ)) :
    primitiveHermiteRightMul hN (primitiveHermiteRightMul hN A g) h =
      primitiveHermiteRightMul hN A (g * h) := by
  apply Subtype.ext
  change fixedDetMatrixRepresentative hN
    (fixedDetMatrixRightMul (fixedDetMatrixRepresentative hN (fixedDetMatrixRightMul A.1 g)) h) =
      fixedDetMatrixRepresentative hN (fixedDetMatrixRightMul A.1 (g * h))
  obtain ⟨k, hk⟩ := (fixedDetMatrixRepresentative_spec hN (fixedDetMatrixRightMul A.1 g)).2
  rw [← hk, fixedDetMatrixRightMul_smul, fixedDetMatrixRepresentative_smul,
    fixedDetMatrixRightMul_mul]

/-- Right translation is a permutation of the primitive Hermite representatives. -/
def primitiveHermiteRightPerm {N : ℕ} (hN : 0 < N) (g : SL(2, ℤ)) :
    Equiv.Perm {A // A ∈ primitiveHermiteMatrices N} where
  toFun A := primitiveHermiteRightMul hN A g
  invFun A := primitiveHermiteRightMul hN A g⁻¹
  left_inv A := by
    change primitiveHermiteRightMul hN (primitiveHermiteRightMul hN A g) g⁻¹ = A
    rw [primitiveHermiteRightMul_mul, mul_inv_cancel, primitiveHermiteRightMul_one]
  right_inv A := by
    change primitiveHermiteRightMul hN (primitiveHermiteRightMul hN A g⁻¹) g = A
    rw [primitiveHermiteRightMul_mul, inv_mul_cancel, primitiveHermiteRightMul_one]

/-- The actual finite cyclic-sublattice index set is permuted by right `SL₂(ℤ)`. -/
def cyclicSublatticeRightPerm {N : ℕ} (hN : 0 < N) (g : SL(2, ℤ)) :
    Equiv.Perm {t // t ∈ cyclicSublatticeTriples N} :=
  (cyclicSublatticeMatrixEquiv hN).trans
    ((primitiveHermiteRightPerm hN g).trans (cyclicSublatticeMatrixEquiv hN).symm)

/-- The permutation is realized by actual left special-linear equivalences
of the corresponding right-translated integer matrices. -/
theorem exists_smul_eq_cyclicSublatticeRightPerm {N : ℕ} (hN : 0 < N)
    (g : SL(2, ℤ)) (t : {t // t ∈ cyclicSublatticeTriples N}) :
    ∃ k : SL(2, ℤ), k • fixedDetMatrixRightMul (cyclicSublatticeMatrix t) g =
      cyclicSublatticeMatrix (cyclicSublatticeRightPerm hN g t) := by
  let B := primitiveHermiteRightMul hN (cyclicSublatticeMatrixEquiv hN t) g
  have heq : cyclicSublatticeMatrix ((cyclicSublatticeMatrixEquiv hN).symm B) = B.1 :=
    congrArg Subtype.val ((cyclicSublatticeMatrixEquiv hN).apply_symm_apply B)
  obtain ⟨k, hk⟩ := (fixedDetMatrixRepresentative_spec hN
    (fixedDetMatrixRightMul (cyclicSublatticeMatrix t) g)).2
  refine ⟨k, ?_⟩
  change k • fixedDetMatrixRightMul (cyclicSublatticeMatrix t) g =
    cyclicSublatticeMatrix ((cyclicSublatticeMatrixEquiv hN).symm B)
  rw [heq]
  exact hk

end BakerHeegnerStark
