/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.CyclicSublattice.Matrices
import BakerHeegnerStark.ModularForms.CyclicSublattice.Mobius
import BakerHeegnerStark.ModularForms.ModularPolynomial.Complex
import BakerHeegnerStark.ComplexMultiplication.JInvariant.Separation
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.FixedMatrices
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.FixedMatrixDiscriminant
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.PrimitiveFixedMatrices

/-!
# Diagonal Modular Roots and Primitive Fixed Matrices

An actual diagonal root of the cyclic-sublattice polynomial at positive level
is equivalent to an actual primitive integral matrix of that determinant fixing
the upper-half-plane parameter. The proof uses the existing primitive Hermite
representatives and separation by the analytic j-invariant. Monicity gives the
same characterization by positive root multiplicity, without requiring distinct
roots or excluding square levels, including level one.
-/

open Matrix UpperHalfPlane ModularForm Polynomial
open scoped MatrixGroups

noncomputable section

namespace BakerHeegnerStark

private theorem fixedDetMatrix_real_det_pos {N : ℕ} (hN : 0 < N)
    (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) :
    0 < (A.1.map (Int.castRingHom ℝ)).det := by
  have hdet : (A.1.map (Int.castRingHom ℝ)).det = (A.1.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det A.1).symm
  rw [hdet, A.2]
  exact_mod_cast hN

/-- The real general-linear matrix attached to a positive fixed-determinant
integral matrix. -/
def positiveFixedDetMatrixGL {N : ℕ} (hN : 0 < N)
    (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero (A.1.map (Int.castRingHom ℝ))
    (ne_of_gt (fixedDetMatrix_real_det_pos hN A))

/-- The realized real matrix has positive determinant. -/
theorem positiveFixedDetMatrixGL_det_pos {N : ℕ} (hN : 0 < N)
    (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) :
    0 < (positiveFixedDetMatrixGL hN A).det.val :=
  fixedDetMatrix_real_det_pos hN A

/-- Left integral equivalence is actual multiplication of the realized matrices. -/
theorem positiveFixedDetMatrixGL_smul {N : ℕ} (hN : 0 < N)
    (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) (g : SL(2, ℤ)) :
    positiveFixedDetMatrixGL hN (g • A) =
      SpecialLinearGroup.mapGL ℝ g * positiveFixedDetMatrixGL hN A := by
  apply Units.ext
  change ((g : Matrix (Fin 2) (Fin 2) ℤ) * A.1).map (Int.castRingHom ℝ) =
    (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) *
      A.1.map (Int.castRingHom ℝ)
  rw [← Matrix.map_mul]

private theorem positiveFixedDetMatrixGL_coe_smul {N : ℕ} (hN : 0 < N)
    (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) (τ : UpperHalfPlane) :
    ((positiveFixedDetMatrixGL hN A • τ : UpperHalfPlane) : ℂ) =
      ((A.1 0 0 : ℂ) * (τ : ℂ) + A.1 0 1) /
        ((A.1 1 0 : ℂ) * (τ : ℂ) + A.1 1 1) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (positiveFixedDetMatrixGL_det_pos hN A)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, positiveFixedDetMatrixGL]

/-- Being fixed by the actual real matrix is the raw complex fixed-point equation. -/
theorem positiveFixedDetMatrixGL_fixed_iff {N : ℕ} (hN : 0 < N)
    (A : FixedDetMatrix (Fin 2) ℤ (N : ℤ)) (τ : UpperHalfPlane) :
    positiveFixedDetMatrixGL hN A • τ = τ ↔
      (A.1 0 0 : ℂ) * (τ : ℂ) + A.1 0 1 =
        (τ : ℂ) * ((A.1 1 0 : ℂ) * (τ : ℂ) + A.1 1 1) := by
  have hden : (A.1 1 0 : ℂ) * (τ : ℂ) + A.1 1 1 ≠ 0 := by
    simpa [UpperHalfPlane.denom, positiveFixedDetMatrixGL] using
      UpperHalfPlane.denom_ne_zero (positiveFixedDetMatrixGL hN A) τ
  constructor
  · intro h
    have hc := congrArg (fun z : UpperHalfPlane => (z : ℂ)) h
    rw [positiveFixedDetMatrixGL_coe_smul] at hc
    exact (div_eq_iff hden).mp hc
  · intro h
    apply UpperHalfPlane.ext
    rw [positiveFixedDetMatrixGL_coe_smul]
    exact (div_eq_iff hden).mpr h

/-- A Hermite representative acts by its actual cyclic-sublattice point. -/
theorem positiveFixedDetMatrixGL_cyclicSublatticeMatrix_smul
    {N : ℕ} (hN : 0 < N) (t : {t // t ∈ cyclicSublatticeTriples N})
    (τ : UpperHalfPlane) :
    positiveFixedDetMatrixGL hN (cyclicSublatticeMatrix t) • τ =
      cyclicSublatticePoint t.1 τ := by
  obtain ⟨had, hbd, _⟩ := (mem_cyclicSublatticeTriples hN).mp t.2
  have hd : 0 < t.1.2.2 := by omega
  have ha : 0 < t.1.1 := by
    by_contra h
    have hz : t.1.1 = 0 := by omega
    simp [hz] at had
    omega
  apply UpperHalfPlane.ext
  rw [positiveFixedDetMatrixGL_coe_smul, cyclicSublatticePoint_coe ha hd]
  simp [cyclicSublatticeMatrix]

private theorem isRoot_cyclicSublatticePolynomial_iff_exists_triple
    (N : ℕ) (τ : UpperHalfPlane) :
    (cyclicSublatticePolynomial N τ).IsRoot (jInvariant τ) ↔
      ∃ t ∈ cyclicSublatticeTriples N,
        jInvariant τ = jInvariant (cyclicSublatticePoint t τ) := by
  classical
  simp only [cyclicSublatticePolynomial, IsRoot, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_eq_zero_iff, sub_eq_zero]

/-- A diagonal root of the actual cyclic-sublattice polynomial is exactly a
primitive integral matrix of determinant `N` fixing the actual parameter. This
includes level one and allows repeated roots and square levels. -/
theorem isRoot_cyclicSublatticePolynomial_iff_exists_primitive_fixed_matrix
    {N : ℕ} (hN : 0 < N) (τ : UpperHalfPlane) :
    (cyclicSublatticePolynomial N τ).IsRoot (jInvariant τ) ↔
      ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
        A.det = (N : ℤ) ∧
        (∀ d : ℕ, (∀ i j, (d : ℤ) ∣ A i j) → d = 1) ∧
        (A 0 0 : ℂ) * (τ : ℂ) + A 0 1 =
          (τ : ℂ) * ((A 1 0 : ℂ) * (τ : ℂ) + A 1 1) := by
  classical
  constructor
  · intro h
    obtain ⟨t, ht, hj⟩ :=
      (isRoot_cyclicSublatticePolynomial_iff_exists_triple N τ).mp h
    obtain ⟨g, hg⟩ :=
      (jInvariant_eq_iff_modularOrbit τ (cyclicSublatticePoint t τ)).mp hj
    let B := cyclicSublatticeMatrix ⟨t, ht⟩
    have hB : B ∈ primitiveHermiteMatrices N :=
      cyclicSublatticeMatrix_mem_primitiveHermiteMatrices hN ⟨t, ht⟩
    refine ⟨(g • B).1, (g • B).2, ?_, ?_⟩
    · intro d hd
      apply hB.2 d
      exact (dvd_entries_specialLinearGroup_mul_iff B.1 g (d : ℤ)).mp hd
    · apply (positiveFixedDetMatrixGL_fixed_iff hN (g • B) τ).mp
      rw [positiveFixedDetMatrixGL_smul, mul_smul]
      change g • (positiveFixedDetMatrixGL hN (cyclicSublatticeMatrix ⟨t, ht⟩) • τ) = τ
      rw [positiveFixedDetMatrixGL_cyclicSublatticeMatrix_smul]
      exact hg
  · rintro ⟨A, hdet, hprimitive, hfix⟩
    let M : FixedDetMatrix (Fin 2) ℤ (N : ℤ) := ⟨A, hdet⟩
    let R := fixedDetMatrixRepresentative hN M
    obtain ⟨hR, k, hk⟩ := fixedDetMatrixRepresentative_spec hN M
    have hRprimitive : R ∈ primitiveHermiteMatrices N := by
      refine ⟨hR, ?_⟩
      intro d hd
      apply hprimitive d
      apply (dvd_entries_specialLinearGroup_mul_iff A k (d : ℤ)).mp
      have hmat := congrArg Subtype.val hk
      rw [FixedDetMatrices.smul_coe] at hmat
      change (k : Matrix (Fin 2) (Fin 2) ℤ) * A = R.1 at hmat
      rw [hmat]
      exact hd
    let B : {B // B ∈ primitiveHermiteMatrices N} := ⟨R, hRprimitive⟩
    let t := (cyclicSublatticeMatrixEquiv hN).symm B
    have ht : cyclicSublatticeMatrix t = R :=
      congrArg Subtype.val ((cyclicSublatticeMatrixEquiv hN).apply_symm_apply B)
    have hfixed : positiveFixedDetMatrixGL hN M • τ = τ :=
      (positiveFixedDetMatrixGL_fixed_iff hN M τ).mpr hfix
    have hact : positiveFixedDetMatrixGL hN R • τ = k • τ := by
      change positiveFixedDetMatrixGL hN (fixedDetMatrixRepresentative hN M) • τ = k • τ
      rw [← hk, positiveFixedDetMatrixGL_smul, mul_smul, hfixed]
      rfl
    have hpoint : cyclicSublatticePoint t.1 τ = k • τ := by
      rw [← positiveFixedDetMatrixGL_cyclicSublatticeMatrix_smul hN t τ, ht]
      exact hact
    apply (isRoot_cyclicSublatticePolynomial_iff_exists_triple N τ).mpr
    refine ⟨t.1, t.2, ?_⟩
    rw [hpoint, ModularForm.jInvariant_smul]

/-- Positive diagonal root multiplicity has the same primitive fixed-matrix
characterization. Nonzeroness follows from monicity of the actual root product,
not from any distinctness of its roots. -/
theorem rootMultiplicity_cyclicSublatticePolynomial_pos_iff_exists_primitive_fixed_matrix
    {N : ℕ} (hN : 0 < N) (τ : UpperHalfPlane) :
    0 < rootMultiplicity (jInvariant τ) (cyclicSublatticePolynomial N τ) ↔
      ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
        A.det = (N : ℤ) ∧
        (∀ d : ℕ, (∀ i j, (d : ℤ) ∣ A i j) → d = 1) ∧
        (A 0 0 : ℂ) * (τ : ℂ) + A 0 1 =
          (τ : ℂ) * ((A 1 0 : ℂ) * (τ : ℂ) + A 1 1) := by
  exact (Polynomial.rootMultiplicity_pos
    (monic_cyclicSublatticePolynomial N τ).ne_zero).trans
      (isRoot_cyclicSublatticePolynomial_iff_exists_primitive_fixed_matrix hN τ)

/-- For a monic quadratic parameter, a diagonal modular root is exactly a
primitive representation by its quadratic norm. Level one is included. -/
theorem rootMultiplicity_cyclicSublatticePolynomial_pos_iff_quadraticNorm
    {N : ℕ} (hN : 0 < N) (τ : UpperHalfPlane) (B C : ℤ)
    (hτ : (τ : ℂ) ^ 2 + (B : ℂ) * (τ : ℂ) + C = 0) :
    0 < rootMultiplicity (jInvariant τ) (cyclicSublatticePolynomial N τ) ↔
      ∃ x k : ℤ, Nat.Coprime x.natAbs k.natAbs ∧
        x ^ 2 + B * x * k + C * k ^ 2 = (N : ℤ) :=
  (rootMultiplicity_cyclicSublatticePolynomial_pos_iff_exists_primitive_fixed_matrix
    hN τ).trans (exists_primitive_fixedMatrix_iff_quadraticNorm τ B C hτ (N : ℤ))

/-- For any actual primitive integral quadratic relation, diagonal modular
roots are exactly the primitive values of its quadratic norm. -/
theorem rootMultiplicity_cyclicSublatticePolynomial_pos_iff_primitiveQuadraticNorm
    {N : ℕ} (hN : 0 < N) (τ : UpperHalfPlane) (a b c : ℤ) (ha : a ≠ 0)
    (hprim : Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0) :
    0 < rootMultiplicity (jInvariant τ) (cyclicSublatticePolynomial N τ) ↔
      ∃ x k : ℤ, Nat.Coprime x.natAbs k.natAbs ∧
        x ^ 2 + b * x * k + a * c * k ^ 2 = (N : ℤ) :=
  (rootMultiplicity_cyclicSublatticePolynomial_pos_iff_exists_primitive_fixed_matrix
    hN τ).trans
      (exists_primitive_fixedMatrix_iff_primitiveQuadraticNorm τ a b c ha hprim hτ (N : ℤ))

/-- A diagonal self-root at a level greater than one certifies that the actual
parameter is imaginary quadratic. The discriminant need not yet be primitive. -/
theorem exists_integer_quadratic_of_cyclicSublattice_rootMultiplicity_pos
    {N : ℕ} (hN : 1 < N) (τ : UpperHalfPlane)
    (hroot : 0 < rootMultiplicity (jInvariant τ) (cyclicSublatticePolynomial N τ)) :
    ∃ a b c : ℤ, 0 < a ∧ b ^ 2 - 4 * a * c < 0 ∧
      (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0 := by
  obtain ⟨A, hdet, hprim, hfix⟩ :=
    (rootMultiplicity_cyclicSublatticePolynomial_pos_iff_exists_primitive_fixed_matrix
      (by omega) τ).mp hroot
  apply exists_integer_quadratic_of_primitive_fixedMatrix τ A hprim hfix
  rw [hdet]
  omega

end BakerHeegnerStark
