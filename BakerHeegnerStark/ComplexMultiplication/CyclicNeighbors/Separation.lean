/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.FixedPoints
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.SmallNorms

/-!
# Distinct cyclic CM neighbours at levels three and eight

Analytic j-separation converts a collision of actual cyclic-sublattice
j-values into an integral modular equivalence. Conjugating by the two
positive Hermite matrices gives an integral matrix fixing the original CM
point, with determinant the square of the level. The small quadratic-norm
criteria force this matrix to be scalar, and uniqueness of positive Hermite
representatives then recovers equality of the original triples.

The level-three statement needs only `m > 9`; the level-eight statement
needs only `m > 4` and `m ≡ 3 (mod 8)`. No primality, squarefreeness, or
class-number hypothesis is involved.
-/

open Matrix UpperHalfPlane ModularForm
open scoped MatrixGroups

noncomputable section

namespace BakerHeegnerStark

private theorem cyclicNeighbor_adjugate_fixed {N : ℕ} (hN : 0 < N)
    (s t : {t // t ∈ cyclicSublatticeTriples N}) (g : SL(2, ℤ))
    (τ : UpperHalfPlane) (hg : g • cyclicSublatticePoint t.1 τ =
      cyclicSublatticePoint s.1 τ) :
    let B := (cyclicSublatticeMatrix s).1.adjugate *
      (g : Matrix (Fin 2) (Fin 2) ℤ) * (cyclicSublatticeMatrix t).1
    (B 0 0 : ℂ) * (τ : ℂ) + B 0 1 =
      (τ : ℂ) * ((B 1 0 : ℂ) * (τ : ℂ) + B 1 1) := by
  let A := cyclicSublatticeMatrix s
  let T := cyclicSublatticeMatrix t
  let B := A.1.adjugate * (g : Matrix (Fin 2) (Fin 2) ℤ) * T.1
  have hdet : B.det = (N : ℤ) ^ 2 := by
    simp [B, Matrix.det_mul, Matrix.det_adjugate, A, T, pow_two,
      (cyclicSublatticeMatrix s).2, (cyclicSublatticeMatrix t).2, g.2]
  let D : FixedDetMatrix (Fin 2) ℤ ((N * N : ℕ) : ℤ) :=
    ⟨B, by simpa only [Nat.cast_mul, pow_two] using hdet⟩
  have hAB : A.1 * B = (N : ℤ) • ((g : Matrix (Fin 2) (Fin 2) ℤ) * T.1) := by
    calc
      A.1 * B = (A.1 * A.1.adjugate) *
          ((g : Matrix (Fin 2) (Fin 2) ℤ) * T.1) := by
        simp only [B, Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.mul_adjugate, A.2, Matrix.smul_mul, Matrix.one_mul]
  let u : ℝˣ := Units.mk0 (N : ℝ) (by exact_mod_cast hN.ne')
  have hGL : positiveFixedDetMatrixGL hN A *
      positiveFixedDetMatrixGL (Nat.mul_pos hN hN) D =
      GeneralLinearGroup.scalar (Fin 2) u *
        (SpecialLinearGroup.mapGL ℝ g * positiveFixedDetMatrixGL hN T) := by
    apply Units.ext
    change A.1.map (Int.castRingHom ℝ) * B.map (Int.castRingHom ℝ) =
      Matrix.scalar (Fin 2) (N : ℝ) *
        ((g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) *
          T.1.map (Int.castRingHom ℝ))
    rw [← Matrix.map_mul, hAB, ← Matrix.map_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      map_natCast, ← Matrix.diagonal_natCast, Matrix.diagonal_mul]
  have hact : positiveFixedDetMatrixGL hN A •
      (positiveFixedDetMatrixGL (Nat.mul_pos hN hN) D • τ) =
      positiveFixedDetMatrixGL hN A • τ := by
    rw [← mul_smul, hGL, mul_smul, UpperHalfPlane.glScalar_smul, mul_smul]
    change g • (positiveFixedDetMatrixGL hN T • τ) = _
    simpa only [A, T, positiveFixedDetMatrixGL_cyclicSublatticeMatrix_smul] using hg
  have hfixed : positiveFixedDetMatrixGL (Nat.mul_pos hN hN) D • τ = τ := by
    calc
      _ = (positiveFixedDetMatrixGL hN A)⁻¹ •
          (positiveFixedDetMatrixGL hN A •
            (positiveFixedDetMatrixGL (Nat.mul_pos hN hN) D • τ)) :=
        (inv_smul_smul _ _).symm
      _ = τ := by rw [hact, inv_smul_smul]
  exact (positiveFixedDetMatrixGL_fixed_iff (Nat.mul_pos hN hN) D τ).mp hfixed

private theorem jInvariant_cyclicNeighbor_injective_of_norm_rigidity
    {N m : ℕ} (hN : 0 < N) (τ : UpperHalfPlane)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (hnorm : ∀ x k : ℤ, x ^ 2 + (m : ℤ) * k ^ 2 = (N : ℤ) ^ 2 →
      k = 0 ∧ (x = (N : ℤ) ∨ x = -(N : ℤ))) :
    Function.Injective (fun t : {t // t ∈ cyclicSublatticeTriples N} =>
      jInvariant (cyclicSublatticePoint t.1 τ)) := by
  intro s t hj
  obtain ⟨g, hg⟩ := (jInvariant_eq_iff_modularOrbit _ _).mp hj
  let A := cyclicSublatticeMatrix s
  let T := cyclicSublatticeMatrix t
  let B := A.1.adjugate * (g : Matrix (Fin 2) (Fin 2) ℤ) * T.1
  have hfix : (B 0 0 : ℂ) * (τ : ℂ) + B 0 1 =
      (τ : ℂ) * ((B 1 0 : ℂ) * (τ : ℂ) + B 1 1) :=
    cyclicNeighbor_adjugate_fixed hN s t g τ hg
  have hquad : (τ : ℂ) ^ 2 + (0 : ℤ) * (τ : ℂ) + (m : ℤ) = 0 := by
    simpa only [Int.cast_zero, zero_mul, add_zero, Int.cast_natCast, hτ] using
      neg_add_cancel (m : ℂ)
  obtain ⟨x, k, hB⟩ := (fixed_iff_eq_quadraticFixedMatrix τ 0 m hquad B).mp hfix
  have hdet : B.det = (N : ℤ) ^ 2 := by
    simp [B, Matrix.det_mul, Matrix.det_adjugate, A, T, pow_two,
      (cyclicSublatticeMatrix s).2, (cyclicSublatticeMatrix t).2, g.2]
  have hnorm' : x ^ 2 + (m : ℤ) * k ^ 2 = (N : ℤ) ^ 2 := by
    simpa only [hB, quadraticFixedMatrix_det, zero_mul, add_zero] using hdet
  obtain ⟨hk, hx⟩ := hnorm x k hnorm'
  have hAB : A.1 * B = (N : ℤ) • ((g : Matrix (Fin 2) (Fin 2) ℤ) * T.1) := by
    calc
      A.1 * B = (A.1 * A.1.adjugate) *
          ((g : Matrix (Fin 2) (Fin 2) ℤ) * T.1) := by
        simp only [B, Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.mul_adjugate, A.2, Matrix.smul_mul, Matrix.one_mul]
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have horbit : ∃ γ : SL(2, ℤ), γ • T = A := by
    rcases hx with hx | hx
    · have hscalar : B = (N : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [hB, hk, hx]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [quadraticFixedMatrix]
      rw [hscalar, Matrix.mul_smul, Matrix.mul_one] at hAB
      refine ⟨g, ?_⟩
      apply FixedDetMatrices.ext'
      change (g : Matrix (Fin 2) (Fin 2) ℤ) * T.1 = A.1
      ext i j
      exact mul_left_cancel₀ hNz (congrFun₂ hAB i j).symm
    · have hscalar : B = -(N : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [hB, hk, hx]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [quadraticFixedMatrix]
      rw [hscalar, Matrix.mul_smul, Matrix.mul_one] at hAB
      refine ⟨-g, ?_⟩
      apply FixedDetMatrices.ext'
      change ((-g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * T.1 = A.1
      have hneg : (g : Matrix (Fin 2) (Fin 2) ℤ) * T.1 = -A.1 := by
        ext i j
        apply mul_left_cancel₀ hNz
        have hij := congrFun₂ hAB i j
        simpa only [Matrix.smul_apply, smul_eq_mul, neg_mul, Matrix.neg_apply,
          mul_neg] using hij.symm
      simp only [SpecialLinearGroup.coe_neg, neg_mul, hneg, neg_neg]
  obtain ⟨γ, hγ⟩ := horbit
  have heq : T = A := (fixedDetMatrix_reps_smul_eq
    (show (0 : ℤ) < N by exact_mod_cast hN)
    (cyclicSublatticeMatrix_mem_primitiveHermiteMatrices hN t).1
    (cyclicSublatticeMatrix_mem_primitiveHermiteMatrices hN s).1 hγ).2
  apply (cyclicSublatticeMatrixEquiv hN).injective
  exact Subtype.ext heq.symm

/-- At a quadratic CM point with `m > 9`, the actual level-three cyclic
neighbours have pairwise distinct analytic j-invariants. -/
theorem jInvariant_cyclicSublatticePoint_injective_three
    (τ : UpperHalfPlane) (m : ℕ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (hm : 9 < m) :
    Function.Injective (fun t : {t // t ∈ cyclicSublatticeTriples 3} =>
      jInvariant (cyclicSublatticePoint t.1 τ)) := by
  apply jInvariant_cyclicNeighbor_injective_of_norm_rigidity (by decide) τ hτ
  intro x k h
  exact (quadraticNorm_eq_nine_iff hm x k).mp (by norm_num at h ⊢; exact h)

/-- At a quadratic CM point with `m > 4` and `m ≡ 3 (mod 8)`, the actual
eight-level cyclic neighbours have pairwise distinct analytic j-invariants. -/
theorem jInvariant_cyclicSublatticePoint_injective_eight
    (τ : UpperHalfPlane) (m : ℕ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (hm : 4 < m) (hm8 : m % 8 = 3) :
    Function.Injective (fun t : {t // t ∈ cyclicSublatticeTriples 8} =>
      jInvariant (cyclicSublatticePoint t.1 τ)) := by
  apply jInvariant_cyclicNeighbor_injective_of_norm_rigidity (by decide) τ hτ
  intro x k h
  exact (quadraticNorm_eq_sixty_four_iff hm hm8 x k).mp
    (by norm_num at h ⊢; exact h)

end BakerHeegnerStark
