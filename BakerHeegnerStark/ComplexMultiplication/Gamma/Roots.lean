/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.CyclicModularity
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.NormThree

/-!
# Exact Twisted Gamma Roots at Shifted CM Points

At levels congruent to two modulo three, a cyclic-sublattice transform with
unchanged j-invariant has twisted gamma value exactly equal to the square of
the original gamma value. The normalization is determined by the cubic
character of an actual integral fixed matrix, not by choosing a cube root.

The fixed matrices of `(3 + √-m)/2` have equal diagonal entries modulo three.
Their determinant-minus-one normalization therefore has trace zero and trivial
cubic character. This also gives uniqueness among actual twisted-product roots
with cube `j²`, including the case `j = 0`, and supplies such a root at some
nontrivial level whenever `3 ∤ m`. No class-number or reciprocity hypothesis is
used.
-/

open Matrix UpperHalfPlane ModularForm Polynomial
open scoped MatrixGroups

noncomputable section

namespace BakerHeegnerStark

private theorem isRoot_cyclicSublatticeGammaPolynomial_iff_exists_triple
    (N : ℕ) (τ : UpperHalfPlane) (z : ℂ) :
    (cyclicSublatticeGammaPolynomial N τ).IsRoot z ↔
      ∃ t ∈ cyclicSublatticeTriples N, z = cyclicSublatticeGammaRoot t τ := by
  classical
  simp only [cyclicSublatticeGammaPolynomial, IsRoot, eval_prod, eval_sub, eval_X,
    eval_C, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- A self-correspondence of the actual shifted CM point has twisted gamma
value exactly `gamma₂²`. The character calculation fixes the cubic phase even
when the gamma value vanishes. -/
theorem cyclicSublatticeGammaRoot_eq_square_of_jInvariant_eq {m N : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) (hN : 0 < N) (hN3 : N % 3 = 2)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ cyclicSublatticeTriples N)
    (hj : jInvariant (cyclicSublatticePoint t (cmPointShift m)) =
      jInvariant (cmPointShift m)) :
    cyclicSublatticeGammaRoot t (cmPointShift m) = gamma₂ (cmPointShift m) ^ 2 := by
  let τ := cmPointShift m
  obtain ⟨g, hg⟩ :=
    (jInvariant_eq_iff_modularOrbit (cyclicSublatticePoint t τ) τ).mp hj
  let M := cyclicSublatticeMatrix ⟨t, ht⟩
  let A : FixedDetMatrix (Fin 2) ℤ (N : ℤ) := g⁻¹ • M
  have hfix : (A.1 0 0 : ℂ) * (τ : ℂ) + A.1 0 1 =
      (τ : ℂ) * ((A.1 1 0 : ℂ) * (τ : ℂ) + A.1 1 1) := by
    apply (positiveFixedDetMatrixGL_fixed_iff hN A τ).mp
    change positiveFixedDetMatrixGL hN (g⁻¹ • M) • τ = τ
    rw [positiveFixedDetMatrixGL_smul, mul_smul]
    change g⁻¹ •
      (positiveFixedDetMatrixGL hN (cyclicSublatticeMatrix ⟨t, ht⟩) • τ) = τ
    rw [positiveFixedDetMatrixGL_cyclicSublatticeMatrix_smul, ← hg, inv_smul_smul]
  have hτ : (τ : ℂ) ^ 2 + ((-3 : ℤ) : ℂ) * (τ : ℂ) +
      ((((m + 1) / 4 + 2 : ℕ) : ℤ) : ℂ) = 0 := by
    simpa only [τ, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, neg_mul,
      sub_eq_add_neg] using cmPointShift_quadratic hm hm4
  obtain ⟨x, k, hA⟩ := (fixed_iff_eq_quadraticFixedMatrix τ (-3)
    (((m + 1) / 4 + 2 : ℕ) : ℤ) hτ A.1).mp hfix
  have hlevel : (N : ZMod 3) = -1 := by
    calc
      (N : ZMod 3) = ((N % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
      _ = -1 := by rw [hN3]; decide
  let A₃ := A.1.map (Int.castRingHom (ZMod 3))
  let M₃ : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
    !![(t.1 : ZMod 3), (t.2.1 : ZMod 3); 0, (t.2.2 : ZMod 3)]
  have hA₃ : A₃.det = -1 := by
    calc
      A₃.det = (A.1.det : ZMod 3) :=
        ((Int.castRingHom (ZMod 3)).map_det A.1).symm
      _ = (N : ZMod 3) := by rw [A.2]; simp
      _ = -1 := hlevel
  have had : (t.1 : ZMod 3) * (t.2.2 : ZMod 3) = -1 := by
    have hadInt := ((mem_cyclicSublatticeTriples hN).mp ht).1
    rw [← Nat.cast_mul, hadInt]
    exact hlevel
  have hM₃ : M₃.det = -1 := by
    simpa [M₃, Matrix.det_fin_two] using had
  have hdiag : A₃ 0 0 = A₃ 1 1 := by
    simp [A₃, hA, quadraticFixedMatrix, show (3 : ZMod 3) = 0 by decide]
  have hχA : gammaNegativeDetThree A₃ hA₃ = 1 := by
    apply gammaCharacterThree_eq_one_of_trace_eq_zero
    change -A₃ 0 0 + A₃ 1 1 = 0
    rw [hdiag, neg_add_cancel]
  have hmatrix : (g : Matrix (Fin 2) (Fin 2) ℤ) * A.1 = M.1 := by
    have h : g • A = M := smul_inv_smul g M
    have h' := congrArg Subtype.val h
    simpa only [FixedDetMatrices.smul_coe] using h'
  have hmapM : M.1.map (Int.castRingHom (ZMod 3)) = M₃ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, M₃, cyclicSublatticeMatrix]
  have hrelation : M₃ =
      (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g :
        Matrix (Fin 2) (Fin 2) (ZMod 3)) * A₃ *
      (1 : SL(2, ZMod 3)) := by
    have h := congrArg
      (fun B : Matrix (Fin 2) (Fin 2) ℤ => B.map (Int.castRingHom (ZMod 3))) hmatrix
    rw [Matrix.map_mul, hmapM] at h
    change
      (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g :
        Matrix (Fin 2) (Fin 2) (ZMod 3)) * A₃ = M₃ at h
    change M₃ =
      (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g :
        Matrix (Fin 2) (Fin 2) (ZMod 3)) * A₃ * (1 : Matrix (Fin 2) (Fin 2) (ZMod 3))
    simpa only [Matrix.mul_one] using h.symm
  have hχM : gammaNegativeDetThree M₃ hM₃ = gammaCharacter g := by
    change gammaNegativeDetThree M₃ hM₃ =
      gammaCharacterThree (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g)
    have h := gammaNegativeDetThree_of_matrix_relation A₃ M₃ hA₃ hM₃ 1
      (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g) hrelation
    simpa only [hχA, map_one, inv_one, mul_one] using h
  have hphase : gammaPhaseThree ^ (t.1 * t.2.1) = (gammaCharacter g)⁻¹ := by
    calc
      gammaPhaseThree ^ (t.1 * t.2.1) =
          gammaMultiplierThree ((t.1 : ZMod 3) * (t.2.1 : ZMod 3)) := by
        rw [← Nat.cast_mul, gammaMultiplierThree_natCast]
      _ = (gammaNegativeDetThree M₃ hM₃)⁻¹ :=
        (gammaNegativeDetThree_upper_inv _ _ _ had).symm
      _ = (gammaCharacter g)⁻¹ := by rw [hχM]
  have hg0 : gammaCharacter g ≠ 0 := gammaCharacterThree_ne_zero
    (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g)
  change cyclicSublatticeGammaRoot t τ = gamma₂ τ ^ 2
  rw [cyclicSublatticeGammaRoot, ← hg, ModularForm.gamma₂_smul, hphase]
  field_simp [hg0] <;> ring

/-- Among the roots of the actual twisted product, the equation `z³ = j²`
selects exactly the square of the normalized gamma value at the shifted CM
point. The zero case does not require cancelling either j or gamma. -/
theorem eq_gamma₂_cmPointShift_sq_of_isRoot_of_cube {m N : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) (hN : 0 < N) (hN3 : N % 3 = 2)
    {z : ℂ} (hz : (cyclicSublatticeGammaPolynomial N (cmPointShift m)).IsRoot z)
    (hcube : z ^ 3 = jInvariant (cmPointShift m) ^ 2) :
    z = gamma₂ (cmPointShift m) ^ 2 := by
  by_cases hj : jInvariant (cmPointShift m) = 0
  · have hz3 : z ^ 3 = 0 := by simpa [hj] using hcube
    have hz0 : z = 0 := eq_zero_of_pow_eq_zero hz3
    have hγ3 : gamma₂ (cmPointShift m) ^ 3 = 0 :=
      (gamma₂_cube (cmPointShift m)).trans hj
    have hγ0 : gamma₂ (cmPointShift m) = 0 := eq_zero_of_pow_eq_zero hγ3
    simp [hz0, hγ0]
  · obtain ⟨t, ht, hzt⟩ :=
      (isRoot_cyclicSublatticeGammaPolynomial_iff_exists_triple N (cmPointShift m) z).mp hz
    have hprod : jInvariant (cmPointShift m) *
        jInvariant (cyclicSublatticePoint t (cmPointShift m)) =
        jInvariant (cmPointShift m) * jInvariant (cmPointShift m) := by
      rw [← cyclicSublatticeGammaRoot_cube, ← hzt, hcube, pow_two]
    have htj : jInvariant (cyclicSublatticePoint t (cmPointShift m)) =
        jInvariant (cmPointShift m) := mul_left_cancel₀ hj hprod
    exact hzt.trans
      (cyclicSublatticeGammaRoot_eq_square_of_jInvariant_eq hm hm4 hN hN3 t ht htj)

/-- Every shifted CM point with `3 ∤ m` has its exact normalized gamma square
as a root of an actual twisted cyclic-sublattice product at a nontrivial level
congruent to two modulo three. -/
theorem exists_level_gamma₂_cmPointShift_sq_isRoot {m : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) (hm3 : ¬ 3 ∣ m) :
    ∃ N : ℕ, 1 < N ∧ N % 3 = 2 ∧
      (cyclicSublatticeGammaPolynomial N (cmPointShift m)).IsRoot
        (gamma₂ (cmPointShift m) ^ 2) := by
  obtain ⟨N, hN, hN3, hmult⟩ :=
    exists_level_mod_three_rootMultiplicity_cmPointShift_pos hm hm4 hm3
  have hroot : (cyclicSublatticePolynomial N (cmPointShift m)).IsRoot
      (jInvariant (cmPointShift m)) :=
    (Polynomial.rootMultiplicity_pos
      (monic_cyclicSublatticePolynomial N (cmPointShift m)).ne_zero).mp hmult
  have hex : ∃ t ∈ cyclicSublatticeTriples N,
      jInvariant (cmPointShift m) =
        jInvariant (cyclicSublatticePoint t (cmPointShift m)) := by
    classical
    simpa only [cyclicSublatticePolynomial, IsRoot, eval_prod, eval_sub, eval_X,
      eval_C, Finset.prod_eq_zero_iff, sub_eq_zero] using hroot
  obtain ⟨t, ht, hj⟩ := hex
  refine ⟨N, hN, hN3, ?_⟩
  apply (isRoot_cyclicSublatticeGammaPolynomial_iff_exists_triple
    N (cmPointShift m) (gamma₂ (cmPointShift m) ^ 2)).mpr
  exact ⟨t, ht,
    (cyclicSublatticeGammaRoot_eq_square_of_jInvariant_eq
      hm hm4 (by omega) hN3 t ht hj.symm).symm⟩

end BakerHeegnerStark
