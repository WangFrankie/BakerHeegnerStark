/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.Transformations
import BakerHeegnerStark.ModularForms.Gamma.CharacterThree
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Gamma as a Modular Function of Level Three

The actual S and T transformations extend to every integral special-linear
matrix via a cubic character that factors through reduction modulo three.
This gives principal level-three invariance, inversion of the character under
determinant-minus-one conjugation, and its triviality on trace-zero matrices.
No CM reciprocity or arithmetic assertion about singular values is assumed.
-/

open scoped MatrixGroups

namespace ModularForm
noncomputable section

/-- The inverse cubic root of unity occurring in the actual T transformation of gamma. -/
def gammaPhaseThree : ℂ := (Complex.exp (2 * Real.pi * Complex.I / 3))⁻¹

theorem gammaPhaseThree_cube : gammaPhaseThree ^ 3 = 1 := by
  unfold gammaPhaseThree
  rw [inv_pow, ← Complex.exp_nat_mul,
    show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3) =
      2 * Real.pi * Complex.I by push_cast; ring, Complex.exp_two_pi_mul_I, inv_one]

theorem gammaPhaseThree_ne_zero : gammaPhaseThree ≠ 0 :=
  inv_ne_zero (Complex.exp_ne_zero _)

/-- The cubic complex multiplier associated to a residue modulo three. -/
def gammaMultiplierThree (r : ZMod 3) : ℂ := gammaPhaseThree ^ r.val

theorem gammaMultiplierThree_zero : gammaMultiplierThree 0 = 1 := by
  simp [gammaMultiplierThree]

theorem gammaMultiplierThree_one : gammaMultiplierThree 1 = gammaPhaseThree := by
  norm_num [gammaMultiplierThree, ZMod.val_one_eq_one_mod]

theorem gammaMultiplierThree_ne_zero (r : ZMod 3) : gammaMultiplierThree r ≠ 0 :=
  pow_ne_zero _ gammaPhaseThree_ne_zero

theorem gammaMultiplierThree_cube (r : ZMod 3) : gammaMultiplierThree r ^ 3 = 1 := by
  rw [gammaMultiplierThree, ← pow_mul, Nat.mul_comm r.val 3, pow_mul,
    gammaPhaseThree_cube, one_pow]

theorem gammaMultiplierThree_add (r s : ZMod 3) :
    gammaMultiplierThree (r + s) = gammaMultiplierThree r * gammaMultiplierThree s := by
  unfold gammaMultiplierThree
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ gammaPhaseThree_cube).symm

theorem gammaMultiplierThree_neg (r : ZMod 3) :
    gammaMultiplierThree (-r) = (gammaMultiplierThree r)⁻¹ := by
  rw [← one_div, eq_div_iff (gammaMultiplierThree_ne_zero r),
    ← gammaMultiplierThree_add, neg_add_cancel, gammaMultiplierThree_zero]

/-- Natural exponents give the same actual multiplier after reduction modulo three. -/
theorem gammaMultiplierThree_natCast (n : ℕ) :
    gammaMultiplierThree (n : ZMod 3) = gammaPhaseThree ^ n := by
  rw [gammaMultiplierThree, ZMod.val_natCast]
  exact (pow_eq_pow_mod n gammaPhaseThree_cube).symm


/-- The actual complex-valued cubic character of the finite matrix group. -/
def gammaCharacterThree : SL(2, ZMod 3) →* ℂ where
  toFun g := gammaMultiplierThree (gammaExponentThree g)
  map_one' := by rw [gammaExponentThree_one, gammaMultiplierThree_zero]
  map_mul' g h := by rw [gammaExponentThree_mul, gammaMultiplierThree_add]

/-- The character of the integral modular group factors through reduction mod three. -/
def gammaCharacter : SL(2, ℤ) →* ℂ :=
  gammaCharacterThree.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)))

theorem gammaCharacterThree_cube (g : SL(2, ZMod 3)) : gammaCharacterThree g ^ 3 = 1 :=
  gammaMultiplierThree_cube _

theorem gammaCharacterThree_ne_zero (g : SL(2, ZMod 3)) : gammaCharacterThree g ≠ 0 :=
  gammaMultiplierThree_ne_zero _

/-- Conjugation by a determinant-minus-one diagonal matrix inverts the character. -/
theorem gammaCharacterThree_reflection (g : SL(2, ZMod 3)) :
    gammaCharacterThree (gammaReflectionThree g) = (gammaCharacterThree g)⁻¹ := by
  change gammaMultiplierThree (gammaExponentThree (gammaReflectionThree g)) =
    (gammaMultiplierThree (gammaExponentThree g))⁻¹
  rw [gammaExponentThree_reflection, gammaMultiplierThree_neg]

/-- Trace-zero matrices lie in the kernel of the cubic character. -/
theorem gammaCharacterThree_eq_one_of_trace_eq_zero (g : SL(2, ZMod 3))
    (h : g 0 0 + g 1 1 = 0) : gammaCharacterThree g = 1 := by
  change gammaMultiplierThree (gammaExponentThree g) = 1
  rw [gammaExponentThree_eq_zero_of_trace_eq_zero g h, gammaMultiplierThree_zero]

theorem gammaCharacter_S : gammaCharacter ModularGroup.S = 1 := by
  change gammaMultiplierThree (gammaExponentThree
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) ModularGroup.S)) = 1
  rw [gammaExponentThree_S, gammaMultiplierThree_zero]

theorem gammaCharacter_T : gammaCharacter ModularGroup.T = gammaPhaseThree := by
  change gammaMultiplierThree (gammaExponentThree
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) ModularGroup.T)) = gammaPhaseThree
  rw [gammaExponentThree_T, gammaMultiplierThree_one]

/-- The actual normalized gamma value transforms by the mod-three character.
This holds also at zeros of gamma; no quotient by its value is used. -/
theorem gamma₂_smul (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    gamma₂ (g • τ) = gammaCharacter g * gamma₂ τ := by
  have hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  revert τ
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      intro τ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · simpa only [gammaCharacter_S, one_mul] using gamma₂_smul_S τ
      · simpa only [UpperHalfPlane.modular_T_smul, gammaCharacter_T, gammaPhaseThree]
          using gamma₂_add_one τ
  | one =>
      intro τ
      simp only [one_smul, map_one, one_mul]
  | mul g h _ _ hg hh =>
      intro τ
      rw [mul_smul, hg, hh, map_mul, mul_assoc]
  | inv g _ hg =>
      intro τ
      have h := hg (g⁻¹ • τ)
      rw [smul_inv_smul] at h
      calc
        gamma₂ (g⁻¹ • τ) =
            (gammaCharacter g⁻¹ * gammaCharacter g) * gamma₂ (g⁻¹ • τ) := by
          rw [← map_mul, inv_mul_cancel, map_one, one_mul]
        _ = gammaCharacter g⁻¹ * gamma₂ τ := by rw [mul_assoc, ← h]

/-- Congruent integral matrices act identically on the actual gamma value. -/
theorem gamma₂_smul_of_mod_three_eq (g h : SL(2, ℤ))
    (hmod : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) h) (τ : UpperHalfPlane) :
    gamma₂ (g • τ) = gamma₂ (h • τ) := by
  rw [gamma₂_smul, gamma₂_smul]
  change gammaCharacterThree
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g) * gamma₂ τ =
    gammaCharacterThree
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) h) * gamma₂ τ
  rw [hmod]

/-- The normalized gamma function is invariant under the principal level-three subgroup. -/
theorem gamma₂_smul_of_mem_Gamma_three (g : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma 3) (τ : UpperHalfPlane) :
    gamma₂ (g • τ) = gamma₂ τ := by
  have hmod := (CongruenceSubgroup.Gamma_mem').mp hg
  rw [gamma₂_smul]
  change gammaCharacterThree
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g) * gamma₂ τ = gamma₂ τ
  rw [hmod, map_one, one_mul]

end

end ModularForm
