/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.Modularity

/-!
# The Cubic Character on Determinant-Minus-One Matrices

Right multiplication by `diag(-1, 1)` identifies determinant-minus-one matrices
with `SL₂(𝔽₃)`. The resulting cubic character transforms by the character on the
left and its inverse on the right. Its inverse on an upper triangular matrix is
the actual gamma multiplier indexed by the product of the first-row entries.
-/

open scoped MatrixGroups

namespace ModularForm
noncomputable section

/-- Right multiplication by `diag(-1, 1)` normalizes determinant minus one. -/
def gammaNegativeDetThreeNormalize (A : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hA : A.det = -1) : SL(2, ZMod 3) :=
  ⟨!![-A 0 0, A 0 1; -A 1 0, A 1 1], by
    calc
      (!![-A 0 0, A 0 1; -A 1 0, A 1 1] :
          Matrix (Fin 2) (Fin 2) (ZMod 3)).det = -A.det := by
        simp [Matrix.det_fin_two]; ring
      _ = 1 := by rw [hA]; ring⟩

@[simp]
theorem gammaNegativeDetThreeNormalize_coe
    (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hA : A.det = -1) :
    (gammaNegativeDetThreeNormalize A hA : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      !![-A 0 0, A 0 1; -A 1 0, A 1 1] := rfl

/-- The cubic character of a determinant-minus-one matrix, normalized on the right. -/
def gammaNegativeDetThree (A : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hA : A.det = -1) : ℂ :=
  gammaCharacterThree (gammaNegativeDetThreeNormalize A hA)

theorem gammaNegativeDetThree_cube (A : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hA : A.det = -1) : gammaNegativeDetThree A hA ^ 3 = 1 :=
  gammaCharacterThree_cube _

theorem gammaNegativeDetThree_ne_zero (A : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hA : A.det = -1) : gammaNegativeDetThree A hA ≠ 0 :=
  gammaCharacterThree_ne_zero _

/-- Right normalization changes the right action into the reflected action. -/
theorem gammaNegativeDetThreeNormalize_of_matrix_relation
    (A B : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hA : A.det = -1) (hB : B.det = -1)
    (g k : SL(2, ZMod 3))
    (h : B = (k : Matrix (Fin 2) (Fin 2) (ZMod 3)) * A *
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3))) :
    gammaNegativeDetThreeNormalize B hB =
      k * gammaNegativeDetThreeNormalize A hA * gammaReflectionThree g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (!![-B 0 0, B 0 1; -B 1 0, B 1 1] :
      Matrix (Fin 2) (Fin 2) (ZMod 3)) i j =
    (((k : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      !![-A 0 0, A 0 1; -A 1 0, A 1 1]) *
      !![g 0 0, -g 0 1; -g 1 0, g 1 1]) i j
  rw [h]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The left character and inverse right character govern matrix equivalence. -/
theorem gammaNegativeDetThree_of_matrix_relation
    (A B : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hA : A.det = -1) (hB : B.det = -1)
    (g k : SL(2, ZMod 3))
    (h : B = (k : Matrix (Fin 2) (Fin 2) (ZMod 3)) * A *
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3))) :
    gammaNegativeDetThree B hB =
      gammaCharacterThree k * gammaNegativeDetThree A hA *
        (gammaCharacterThree g)⁻¹ := by
  unfold gammaNegativeDetThree
  rw [gammaNegativeDetThreeNormalize_of_matrix_relation A B hA hB g k h,
    map_mul, map_mul, gammaCharacterThree_reflection]

/-- On upper triangular matrices, right normalization has exponent `-(a * b)`. -/
theorem gammaNegativeDetThreeNormalize_upper_exponent (a b d : ZMod 3)
    (had : a * d = -1) :
    gammaExponentThree (gammaNegativeDetThreeNormalize (!![a, b; 0, d])
      (by simpa [Matrix.det_fin_two] using had)) = -(a * b) := by
  have hfinite : ∀ a b d : ZMod 3, a * d = -1 → b * d = -(a * b) := by decide
  simpa [gammaExponentThree, gammaNegativeDetThreeNormalize] using hfinite a b d had

/-- The inverse upper triangular character is the actual gamma phase. -/
theorem gammaNegativeDetThree_upper_inv (a b d : ZMod 3) (had : a * d = -1) :
    (gammaNegativeDetThree (!![a, b; 0, d])
      (by simpa [Matrix.det_fin_two] using had))⁻¹ = gammaMultiplierThree (a * b) := by
  change (gammaMultiplierThree (gammaExponentThree
    (gammaNegativeDetThreeNormalize (!![a, b; 0, d])
      (by simpa [Matrix.det_fin_two] using had))))⁻¹ = gammaMultiplierThree (a * b)
  rw [gammaNegativeDetThreeNormalize_upper_exponent a b d had,
    gammaMultiplierThree_neg, inv_inv]

end

end ModularForm
