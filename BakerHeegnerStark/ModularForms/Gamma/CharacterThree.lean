/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The cubic exponent on `SL₂(𝔽₃)`

The additive cubic quotient is normalized to take `S` to zero and `T` to one.
For a matrix with nonzero lower-left entry `c`, its exponent is `(a + d) * c`:
over `𝔽₃`, the inverse of a nonzero `c` is `c` itself. For an upper-triangular
matrix it is `b * d`. These formulas are compatible with multiplication.

This file contains only finite matrix-group statements. It does not depend on
an analytic gamma function or assert a modular transformation formula for one.
-/

open scoped MatrixGroups

namespace ModularForm

/-- The additive cubic exponent on `SL₂(𝔽₃)`, normalized by `e(S) = 0` and `e(T) = 1`. -/
def gammaExponentThree (g : SL(2, ZMod 3)) : ZMod 3 :=
  if g 1 0 = 0 then g 0 1 * g 1 1 else (g 0 0 + g 1 1) * g 1 0

@[simp]
theorem gammaExponentThree_one : gammaExponentThree (1 : SL(2, ZMod 3)) = 0 := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- The cubic exponent is additive under matrix multiplication. The finite
verification is checked by the Lean kernel. -/
theorem gammaExponentThree_mul (g h : SL(2, ZMod 3)) :
    gammaExponentThree (g * h) = gammaExponentThree g + gammaExponentThree h := by
  revert g h
  decide +kernel

@[simp]
theorem gammaExponentThree_S :
    gammaExponentThree
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) ModularGroup.S) = 0 := by
  decide

@[simp]
theorem gammaExponentThree_T :
    gammaExponentThree
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) ModularGroup.T) = 1 := by
  decide

/-- Conjugation by `diag(-1, 1)`, expressed without adjoining a determinant-minus-one
matrix to the special linear group. -/
def gammaReflectionThree (g : SL(2, ZMod 3)) : SL(2, ZMod 3) :=
  ⟨!![g 0 0, -g 0 1; -g 1 0, g 1 1], by
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using g.property
    simpa [Matrix.det_fin_two] using hdet⟩

@[simp]
theorem gammaExponentThree_reflection (g : SL(2, ZMod 3)) :
    gammaExponentThree (gammaReflectionThree g) = -gammaExponentThree g := by
  by_cases hc : g 1 0 = 0 <;>
    simp [gammaExponentThree, gammaReflectionThree, hc]

/-- A trace-zero matrix in `SL₂(𝔽₃)` has zero cubic exponent. -/
theorem gammaExponentThree_eq_zero_of_trace_eq_zero (g : SL(2, ZMod 3))
    (h : g 0 0 + g 1 1 = 0) : gammaExponentThree g = 0 := by
  by_cases hc : g 1 0 = 0
  · have hdet : g 0 0 * g 1 1 = 1 := by
      simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using g.property
    have hnonzero : ∀ a d : ZMod 3, a * d = 1 → a + d ≠ 0 := by decide
    exact False.elim (hnonzero _ _ hdet h)
  · simp [gammaExponentThree, hc, h]

end ModularForm
