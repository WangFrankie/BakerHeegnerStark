/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticCurves.JInvariant.Uniformization
import BakerHeegnerStark.EllipticCurves.Weierstrass.Torsion
import BakerHeegnerStark.ComplexMultiplication.SingularModuli.Basic

/-!
# Algebraic torsion coordinates on the j-generated model

The proved positive-level torsion coordinates give finiteness of the
actual complex torsion group. The true coefficient action and the finite
orbit theorem then make both affine coordinates algebraic over `ℚ(j(τ))`.
No CM hypothesis or false Galois assumption on `ℂ/ℚ(j(τ))` is needed.
For positive square-root CM parameters, the proved singular-modulus
integrality further makes these torsion coordinates algebraic over `ℚ`.
-/

open scoped IntermediateField

namespace BakerHeegnerStark

/-- Actual positive-level torsion coordinates of the j-generated model are algebraic
over its actual coefficient field, with no Galois or algebraicity assumption on `ℂ`. -/
theorem jInvariantCurveTorsion_coordinates_isAlgebraic [DecidableEq ℂ]
    (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) {x y : ℂ}
    (hp : ((jInvariantCurve τ).toAffine.baseChange ℂ).Nonsingular x y)
    (hkill : N • WeierstrassCurve.Affine.Point.some x y hp = 0) :
    IsAlgebraic ℚ⟮ModularForm.jInvariant τ⟯ x ∧
      IsAlgebraic ℚ⟮ModularForm.jInvariant τ⟯ y := by
  let : NeZero N := ⟨ne_of_gt hN⟩
  let : Finite (WeierstrassTorsion (jInvariantCurve τ).toAffine ℂ N) :=
    Finite.of_equiv (Fin 2 → ZMod N) (jInvariantCurveTorsionCoordinatesEquiv τ N hN).toEquiv
  exact weierstrassTorsion_coordinates_isAlgebraic (jInvariantCurve τ).toAffine N hp hkill

/-- At every positive square-root CM parameter, all actual positive-level torsion
coordinates of the j-generated model are algebraic over `ℚ`, without reciprocity. -/
theorem jInvariantCurveTorsion_sqrtPoint_coordinates_isAlgebraic [DecidableEq ℂ]
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) {x y : ℂ}
    (hp : ((jInvariantCurve (sqrtPoint m)).toAffine.baseChange ℂ).Nonsingular x y)
    (hkill : N • WeierstrassCurve.Affine.Point.some x y hp = 0) :
    IsAlgebraic ℚ x ∧ IsAlgebraic ℚ y := by
  let := finiteDimensional_jInvariant_sqrtPoint hm
  have h := jInvariantCurveTorsion_coordinates_isAlgebraic (sqrtPoint m) N hN hp hkill
  exact ⟨IsAlgebraic.restrictScalars ℚ h.1, IsAlgebraic.restrictScalars ℚ h.2⟩

end BakerHeegnerStark
