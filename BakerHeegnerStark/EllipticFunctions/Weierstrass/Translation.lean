/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Rational Weierstrass translation coordinates

These are the chord expressions for the convention
`y² = 4x³ - g₂ x - g₃`, so `y` has the scale of `wp'`, not `wp'/2`.
At lattice poles of the second argument the expressions are filled in with
the coordinates of the first argument. At equal x-coordinates the raw
quotients remain totalized; no tangent formula is asserted by a definition.
-/

namespace PeriodPair

/-- The rational x-coordinate for translation by the Weierstrass point at `z`. -/
noncomputable def weierstrassTranslateX (L : PeriodPair) (z u : ℂ) : ℂ := by
  classical
  exact if u ∈ L.lattice then L.weierstrassP z else
    ((L.derivWeierstrassP u - L.derivWeierstrassP z) /
      (2 * (L.weierstrassP u - L.weierstrassP z))) ^ 2 -
      L.weierstrassP u - L.weierstrassP z

/-- The rational derivative-scale y-coordinate for the same translation. -/
noncomputable def weierstrassTranslateY (L : PeriodPair) (z u : ℂ) : ℂ := by
  classical
  exact if u ∈ L.lattice then L.derivWeierstrassP z else
    -L.derivWeierstrassP u +
      (L.derivWeierstrassP u - L.derivWeierstrassP z) /
        (L.weierstrassP u - L.weierstrassP z) *
          (L.weierstrassP u - L.weierstrassTranslateX z u)

/-- At a lattice argument the translated x-coordinate has the specified regular value. -/
theorem weierstrassTranslateX_of_mem (L : PeriodPair) (z : ℂ) {u : ℂ}
    (hu : u ∈ L.lattice) : L.weierstrassTranslateX z u = L.weierstrassP z := by
  classical
  simp only [weierstrassTranslateX, ite_eq_left hu]

/-- At a lattice argument the translated y-coordinate has the specified regular value. -/
theorem weierstrassTranslateY_of_mem (L : PeriodPair) (z : ℂ) {u : ℂ}
    (hu : u ∈ L.lattice) : L.weierstrassTranslateY z u = L.derivWeierstrassP z := by
  classical
  simp only [weierstrassTranslateY, ite_eq_left hu]

end PeriodPair
