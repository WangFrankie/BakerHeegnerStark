/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.FieldTheory.AlgebraicOrbit
import BakerHeegnerStark.EllipticCurves.Weierstrass.Galois

/-!
# Algebraic coordinates of finite actual Weierstrass torsion

The genuine coefficient Galois action carries every torsion point into
the same finite subgroup. Both affine coordinates therefore have finite
automorphism orbits and are algebraic over the infinite coefficient field.
The algebraically closed ambient extension need not be algebraic or Galois.
-/

namespace BakerHeegnerStark

/-- Finite actual torsion forces its affine coordinates to be algebraic, using the
genuine coefficient action rather than an algebraicity assumption on the extension. -/
theorem weierstrassTorsion_coordinates_isAlgebraic
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K L]
    [IsAlgClosed L] [DecidableEq L] (W : WeierstrassCurve.Affine K) (N : ℕ)
    [Finite (WeierstrassTorsion W L N)] {x y : L}
    (hp : (W.baseChange L).Nonsingular x y)
    (hkill : N • WeierstrassCurve.Affine.Point.some x y hp = 0) :
    IsAlgebraic K x ∧ IsAlgebraic K y := by
  let P : WeierstrassTorsion W L N :=
    ⟨.some x y hp, AddSubgroup.torsionBy.nsmul_iff.mpr hkill⟩
  let xCoord : WeierstrassTorsion W L N → L := fun Q =>
    match (Q : (W.baseChange L).Point) with
    | .zero => 0
    | .some a _ _ => a
  let yCoord : WeierstrassTorsion W L N → L := fun Q =>
    match (Q : (W.baseChange L).Point) with
    | .zero => 0
    | .some _ b _ => b
  have hx : (Set.range (fun σ : L ≃ₐ[K] L => σ x)).Finite := by
    apply (Set.finite_range xCoord).subset
    rintro z ⟨σ, rfl⟩
    exact ⟨(weierstrassTorsionGaloisAut W N σ).toAdd P, rfl⟩
  have hy : (Set.range (fun σ : L ≃ₐ[K] L => σ y)).Finite := by
    apply (Set.finite_range yCoord).subset
    rintro z ⟨σ, rfl⟩
    exact ⟨(weierstrassTorsionGaloisAut W N σ).toAdd P, rfl⟩
  exact ⟨isAlgebraic_of_finite_algEquiv_orbit x hx, isAlgebraic_of_finite_algEquiv_orbit y hy⟩

end BakerHeegnerStark
