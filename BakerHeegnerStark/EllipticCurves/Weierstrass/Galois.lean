/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Group.End
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Galois action on actual Weierstrass points and torsion

For a Weierstrass model defined over `K`, coefficient automorphisms of `L/K`
act on its actual nonsingular point group after base change to `L`.
The action is an invertible additive map, respects automorphism composition,
and restricts to the actual `N`-torsion subgroup for every `N`, including zero.
Affine coordinates transform exactly as `(x,y) ↦ (σ(x),σ(y))`.

When `L/K` is Galois, points fixed by every coefficient automorphism descend
to actual points of the base-field model. The same statement holds in the
actual `N`-torsion subgroups, with no finite-dimensional hypothesis.

The point-group convention `[DecidableEq L]` follows mathlib. Its `AddAut`
composition group is tagged `Multiplicative` for the Galois representation.
No nonsingularity hypothesis on the entire curve is needed for the action on
its nonsingular points; in particular this applies to elliptic curves.

This constructs the algebraic torsion action, not an identification with the
analytic period quotient in `EllipticFunctions/PeriodTorus/Torsion.lean`. A base-field-defined CM
endomorphism, uniformization compatibility, and algebraic modular-function
evaluation are still needed for the CM reciprocity argument.
-/

namespace BakerHeegnerStark
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq L]

/-- The actual base-changed nonsingular point group carries the coefficient Galois action. -/
noncomputable def weierstrassPointGaloisAut (W : WeierstrassCurve.Affine K) :
    (L ≃ₐ[K] L) →* Multiplicative (AddAut (W.baseChange L).Point) where
  toFun σ := Multiplicative.ofAdd
    { __ := WeierstrassCurve.Affine.Point.map (W' := W) σ.toAlgHom
      invFun := WeierstrassCurve.Affine.Point.map (W' := W) σ.symm.toAlgHom
      left_inv := by
        intro P
        cases P <;> simp [WeierstrassCurve.Affine.Point.map, WeierstrassCurve.Affine.Point.zero_def]
      right_inv := by
        intro P
        cases P <;> simp [WeierstrassCurve.Affine.Point.map, WeierstrassCurve.Affine.Point.zero_def] }
  map_one' := by
    change (_ : AddAut (W.baseChange L).Point) = _
    apply AddEquiv.ext
    intro P
    cases P <;> rfl
  map_mul' σ ρ := by
    change (_ : AddAut (W.baseChange L).Point) = _
    apply AddEquiv.ext
    intro P
    cases P <;> rfl

/-- The actual `N`-torsion subgroup of the base-changed nonsingular point group. -/
abbrev WeierstrassTorsion (W : WeierstrassCurve.Affine K) (F : Type*)
    [Field F] [Algebra K F] [DecidableEq F] (N : ℕ) :=
  AddSubgroup.torsionBy (W.baseChange F).Point (N : ℤ)

/-- The coefficient Galois action restricts to the actual `N`-torsion subgroup. -/
noncomputable def weierstrassTorsionGaloisAut (W : WeierstrassCurve.Affine K) (N : ℕ) :
    (L ≃ₐ[K] L) →* Multiplicative (AddAut (WeierstrassTorsion W L N)) where
  toFun σ :=
    let e := (weierstrassPointGaloisAut W σ).toAdd
    Multiplicative.ofAdd
      { toFun P := ⟨e P, by
          apply AddSubgroup.torsionBy.nsmul_iff.mpr
          rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp P.property, map_zero]⟩
        invFun P := ⟨e.symm P, by
          apply AddSubgroup.torsionBy.nsmul_iff.mpr
          rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp P.property, map_zero]⟩
        left_inv := by intro P; apply Subtype.ext; exact e.symm_apply_apply _
        right_inv := by intro P; apply Subtype.ext; exact e.apply_symm_apply _
        map_add' P Q := by apply Subtype.ext; exact map_add e (P : (W.baseChange L).Point) (Q : (W.baseChange L).Point) }
  map_one' := by
    change (_ : AddAut (WeierstrassTorsion W L N)) = _
    apply AddEquiv.ext
    intro P
    apply Subtype.ext
    change (weierstrassPointGaloisAut W (1 : L ≃ₐ[K] L)).toAdd (P : (W.baseChange L).Point) = _
    rw [map_one]
    rfl
  map_mul' σ ρ := by
    change (_ : AddAut (WeierstrassTorsion W L N)) = _
    apply AddEquiv.ext
    intro P
    apply Subtype.ext
    change (weierstrassPointGaloisAut W (σ * ρ)).toAdd (P : (W.baseChange L).Point) =
      (weierstrassPointGaloisAut W σ).toAdd
        ((weierstrassPointGaloisAut W ρ).toAdd (P : (W.baseChange L).Point))
    rw [map_mul]
    rfl

/-- Galois acts on an actual affine point by applying the automorphism to both coordinates. -/
theorem weierstrassPointGaloisAut_some (W : WeierstrassCurve.Affine K)
    (σ : L ≃ₐ[K] L) {x y : L} (h : (W.baseChange L).Nonsingular x y) :
    (weierstrassPointGaloisAut W σ).toAdd (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some (σ x) (σ y)
        ((W.baseChange_nonsingular σ.toAlgHom.injective x y).mpr h) := rfl

/-- A nonsingular affine point is fixed exactly when both coordinates are fixed. -/
theorem weierstrassPointGaloisAut_some_eq_self_iff (W : WeierstrassCurve.Affine K)
    (σ : L ≃ₐ[K] L) {x y : L} (h : (W.baseChange L).Nonsingular x y) :
    (weierstrassPointGaloisAut W σ).toAdd (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some x y h ↔ σ x = x ∧ σ y = y := by
  rw [weierstrassPointGaloisAut_some]
  constructor
  · intro hp
    exact WeierstrassCurve.Affine.Point.some.inj hp
  · rintro ⟨hx, hy⟩
    simp only [hx, hy]

/-- The torsion representation is the restriction of the actual coefficient map on points. -/
theorem weierstrassTorsionGaloisAut_val (W : WeierstrassCurve.Affine K) (N : ℕ)
    (σ : L ≃ₐ[K] L) (P : WeierstrassTorsion W L N) :
    ((weierstrassTorsionGaloisAut W N σ).toAdd P : (W.baseChange L).Point) =
      WeierstrassCurve.Affine.Point.map (W' := W) σ.toAlgHom (P : (W.baseChange L).Point) := rfl

/-- Galois-fixed actual points descend to the base-field model, also for infinite extensions. -/
theorem weierstrassPointGaloisAut_fixed_iff [DecidableEq K] [IsGalois K L]
    (W : WeierstrassCurve.Affine K) (P : (W.baseChange L).Point) :
    (∀ σ : L ≃ₐ[K] L, (weierstrassPointGaloisAut W σ).toAdd P = P) ↔
      ∃ Q : (W.baseChange K).Point,
        WeierstrassCurve.Affine.Point.baseChange (W' := W) K L Q = P := by
  constructor
  · intro h
    cases P with
    | zero => exact ⟨0, rfl⟩
    | some x y hp =>
      have hx : ∀ σ : L ≃ₐ[K] L, σ x = x := fun σ =>
        ((weierstrassPointGaloisAut_some_eq_self_iff W σ hp).mp (h σ)).1
      have hy : ∀ σ : L ≃ₐ[K] L, σ y = y := fun σ =>
        ((weierstrassPointGaloisAut_some_eq_self_iff W σ hp).mp (h σ)).2
      obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) x).mpr hx
      obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) y).mpr hy
      have hq : (W.baseChange K).Nonsingular a b := by
        apply (W.baseChange_nonsingular (Algebra.ofId K L).injective a b).mp
        change (W.baseChange L).Nonsingular (algebraMap K L a) (algebraMap K L b)
        rw [ha, hb]
        exact hp
      refine ⟨WeierstrassCurve.Affine.Point.some a b hq, ?_⟩
      simp [WeierstrassCurve.Affine.Point.baseChange,
        WeierstrassCurve.Affine.Point.map, Algebra.ofId, ha, hb]
  · rintro ⟨Q, rfl⟩ σ
    change WeierstrassCurve.Affine.Point.map σ.toAlgHom
      (WeierstrassCurve.Affine.Point.baseChange (W' := W) K L Q) = _
    exact WeierstrassCurve.Affine.Point.map_baseChange σ.toAlgHom Q

/-- Fixed actual torsion points descend without losing their `N`-torsion condition. -/
theorem weierstrassTorsionGaloisAut_fixed_iff [DecidableEq K] [IsGalois K L]
    (W : WeierstrassCurve.Affine K) (N : ℕ) (P : WeierstrassTorsion W L N) :
    (∀ σ : L ≃ₐ[K] L, (weierstrassTorsionGaloisAut W N σ).toAdd P = P) ↔
      ∃ Q : WeierstrassTorsion W K N,
        WeierstrassCurve.Affine.Point.baseChange (W' := W) K L
          (Q : (W.baseChange K).Point) = (P : (W.baseChange L).Point) := by
  constructor
  · intro h
    have hpoint : ∀ σ : L ≃ₐ[K] L,
        (weierstrassPointGaloisAut W σ).toAdd (P : (W.baseChange L).Point) = P := by
      intro σ
      exact congrArg Subtype.val (h σ)
    obtain ⟨Q, hQ⟩ := (weierstrassPointGaloisAut_fixed_iff W (P : (W.baseChange L).Point)).mp hpoint
    have hNQ : Q ∈ WeierstrassTorsion W K N := by
      apply AddSubgroup.torsionBy.nsmul_iff.mpr
      apply WeierstrassCurve.Affine.Point.map_injective (W' := W) (Algebra.ofId K L)
      rw [map_nsmul, map_zero]
      change N • (WeierstrassCurve.Affine.Point.baseChange (W' := W) K L Q) = 0
      rw [hQ]
      exact AddSubgroup.torsionBy.nsmul_iff.mp P.property
    exact ⟨⟨Q, hNQ⟩, hQ⟩
  · rintro ⟨Q, hQ⟩ σ
    apply Subtype.ext
    change (weierstrassPointGaloisAut W σ).toAdd (P : (W.baseChange L).Point) = P
    exact ((weierstrassPointGaloisAut_fixed_iff W (P : (W.baseChange L).Point)).mpr
      ⟨(Q : (W.baseChange K).Point), hQ⟩) σ

end BakerHeegnerStark
