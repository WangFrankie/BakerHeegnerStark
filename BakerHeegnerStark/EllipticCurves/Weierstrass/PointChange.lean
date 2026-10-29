/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticCurves.Torsion
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Admissible changes on actual elliptic-curve point groups

The standard affine coordinate change maps points of the transformed
Weierstrass equation to points of the original equation, with infinity
fixed. It preserves the existing point-group addition: vertical chords,
ordinary chords, and tangents are handled using their actual formulas.
The resulting additive isomorphism restricts to every integer-torsion
subgroup. No characteristic-zero assumption is needed.
-/

namespace WeierstrassCurve.VariableChange

variable {F : Type*} [Field F]

/-- The x-coordinate of the admissible change from the transformed curve to the original. -/
def pointX (C : VariableChange F) (x : F) : F := (C.u : F) ^ 2 * x + C.r

/-- The y-coordinate, sharing the square factor in the standard affine change. -/
def pointY (C : VariableChange F) (x y : F) : F :=
  (C.u : F) ^ 2 * ((C.u : F) * y + C.s * x) + C.t

/-- The actual equation is preserved in the direction from the transformed curve to the original. -/
theorem equation_point_iff (W : WeierstrassCurve F) (C : VariableChange F) (x y : F) :
    W.toAffine.Equation (C.pointX x) (C.pointY x y) ↔
      (C • W).toAffine.Equation x y := by
  have hcomp : VariableChange.mk 1 x 0 y * C =
      VariableChange.mk C.u (C.pointX x) C.s (C.pointY x y) := by
    ext <;> simp [VariableChange.mul_def, pointX, pointY] <;> ring
  rw [W.toAffine.equation_iff_variableChange, (C • W).toAffine.equation_iff_variableChange,
    ← mul_smul, hcomp]
  simp only [WeierstrassCurve.Affine.equation_zero, variableChange_a₆, inv_one,
    Units.val_one, one_pow, one_mul]
  simp [mul_eq_zero]

/-- The transformed x-coordinate is injective. -/
theorem pointX_injective (C : VariableChange F) : Function.Injective C.pointX := by
  intro x y h
  have hp : (C.u : F) ^ 2 * (x - y) = 0 := by
    dsimp only [pointX] at h
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (pow_ne_zero 2 C.u.ne_zero))

/-- At fixed x, the transformed y-coordinate is injective. -/
theorem pointY_injective (C : VariableChange F) (x : F) : Function.Injective (C.pointY x) := by
  intro y v h
  have hp : (C.u : F) ^ 3 * (y - v) = 0 := by
    dsimp only [pointY] at h
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (pow_ne_zero 3 C.u.ne_zero))

/-- The admissible coordinate change respects actual point negation. -/
theorem pointY_negY (W : WeierstrassCurve F) (C : VariableChange F) (x y : F) :
    C.pointY x ((C • W).toAffine.negY x y) =
      W.toAffine.negY (C.pointX x) (C.pointY x y) := by
  simp only [pointY, pointX, WeierstrassCurve.Affine.negY, variableChange_a₁,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp [C.u.ne_zero]
  ring

/-- The x-coordinate chord polynomial respects the transformed slope. -/
theorem pointX_addX (W : WeierstrassCurve F) (C : VariableChange F) (x₁ x₂ ℓ : F) :
    C.pointX ((C • W).toAffine.addX x₁ x₂ ℓ) =
      W.toAffine.addX (C.pointX x₁) (C.pointX x₂) ((C.u : F) * ℓ + C.s) := by
  simp only [pointX, WeierstrassCurve.Affine.addX, variableChange_a₁,
    variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp [C.u.ne_zero]
  ring

/-- The y-coordinate chord polynomial respects the same transformed slope. -/
theorem pointY_addY (W : WeierstrassCurve F) (C : VariableChange F) (x₁ x₂ y₁ ℓ : F) :
    C.pointY ((C • W).toAffine.addX x₁ x₂ ℓ) ((C • W).toAffine.addY x₁ x₂ y₁ ℓ) =
      W.toAffine.addY (C.pointX x₁) (C.pointX x₂) (C.pointY x₁ y₁)
        ((C.u : F) * ℓ + C.s) := by
  have hx := pointX_addX W C x₁ x₂ ℓ
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY]
  rw [pointY_negY]
  simp only [← hx]
  congr 1
  simp only [pointX, pointY]
  ring

/-- The actual point map from the transformed equation to the original equation. -/
noncomputable def pointMap (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic] :
    (C • W).toAffine.Point → W.toAffine.Point
  | .zero => 0
  | .some x y h => .mk ((equation_point_iff W C x y).mpr h.1)

@[simp]
theorem pointMap_zero (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic] :
    C.pointMap W 0 = 0 := rfl

/-- Admissible changes separate actual affine points and never identify one with infinity. -/
theorem pointMap_injective (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic] :
    Function.Injective (C.pointMap W) := by
  rintro (_ | ⟨x, y, hp⟩) (_ | ⟨a, b, hq⟩) h
  · rfl
  · cases h
  · cases h
  · have hxy := WeierstrassCurve.Affine.Point.some.inj h
    have hx := C.pointX_injective hxy.1
    subst a
    have hy := C.pointY_injective x hxy.2
    subst b
    rfl

/-- Inverting the actual affine coordinates gives every point of the original curve. -/
theorem pointMap_surjective (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic] :
    Function.Surjective (C.pointMap W) := by
  intro P
  cases P with
  | zero => exact ⟨0, rfl⟩
  | some X Y hp =>
    let x := (X - C.r) / (C.u : F) ^ 2
    let y := (Y - C.t - C.s * (X - C.r)) / (C.u : F) ^ 3
    have hx : C.pointX x = X := by
      dsimp only [pointX, x]
      field_simp [C.u.ne_zero]
      ring
    have hy : C.pointY x y = Y := by
      dsimp only [pointY, x, y]
      field_simp [C.u.ne_zero]
      ring
    have heq : (C • W).toAffine.Equation x y :=
      (equation_point_iff W C x y).mp (by rw [hx, hy]; exact hp.1)
    refine ⟨.mk heq, ?_⟩
    simp only [WeierstrassCurve.Affine.Point.mk, pointMap, hx, hy]

variable [DecidableEq F]

/-- At a nonvertical chord or tangent, the actual slope transforms by `ℓ ↦ uℓ+s`. -/
theorem slope_point (W : WeierstrassCurve F) (C : VariableChange F)
    {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope (C.pointX x₁) (C.pointX x₂) (C.pointY x₁ y₁) (C.pointY x₂ y₂) =
      (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  by_cases hx : x₁ = x₂
  · subst x₂
    have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have heq := ((C • W).toAffine.Y_eq_of_X_eq h₁ h₂ rfl).resolve_right hy
    subst y₂
    have hym : C.pointY x₁ y₁ ≠ W.toAffine.negY (C.pointX x₁) (C.pointY x₁ y₁) := by
      intro h
      apply hy
      apply C.pointY_injective x₁
      exact h.trans (pointY_negY W C x₁ y₁).symm
    have hden : C.pointY x₁ y₁ - W.toAffine.negY (C.pointX x₁) (C.pointY x₁ y₁) =
        (C.u : F) ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁) := by
      rw [← pointY_negY W C x₁ y₁]
      dsimp only [pointY]
      ring
    have hne : y₁ - (C • W).toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hym,
      WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hden]
    generalize hd : y₁ - (C • W).toAffine.negY x₁ y₁ = d at hne ⊢
    field_simp [C.u.ne_zero, hne]
    rw [← hd]
    simp only [pointX, pointY, WeierstrassCurve.Affine.negY,
      variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      Units.val_inv_eq_inv_val]
    field_simp [C.u.ne_zero]
    ring
  · have hxm : C.pointX x₁ ≠ C.pointX x₂ := fun h => hx (C.pointX_injective h)
    have hden : C.pointX x₁ - C.pointX x₂ = (C.u : F) ^ 2 * (x₁ - x₂) := by
      dsimp only [pointX]
      ring
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxm,
      WeierstrassCurve.Affine.slope_of_X_ne hx, hden]
    simp only [pointY]
    field_simp [C.u.ne_zero, sub_ne_zero.mpr hx]
    ring

/-- The actual coordinate change preserves the existing point-group addition. -/
theorem pointMap_add (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic]
    (P Q : (C • W).toAffine.Point) : C.pointMap W (P + Q) = C.pointMap W P + C.pointMap W Q := by
  rcases P, Q with ⟨_ | ⟨x₁, y₁, h₁⟩, _ | ⟨x₂, y₂, h₂⟩⟩
  · rfl
  · rfl
  · rfl
  · by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · have hxm : C.pointX x₁ = C.pointX x₂ := congrArg C.pointX hxy.1
      have hym : C.pointY x₁ y₁ = W.toAffine.negY (C.pointX x₂) (C.pointY x₂ y₂) := by
        rw [hxy.1, hxy.2]
        exact pointY_negY W C x₂ y₂
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2, pointMap_zero]
      simp only [pointMap, WeierstrassCurve.Affine.Point.mk]
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxm hym]
    · have hmxy : ¬(C.pointX x₁ = C.pointX x₂ ∧
          C.pointY x₁ y₁ = W.toAffine.negY (C.pointX x₂) (C.pointY x₂ y₂)) := by
        rintro ⟨hx, hy⟩
        have hxeq := C.pointX_injective hx
        apply hxy
        refine ⟨hxeq, ?_⟩
        apply C.pointY_injective x₂
        rw [← pointY_negY W C x₂ y₂] at hy
        simpa only [hxeq] using hy
      rw [WeierstrassCurve.Affine.Point.add_some hxy]
      simp only [pointMap, WeierstrassCurve.Affine.Point.mk]
      rw [WeierstrassCurve.Affine.Point.add_some hmxy]
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      rw [slope_point W C h₁.1 h₂.1 hxy]
      exact And.intro
        (pointX_addX W C x₁ x₂ ((C • W).toAffine.slope x₁ x₂ y₁ y₂))
        (pointY_addY W C x₁ x₂ y₁ ((C • W).toAffine.slope x₁ x₂ y₁ y₂))

/-- The admissible change as a homomorphism of the actual curve point groups. -/
noncomputable def pointMapHom (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic] :
    (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := C.pointMap W
  map_zero' := C.pointMap_zero W
  map_add' := C.pointMap_add W

/-- The admissible change as an additive isomorphism, with the original group laws. -/
noncomputable def pointAddEquiv (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic] :
    (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  AddEquiv.ofBijective (C.pointMapHom W) ⟨C.pointMap_injective W, C.pointMap_surjective W⟩

@[simp]
theorem pointAddEquiv_apply (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic]
    (P : (C • W).toAffine.Point) : C.pointAddEquiv W P = C.pointMap W P := rfl

/-- The actual point isomorphism restricts to every integer-torsion subgroup. -/
noncomputable def pointTorsionEquiv (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℤ) : AddSubgroup.torsionBy (C • W).toAffine.Point n ≃+
      AddSubgroup.torsionBy W.toAffine.Point n :=
  (C.pointAddEquiv W).torsionByEquiv n

@[simp]
theorem pointTorsionEquiv_val (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℤ) (P : AddSubgroup.torsionBy (C • W).toAffine.Point n) :
    (C.pointTorsionEquiv W n P : W.toAffine.Point) = C.pointAddEquiv W P := rfl

end WeierstrassCurve.VariableChange
