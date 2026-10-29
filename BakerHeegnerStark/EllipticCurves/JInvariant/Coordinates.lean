/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticCurves.JInvariant.Normalization

/-!
# Auxiliary totalized coordinates on the actual normalized curves

These projections retain the affine coordinates on actual finite points. Their
values at infinity are only auxiliary defaults: `(0, 0)` on the period curve,
and `(r, t)` on the j-generated model. Thus the actual normalization and every
coefficient automorphism respect these projections even at infinity.

The defaults do not turn infinity into an affine point. In particular, these
pairs of totalized coordinates are not asserted to distinguish all actual
points; reconstruction of a point must retain its finite/infinite branch.
-/

open scoped IntermediateField

namespace BakerHeegnerStark

private def curvePointX (W : WeierstrassCurve ℂ) (infinityValue : ℂ) :
    W.toAffine.Point → ℂ
  | .zero => infinityValue
  | .some x _ _ => x

private def curvePointY (W : WeierstrassCurve ℂ) (infinityValue : ℂ) :
    W.toAffine.Point → ℂ
  | .zero => infinityValue
  | .some _ y _ => y

/-- Auxiliary x-projection of the period curve, with default zero at infinity. -/
noncomputable def periodCurveX (τ : UpperHalfPlane) :
    (periodCurve (standardPeriodPair τ)).toAffine.Point → ℂ :=
  curvePointX (periodCurve (standardPeriodPair τ)) 0

/-- Auxiliary y-projection of the period curve, with default zero at infinity. -/
noncomputable def periodCurveY (τ : UpperHalfPlane) :
    (periodCurve (standardPeriodPair τ)).toAffine.Point → ℂ :=
  curvePointY (periodCurve (standardPeriodPair τ)) 0

/-- Auxiliary x-projection of the j-generated model, with default `r` at infinity. -/
noncomputable def jInvariantCurveX (τ : UpperHalfPlane) :
    ((jInvariantCurve τ).baseChange ℂ).toAffine.Point → ℂ :=
  curvePointX ((jInvariantCurve τ).baseChange ℂ) (jInvariantCurveChange τ).r

/-- Auxiliary y-projection of the j-generated model, with default `t` at infinity. -/
noncomputable def jInvariantCurveY (τ : UpperHalfPlane) :
    ((jInvariantCurve τ).baseChange ℂ).toAffine.Point → ℂ :=
  curvePointY ((jInvariantCurve τ).baseChange ℂ) (jInvariantCurveChange τ).t

/-- The auxiliary period x-coordinate agrees with the totalized `wp`, including its lattice values. -/
theorem periodCurveX_standardPeriodPoint (τ : UpperHalfPlane) (z : ℂ) :
    periodCurveX τ (standardPeriodPoint τ z) = (standardPeriodPair τ).weierstrassP z := by
  by_cases hz : z ∈ periodModule (τ : ℂ)
  · rw [standardPeriodPoint_of_mem τ hz]
    exact ((standardPeriodPair τ).weierstrassP_coe ⟨z, hz⟩).symm
  · rw [standardPeriodPoint_of_not_mem τ hz]
    rfl

/-- The auxiliary period y-coordinate agrees with totalized `wp'/2`, including lattice values. -/
theorem periodCurveY_standardPeriodPoint (τ : UpperHalfPlane) (z : ℂ) :
    periodCurveY τ (standardPeriodPoint τ z) =
      (standardPeriodPair τ).derivWeierstrassP z / 2 := by
  by_cases hz : z ∈ periodModule (τ : ℂ)
  · rw [standardPeriodPoint_of_mem τ hz]
    change 0 = (standardPeriodPair τ).derivWeierstrassP z / 2
    rw [(standardPeriodPair τ).derivWeierstrassP_coe ⟨z, hz⟩, zero_div]
  · rw [standardPeriodPoint_of_not_mem τ hz]
    rfl

private theorem pointAddEquiv_coordinates [DecidableEq ℂ]
    (W W' : WeierstrassCurve ℂ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℂ) (h : C • W = W') (P : W'.toAffine.Point) :
    let e : W'.toAffine.Point ≃+ W.toAffine.Point := by
      rw [← h]
      exact C.pointAddEquiv W
    (curvePointX W C.r (e P) = C.pointX (curvePointX W' 0 P)) ∧
    (curvePointY W C.t (e P) = C.pointY (curvePointX W' 0 P) (curvePointY W' 0 P)) := by
  cases h
  cases P with
  | zero =>
    change C.r = C.pointX 0 ∧ C.t = C.pointY 0 0
    simp [WeierstrassCurve.VariableChange.pointX, WeierstrassCurve.VariableChange.pointY]
  | some x y hp => exact ⟨rfl, rfl⟩

/-- The auxiliary x-projections respect the actual point equivalence, including infinity. -/
theorem jInvariantCurveX_equiv [DecidableEq ℂ] (τ : UpperHalfPlane)
    (P : (periodCurve (standardPeriodPair τ)).toAffine.Point) :
    jInvariantCurveX τ (jInvariantCurvePointEquiv τ P) =
      (jInvariantCurveChange τ).pointX (periodCurveX τ P) :=
  (pointAddEquiv_coordinates ((jInvariantCurve τ).baseChange ℂ)
    (periodCurve (standardPeriodPair τ)) (jInvariantCurveChange τ)
    (jInvariantCurveChange_smul τ) P).1

/-- The auxiliary y-projections respect the actual point equivalence, including infinity. -/
theorem jInvariantCurveY_equiv [DecidableEq ℂ] (τ : UpperHalfPlane)
    (P : (periodCurve (standardPeriodPair τ)).toAffine.Point) :
    jInvariantCurveY τ (jInvariantCurvePointEquiv τ P) =
      (jInvariantCurveChange τ).pointY (periodCurveX τ P) (periodCurveY τ P) :=
  (pointAddEquiv_coordinates ((jInvariantCurve τ).baseChange ℂ)
    (periodCurve (standardPeriodPair τ)) (jInvariantCurveChange τ)
    (jInvariantCurveChange_smul τ) P).2

/-- The normalized totalized x-coordinate of every actual uniformization point. -/
theorem jInvariantCurveX_periodPoint [DecidableEq ℂ] (τ : UpperHalfPlane) (z : ℂ) :
    jInvariantCurveX τ (jInvariantCurvePointEquiv τ (standardPeriodPoint τ z)) =
      (jInvariantCurveChange τ).pointX ((standardPeriodPair τ).weierstrassP z) := by
  rw [jInvariantCurveX_equiv, periodCurveX_standardPeriodPoint]

/-- The normalized totalized y-coordinate of every actual uniformization point. -/
theorem jInvariantCurveY_periodPoint [DecidableEq ℂ] (τ : UpperHalfPlane) (z : ℂ) :
    jInvariantCurveY τ (jInvariantCurvePointEquiv τ (standardPeriodPoint τ z)) =
      (jInvariantCurveChange τ).pointY ((standardPeriodPair τ).weierstrassP z)
        ((standardPeriodPair τ).derivWeierstrassP z / 2) := by
  rw [jInvariantCurveY_equiv, periodCurveX_standardPeriodPoint,
    periodCurveY_standardPeriodPoint]

/-- Coefficient automorphisms respect the auxiliary x-projection, including its arithmetic default. -/
theorem jInvariantCurveX_galois [DecidableEq ℂ] (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    jInvariantCurveX τ ((weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd P) =
      σ (jInvariantCurveX τ P) := by
  cases P with
  | zero =>
    change (jInvariantCurveChange τ).r = σ (jInvariantCurveChange τ).r
    exact (σ.commutes ⟨(jInvariantCurveChange τ).r, jInvariantCurveChange_r_mem τ⟩).symm
  | some x y hp => rfl

/-- Coefficient automorphisms respect the auxiliary y-projection, including its arithmetic default. -/
theorem jInvariantCurveY_galois [DecidableEq ℂ] (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    jInvariantCurveY τ ((weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd P) =
      σ (jInvariantCurveY τ P) := by
  cases P with
  | zero =>
    change (jInvariantCurveChange τ).t = σ (jInvariantCurveChange τ).t
    exact (σ.commutes ⟨(jInvariantCurveChange τ).t, jInvariantCurveChange_t_mem τ⟩).symm
  | some x y hp => rfl

/-- Completing the square recovers `u³ wp'/2` for all arguments, including actual lattice points. -/
theorem jInvariantCurve_shortY_periodPoint [DecidableEq ℂ] (τ : UpperHalfPlane) (z : ℂ) :
    jInvariantCurveY τ (jInvariantCurvePointEquiv τ (standardPeriodPoint τ z)) +
      (((jInvariantCurve τ).baseChange ℂ).a₁ *
        jInvariantCurveX τ (jInvariantCurvePointEquiv τ (standardPeriodPoint τ z)) +
        ((jInvariantCurve τ).baseChange ℂ).a₃) / 2 =
      ((jInvariantCurveChange τ).u : ℂ) ^ 3 *
        (standardPeriodPair τ).derivWeierstrassP z / 2 := by
  rw [jInvariantCurveX_periodPoint, jInvariantCurveY_periodPoint,
    jInvariantCurveChange_pointY]
  ring

end BakerHeegnerStark
