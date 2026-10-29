/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Isogeny
import BakerHeegnerStark.ComplexMultiplication.JInvariant.Endomorphism
import BakerHeegnerStark.EllipticCurves.JInvariant.Coordinates

/-!
# Finite coordinates of actual CM and its coefficient conjugates

All formulas concern actual curve points, including infinity. The finite kernel
points are transported by the genuine coefficient action; no continuity of that
action, fixed normalization scale, or fixed quadratic period is assumed.
-/

open scoped IntermediateField

namespace BakerHeegnerStark

/-- Completing the square on the auxiliary model coordinates. -/
noncomputable def jInvariantCurveShortY (τ : UpperHalfPlane)
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) : ℂ :=
  jInvariantCurveY τ P +
    (((jInvariantCurve τ).baseChange ℂ).a₁ * jInvariantCurveX τ P +
      ((jInvariantCurve τ).baseChange ℂ).a₃) / 2

@[simp]
theorem jInvariantCurveShortY_zero (τ : UpperHalfPlane) :
    jInvariantCurveShortY τ 0 = 0 := by
  change (jInvariantCurveChange τ).t +
    (((jInvariantCurve τ).baseChange ℂ).a₁ * (jInvariantCurveChange τ).r +
      ((jInvariantCurve τ).baseChange ℂ).a₃) / 2 = 0
  rw [jInvariantCurveChange_t_eq]
  ring

/-- The completed-square coordinate is coefficient equivariant even at infinity. -/
theorem jInvariantCurveShortY_galois [DecidableEq ℂ] (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    jInvariantCurveShortY τ
      ((weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd P) =
        σ (jInvariantCurveShortY τ P) := by
  have h₁ : σ ((jInvariantCurve τ).baseChange ℂ).a₁ =
      ((jInvariantCurve τ).baseChange ℂ).a₁ := σ.commutes (jInvariantCurve τ).a₁
  have h₃ : σ ((jInvariantCurve τ).baseChange ℂ).a₃ =
      ((jInvariantCurve τ).baseChange ℂ).a₃ := σ.commutes (jInvariantCurve τ).a₃
  simp only [jInvariantCurveShortY, jInvariantCurveY_galois, jInvariantCurveX_galois,
    map_add, map_div₀, map_mul, map_ofNat, h₁, h₃]

/-- The actual scale of the completed-square uniformization coordinate. -/
theorem jInvariantCurveShortY_periodPoint [DecidableEq ℂ]
    (τ : UpperHalfPlane) (z : ℂ) :
    jInvariantCurveShortY τ (jInvariantCurvePointEquiv τ (standardPeriodPoint τ z)) =
      ((jInvariantCurveChange τ).u : ℂ) ^ 3 *
        (standardPeriodPair τ).derivWeierstrassP z / 2 :=
  jInvariantCurve_shortY_periodPoint τ z

/-- The completed-square coordinate respects the actual normalization at every point. -/
theorem jInvariantCurveShortY_equiv [DecidableEq ℂ] (τ : UpperHalfPlane)
    (P : (periodCurve (standardPeriodPair τ)).toAffine.Point) :
    jInvariantCurveShortY τ (jInvariantCurvePointEquiv τ P) =
      ((jInvariantCurveChange τ).u : ℂ) ^ 3 * periodCurveY τ P := by
  obtain ⟨z, rfl⟩ := standardPeriodPoint_surjective τ P
  rw [jInvariantCurveShortY_periodPoint, periodCurveY_standardPeriodPoint]
  ring

/-- The specified actual CM kernel point on the j-generated coefficient model. -/
noncomputable def jInvariantCMKernelPoint [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (k : Fin m) :
    ((jInvariantCurve τ).baseChange ℂ).toAffine.Point :=
  jInvariantCurvePointEquiv τ
    (periodCurveCMKernelPoint τ m hm (by simpa only [Int.cast_natCast] using hτ) k)

/-- The actual image of the specified kernel point, returned to the period curve. -/
noncomputable def periodCMConjugateKernelPoint [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) (k : Fin m) :
    (periodCurve (standardPeriodPair τ)).toAffine.Point :=
  (jInvariantCurvePointEquiv τ).symm
    ((weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
      (jInvariantCMKernelPoint τ m hm hτ k))

@[simp]
theorem jInvariantCMKernelPoint_zero [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) :
    jInvariantCMKernelPoint τ m hm hτ ⟨0, hm⟩ = 0 := by
  simp [jInvariantCMKernelPoint, periodCurveCMKernelPoint,
    standardPeriodPoint_of_mem τ (zero_mem _)]

/-- The actual enumeration remains injective after normalization. -/
theorem jInvariantCMKernelPoint_injective [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) :
    Function.Injective (jInvariantCMKernelPoint τ m hm hτ) := by
  intro k l h
  apply (periodCurveCMKernelPoint_bijective τ m hm
    (by simpa only [Int.cast_natCast] using hτ)).1
  apply Subtype.ext
  exact (jInvariantCurvePointEquiv τ).injective h

@[simp]
theorem periodCMConjugateKernelPoint_zero [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) :
    periodCMConjugateKernelPoint τ m hm hτ σ ⟨0, hm⟩ = 0 := by
  simp [periodCMConjugateKernelPoint]

/-- Only the specified zero index maps to infinity after actual coefficient conjugation. -/
theorem periodCMConjugateKernelPoint_eq_zero_iff [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) (k : Fin m) :
    periodCMConjugateKernelPoint τ m hm hτ σ k = 0 ↔ k = ⟨0, hm⟩ := by
  constructor
  · intro h
    apply jInvariantCMKernelPoint_injective τ m hm hτ
    have he := congrArg (jInvariantCurvePointEquiv τ) h
    have hs := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd.injective
      (by simpa [periodCMConjugateKernelPoint] using he)
    simpa using hs
  · rintro rfl
    exact periodCMConjugateKernelPoint_zero τ m hm hτ σ

/-- The genuine coefficient conjugate of actual CM, as a period-curve group endomorphism. -/
noncomputable def periodCMGaloisConjugate [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) :
    (periodCurve (standardPeriodPair τ)).toAffine.Point →+
      (periodCurve (standardPeriodPair τ)).toAffine.Point :=
  let e := jInvariantCurvePointEquiv τ
  let s := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
  e.symm.toAddMonoidHom.comp (s.toAddMonoidHom.comp
    ((jInvariantCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ)).comp
      (s.symm.toAddMonoidHom.comp e.toAddMonoidHom)))

private theorem divisionPeriodRepresentatives_sum_fin
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (f : ℂ → ℂ) :
    (∑ t ∈ divisionPeriodRepresentatives τ m, f t) =
      ∑ k : Fin m, f ((k.val : ℂ) * (τ : ℂ) / (m : ℂ)) := by
  classical
  rw [divisionPeriodRepresentatives, Finset.sum_image]
  · exact (Fin.sum_univ_eq_sum_range
      (fun k : ℕ => f ((k : ℂ) * (τ : ℂ) / (m : ℂ))) m).symm
  · intro k hk l hl h
    apply (divisionPeriodPoint_sub_mem_iff τ m hm k l
      (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)).mp
    dsimp only at h
    rw [h]
    simp only [sub_self, zero_mem]

private theorem standardPeriodPoint_sub [DecidableEq ℂ]
    (τ : UpperHalfPlane) (z w : ℂ) :
    standardPeriodPoint τ (z - w) = standardPeriodPoint τ z - standardPeriodPoint τ w := by
  rw [sub_eq_add_neg, standardPeriodPoint_add, standardPeriodPoint_neg, sub_eq_add_neg]

/-- Finite x-coordinates of actual CM on every actual normalized-model point. -/
theorem jInvariantCurveX_CM_finite_sum [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    jInvariantCurveX τ
      (jInvariantCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ) P) =
      (jInvariantCurveChange τ).r + ((τ : ℂ) ^ 2)⁻¹ *
        ((∑ k : Fin m, jInvariantCurveX τ (P - jInvariantCMKernelPoint τ m hm hτ k)) -
          ∑ k : Fin m, jInvariantCurveX τ (jInvariantCMKernelPoint τ m hm hτ k)) := by
  obtain ⟨R, rfl⟩ := (jInvariantCurvePointEquiv τ).surjective P
  obtain ⟨z, rfl⟩ := standardPeriodPoint_surjective τ R
  simp only [jInvariantCMKernelPoint, periodCurveCMKernelPoint,
    ← map_sub, ← standardPeriodPoint_sub, jInvariantCurveCMEnd_periodPoint,
    jInvariantCurveX_periodPoint, WeierstrassCurve.VariableChange.pointX]
  rw [weierstrassP_CM_finite_sum τ m hm hτ z,
    divisionPeriodRepresentatives_sum_fin τ m hm,
    divisionPeriodRepresentatives_sum_fin τ m hm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Finite completed-square y-coordinates of actual CM on every actual model point. -/
theorem jInvariantCurveShortY_CM_finite_sum [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    jInvariantCurveShortY τ
      (jInvariantCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ) P) =
      ((τ : ℂ) ^ 3)⁻¹ *
        ∑ k : Fin m, jInvariantCurveShortY τ (P - jInvariantCMKernelPoint τ m hm hτ k) := by
  obtain ⟨R, rfl⟩ := (jInvariantCurvePointEquiv τ).surjective P
  obtain ⟨z, rfl⟩ := standardPeriodPoint_surjective τ R
  simp only [jInvariantCMKernelPoint, periodCurveCMKernelPoint,
    ← map_sub, ← standardPeriodPoint_sub, jInvariantCurveCMEnd_periodPoint,
    jInvariantCurveShortY_periodPoint]
  rw [derivWeierstrassP_CM_finite_sum τ m hm hτ z,
    divisionPeriodRepresentatives_sum_fin τ m hm]
  simp only [div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Applying a coefficient automorphism to the proved finite x-formula involves only finite sums. -/
theorem jInvariantCurveX_CM_conjugate_finite_sum [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    let s := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
    jInvariantCurveX τ
      (s (jInvariantCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ) (s.symm P))) =
      (jInvariantCurveChange τ).r + ((σ (τ : ℂ)) ^ 2)⁻¹ *
        ((∑ k : Fin m, jInvariantCurveX τ (P - s (jInvariantCMKernelPoint τ m hm hτ k))) -
          ∑ k : Fin m, jInvariantCurveX τ (s (jInvariantCMKernelPoint τ m hm hτ k))) := by
  let s := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
  have h := congrArg σ (jInvariantCurveX_CM_finite_sum τ m hm hτ (s.symm P))
  have hr : σ (jInvariantCurveChange τ).r = (jInvariantCurveChange τ).r :=
    σ.commutes ⟨_, jInvariantCurveChange_r_mem τ⟩
  simp only [map_add, map_mul, map_inv₀, map_pow, map_sub, map_sum, hr] at h
  simpa only [← jInvariantCurveX_galois, s, map_sub, AddEquiv.apply_symm_apply] using h

/-- The genuine coefficient action transports the finite completed-square y-formula. -/
theorem jInvariantCurveShortY_CM_conjugate_finite_sum [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    let s := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
    jInvariantCurveShortY τ
      (s (jInvariantCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ) (s.symm P))) =
      ((σ (τ : ℂ)) ^ 3)⁻¹ *
        ∑ k : Fin m, jInvariantCurveShortY τ (P - s (jInvariantCMKernelPoint τ m hm hτ k)) := by
  let s := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
  have h := congrArg σ (jInvariantCurveShortY_CM_finite_sum τ m hm hτ (s.symm P))
  simp only [map_mul, map_inv₀, map_pow, map_sum] at h
  simpa only [← jInvariantCurveShortY_galois, s, map_sub, AddEquiv.apply_symm_apply] using h

/-- The x-coordinate of actual coefficient-conjugate CM, with the conjugated period scalar. -/
theorem periodCurveX_CMGaloisConjugate_finite_sum [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (P : (periodCurve (standardPeriodPair τ)).toAffine.Point) :
    periodCurveX τ (periodCMGaloisConjugate τ m hτ σ P) =
      ((σ (τ : ℂ)) ^ 2)⁻¹ *
        ((∑ k : Fin m, periodCurveX τ (P - periodCMConjugateKernelPoint τ m hm hτ σ k)) -
          ∑ k : Fin m, periodCurveX τ (periodCMConjugateKernelPoint τ m hm hτ σ k)) := by
  let e := jInvariantCurvePointEquiv τ
  let s := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
  have h := jInvariantCurveX_CM_conjugate_finite_sum τ m hm hτ σ (e P)
  have he : s (jInvariantCurveCMEnd τ m
      (by simpa only [Int.cast_natCast] using hτ) (s.symm (e P))) =
      e (periodCMGaloisConjugate τ m hτ σ P) := by
    simp [periodCMGaloisConjugate, e, s]
  have hq (k : Fin m) :
      s (jInvariantCMKernelPoint τ m hm hτ k) =
        e (periodCMConjugateKernelPoint τ m hm hτ σ k) := by
    simp [periodCMConjugateKernelPoint, e, s]
  dsimp only at h
  dsimp only [s] at he hq
  rw [he] at h
  simp only [hq, e, ← map_sub, jInvariantCurveX_equiv,
    WeierstrassCurve.VariableChange.pointX, Finset.sum_add_distrib,
    ← Finset.mul_sum] at h
  have hu : ((jInvariantCurveChange τ).u : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Units.ne_zero _)
  apply (mul_left_cancel₀ hu)
  linear_combination h

/-- The y-coordinate of actual coefficient-conjugate CM, with scale `(σ τ)⁻³`. -/
theorem periodCurveY_CMGaloisConjugate_finite_sum [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (P : (periodCurve (standardPeriodPair τ)).toAffine.Point) :
    periodCurveY τ (periodCMGaloisConjugate τ m hτ σ P) =
      ((σ (τ : ℂ)) ^ 3)⁻¹ *
        ∑ k : Fin m, periodCurveY τ (P - periodCMConjugateKernelPoint τ m hm hτ σ k) := by
  let e := jInvariantCurvePointEquiv τ
  let s := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
  have h := jInvariantCurveShortY_CM_conjugate_finite_sum τ m hm hτ σ (e P)
  have he : s (jInvariantCurveCMEnd τ m
      (by simpa only [Int.cast_natCast] using hτ) (s.symm (e P))) =
      e (periodCMGaloisConjugate τ m hτ σ P) := by
    simp [periodCMGaloisConjugate, e, s]
  have hq (k : Fin m) :
      s (jInvariantCMKernelPoint τ m hm hτ k) =
        e (periodCMConjugateKernelPoint τ m hm hτ σ k) := by
    simp [periodCMConjugateKernelPoint, e, s]
  dsimp only at h
  dsimp only [s] at he hq
  rw [he] at h
  simp only [hq, e, ← map_sub, jInvariantCurveShortY_equiv, ← Finset.mul_sum] at h
  have hu : ((jInvariantCurveChange τ).u : ℂ) ^ 3 ≠ 0 :=
    pow_ne_zero _ (Units.ne_zero _)
  apply (mul_left_cancel₀ hu)
  linear_combination h

end BakerHeegnerStark
