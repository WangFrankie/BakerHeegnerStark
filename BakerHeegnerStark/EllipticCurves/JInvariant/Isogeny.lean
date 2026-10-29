/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticCurves.JInvariant.Coordinates
import BakerHeegnerStark.EllipticFunctions.Weierstrass.IsogenyInvariants

/-!
# Finite-kernel invariant traces on the actual j-generated curve

The finite expressions below use actual curve points, omitting infinity before
summing. Their arithmetic equivariance uses only coefficients and the arithmetic
x-translation, not an arithmetic normalization unit or a continuous complex
automorphism. For genuine finite lattice quotients the analytic trace formulas
identify these expressions with the target invariants. Homothetic standard
lattices therefore give the actual analytic target j-value.
-/

open scoped IntermediateField

namespace BakerHeegnerStark

/-- The actual period map to the chosen curve over `ℚ(j(τ))`. -/
noncomputable def jInvariantPeriodPoint [DecidableEq ℂ] (τ : UpperHalfPlane) (z : ℂ) :
    ((jInvariantCurve τ).baseChange ℂ).toAffine.Point :=
  jInvariantCurvePointEquiv τ (standardPeriodPoint τ z)

/-- The period origin maps to the actual point at infinity. -/
@[simp]
theorem jInvariantPeriodPoint_zero [DecidableEq ℂ] (τ : UpperHalfPlane) :
    jInvariantPeriodPoint τ 0 = 0 := by
  simp [jInvariantPeriodPoint, standardPeriodPoint_of_mem τ (zero_mem _)]

/-- Fibres of the actual normalized period map are precisely period classes. -/
theorem jInvariantPeriodPoint_eq_iff_sub_mem [DecidableEq ℂ]
    (τ : UpperHalfPlane) (z w : ℂ) :
    jInvariantPeriodPoint τ z = jInvariantPeriodPoint τ w ↔
      z - w ∈ (standardPeriodPair τ).lattice := by
  rw [jInvariantPeriodPoint, jInvariantPeriodPoint,
    (jInvariantCurvePointEquiv τ).injective.eq_iff,
    standardPeriodPoint_eq_iff_sub_mem, standardPeriodPair_lattice_eq_periodModule]

/-- Infinity occurs exactly on the actual period lattice. -/
theorem jInvariantPeriodPoint_eq_zero_iff [DecidableEq ℂ]
    (τ : UpperHalfPlane) (z : ℂ) :
    jInvariantPeriodPoint τ z = 0 ↔ z ∈ (standardPeriodPair τ).lattice := by
  rw [← jInvariantPeriodPoint_zero τ, jInvariantPeriodPoint_eq_iff_sub_mem, sub_zero]

/-- The shifted actual x-projection. Its auxiliary value at infinity is zero. -/
noncomputable def jInvariantKernelX (τ : UpperHalfPlane)
    (Q : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) : ℂ :=
  jInvariantCurveX τ Q - (jInvariantCurveChange τ).r

/-- The first invariant of the coefficient model in classical normalization. -/
noncomputable def jInvariantBaseG₂ (τ : UpperHalfPlane) : ℂ :=
  ((jInvariantCurve τ).baseChange ℂ).c₄ / 12

/-- The second invariant of the coefficient model in classical normalization. -/
noncomputable def jInvariantBaseG₃ (τ : UpperHalfPlane) : ℂ :=
  ((jInvariantCurve τ).baseChange ℂ).c₆ / 216

/-- The finite first-invariant expression on actual points, with infinity omitted. -/
noncomputable def jInvariantKernelG₂ [DecidableEq ℂ] (τ : UpperHalfPlane)
    (S : Finset (((jInvariantCurve τ).baseChange ℂ).toAffine.Point)) : ℂ :=
  jInvariantBaseG₂ τ +
    ∑ Q ∈ S.erase 0, (60 * jInvariantKernelX τ Q ^ 2 - 5 * jInvariantBaseG₂ τ)

/-- The finite second-invariant expression on actual points, with infinity omitted. -/
noncomputable def jInvariantKernelG₃ [DecidableEq ℂ] (τ : UpperHalfPlane)
    (S : Finset (((jInvariantCurve τ).baseChange ℂ).toAffine.Point)) : ℂ :=
  jInvariantBaseG₃ τ +
    ∑ Q ∈ S.erase 0, (140 * jInvariantKernelX τ Q ^ 3 -
      21 * jInvariantBaseG₂ τ * jInvariantKernelX τ Q - 14 * jInvariantBaseG₃ τ)

/-- The finite j-expression; its geometric meaning is supplied by the coset theorems below. -/
noncomputable def jInvariantKernelJ [DecidableEq ℂ] (τ : UpperHalfPlane)
    (S : Finset (((jInvariantCurve τ).baseChange ℂ).toAffine.Point)) : ℂ :=
  1728 * jInvariantKernelG₂ τ S ^ 3 /
    (jInvariantKernelG₂ τ S ^ 3 - 27 * jInvariantKernelG₃ τ S ^ 2)

/-- The actual complex normalization scales the first lattice invariant by `u⁴`. -/
theorem jInvariantCurveChange_g₂ (τ : UpperHalfPlane) :
    ((jInvariantCurveChange τ).u : ℂ) ^ 4 * (standardPeriodPair τ).g₂ =
      jInvariantBaseG₂ τ := by
  have h := congrArg WeierstrassCurve.c₄ (jInvariantCurveChange_smul τ)
  rw [WeierstrassCurve.variableChange_c₄, periodCurve_c₄] at h
  simp only [Units.val_inv_eq_inv_val, inv_pow] at h
  have hu := Units.ne_zero (jInvariantCurveChange τ).u
  field_simp [hu] at h
  dsimp [jInvariantBaseG₂]
  linear_combination -h / 12

/-- The actual complex normalization scales the second lattice invariant by `u⁶`. -/
theorem jInvariantCurveChange_g₃ (τ : UpperHalfPlane) :
    ((jInvariantCurveChange τ).u : ℂ) ^ 6 * (standardPeriodPair τ).g₃ =
      jInvariantBaseG₃ τ := by
  have h := congrArg WeierstrassCurve.c₆ (jInvariantCurveChange_smul τ)
  rw [WeierstrassCurve.variableChange_c₆, periodCurve_c₆] at h
  simp only [Units.val_inv_eq_inv_val, inv_pow] at h
  have hu := Units.ne_zero (jInvariantCurveChange τ).u
  field_simp [hu] at h
  dsimp [jInvariantBaseG₃]
  linear_combination -h / 216

/-- The shifted actual x-coordinate is `u² wp`, including the auxiliary pole values. -/
theorem jInvariantKernelX_periodPoint [DecidableEq ℂ] (τ : UpperHalfPlane) (z : ℂ) :
    jInvariantKernelX τ (jInvariantPeriodPoint τ z) =
      ((jInvariantCurveChange τ).u : ℂ) ^ 2 * (standardPeriodPair τ).weierstrassP z := by
  rw [jInvariantKernelX, jInvariantPeriodPoint, jInvariantCurveX_periodPoint]
  simp [WeierstrassCurve.VariableChange.pointX]

private theorem baseG₂_mem (τ : UpperHalfPlane) :
    jInvariantBaseG₂ τ ∈ ℚ⟮ModularForm.jInvariant τ⟯ := by
  rw [jInvariantBaseG₂, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄]
  exact (ℚ⟮ModularForm.jInvariant τ⟯).div_mem (jInvariantCurve τ).c₄.property
    ((ℚ⟮ModularForm.jInvariant τ⟯).natCast_mem 12)

private theorem baseG₃_mem (τ : UpperHalfPlane) :
    jInvariantBaseG₃ τ ∈ ℚ⟮ModularForm.jInvariant τ⟯ := by
  rw [jInvariantBaseG₃, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆]
  exact (ℚ⟮ModularForm.jInvariant τ⟯).div_mem (jInvariantCurve τ).c₆.property
    ((ℚ⟮ModularForm.jInvariant τ⟯).natCast_mem 216)

/-- Coefficient automorphisms commute with the shifted coordinate on every actual point. -/
theorem jInvariantKernelX_galois [DecidableEq ℂ] (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (Q : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    jInvariantKernelX τ ((weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd Q) =
      σ (jInvariantKernelX τ Q) := by
  have hr : σ (jInvariantCurveChange τ).r = (jInvariantCurveChange τ).r :=
    σ.commutes ⟨_, jInvariantCurveChange_r_mem τ⟩
  simp only [jInvariantKernelX, jInvariantCurveX_galois, map_sub, hr]

/-- The finite first-invariant trace is covariant for the actual coefficient point action. -/
theorem jInvariantKernelG₂_galois [DecidableEq ℂ] (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (S : Finset (((jInvariantCurve τ).baseChange ℂ).toAffine.Point)) :
    σ (jInvariantKernelG₂ τ S) =
      jInvariantKernelG₂ τ
        (S.image (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd) := by
  classical
  let e := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
  have he : (S.image e).erase 0 = (S.erase 0).image e := by
    simpa only [map_zero] using (Finset.image_erase e.injective S 0).symm
  have hA : σ (jInvariantBaseG₂ τ) = jInvariantBaseG₂ τ := σ.commutes ⟨_, baseG₂_mem τ⟩
  change σ (jInvariantKernelG₂ τ S) = jInvariantKernelG₂ τ (S.image e)
  simp only [jInvariantKernelG₂, he,
    Finset.sum_image (fun _ _ _ _ h => e.injective h), map_add, map_sum,
    map_sub, map_mul, map_pow, map_ofNat, hA]
  congr 1
  apply Finset.sum_congr rfl
  intro Q _
  rw [show jInvariantKernelX τ (e Q) = σ (jInvariantKernelX τ Q) from
    jInvariantKernelX_galois τ σ Q]

/-- The finite second-invariant trace is covariant for the actual coefficient point action. -/
theorem jInvariantKernelG₃_galois [DecidableEq ℂ] (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (S : Finset (((jInvariantCurve τ).baseChange ℂ).toAffine.Point)) :
    σ (jInvariantKernelG₃ τ S) =
      jInvariantKernelG₃ τ
        (S.image (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd) := by
  classical
  let e := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
  have he : (S.image e).erase 0 = (S.erase 0).image e := by
    simpa only [map_zero] using (Finset.image_erase e.injective S 0).symm
  have hA : σ (jInvariantBaseG₂ τ) = jInvariantBaseG₂ τ := σ.commutes ⟨_, baseG₂_mem τ⟩
  have hB : σ (jInvariantBaseG₃ τ) = jInvariantBaseG₃ τ := σ.commutes ⟨_, baseG₃_mem τ⟩
  change σ (jInvariantKernelG₃ τ S) = jInvariantKernelG₃ τ (S.image e)
  simp only [jInvariantKernelG₃, he,
    Finset.sum_image (fun _ _ _ _ h => e.injective h), map_add, map_sum,
    map_sub, map_mul, map_pow, map_ofNat, hA, hB]
  congr 1
  apply Finset.sum_congr rfl
  intro Q _
  rw [show jInvariantKernelX τ (e Q) = σ (jInvariantKernelX τ Q) from
    jInvariantKernelX_galois τ σ Q]

/-- The finite j-expression is covariant, without any continuity assumption on `σ`. -/
theorem jInvariantKernelJ_galois [DecidableEq ℂ] (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (S : Finset (((jInvariantCurve τ).baseChange ℂ).toAffine.Point)) :
    σ (jInvariantKernelJ τ S) =
      jInvariantKernelJ τ
        (S.image (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd) := by
  simp only [jInvariantKernelJ, map_div₀, map_mul, map_sub, map_pow, map_ofNat,
    jInvariantKernelG₂_galois, jInvariantKernelG₃_galois]

/-- Distinct coset representatives give distinct actual normalized curve points. -/
theorem jInvariantPeriodPoint_injOn [DecidableEq ℂ] (τ : UpperHalfPlane) (T : Finset ℂ)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ (standardPeriodPair τ).lattice → s = t) :
    Set.InjOn (jInvariantPeriodPoint τ) T := by
  intro s hs t ht h
  exact hTi s hs t ht ((jInvariantPeriodPoint_eq_iff_sub_mem τ s t).mp h)

/-- Removing infinity from the actual kernel image removes exactly the zero representative. -/
theorem jInvariantPeriodPoint_image_erase [DecidableEq ℂ] (τ : UpperHalfPlane)
    (T : Finset ℂ)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ (standardPeriodPair τ).lattice → s = t)
    (h0 : 0 ∈ T) :
    (T.image (jInvariantPeriodPoint τ)).erase 0 =
      (T.erase 0).image (jInvariantPeriodPoint τ) := by
  classical
  ext Q
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hQ, z, hz, rfl⟩
    exact ⟨z, ⟨fun hz0 => hQ (by simp [hz0]), hz⟩, rfl⟩
  · rintro ⟨z, ⟨hz0, hz⟩, rfl⟩
    refine ⟨?_, z, hz, rfl⟩
    intro h
    exact hz0 (jInvariantPeriodPoint_injOn τ T hTi hz h0
      (h.trans (jInvariantPeriodPoint_zero τ).symm))

/-- The actual finite kernel first-invariant expression is the scaled analytic target invariant. -/
theorem jInvariantKernelG₂_finite_coset_sum [DecidableEq ℂ]
    (τ : UpperHalfPlane) (M : PeriodPair) (T : Finset ℂ)
    (hLM : ((standardPeriodPair τ).lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ (standardPeriodPair τ).lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ (standardPeriodPair τ).lattice)
    (h0 : 0 ∈ T) :
    jInvariantKernelG₂ τ (T.image (jInvariantPeriodPoint τ)) =
      ((jInvariantCurveChange τ).u : ℂ) ^ 4 * M.g₂ := by
  classical
  rw [jInvariantKernelG₂, jInvariantPeriodPoint_image_erase τ T hTi h0,
    Finset.sum_image (fun s hs t ht h =>
      jInvariantPeriodPoint_injOn τ T hTi (Finset.mem_erase.mp hs).2
        (Finset.mem_erase.mp ht).2 h),
    ← jInvariantCurveChange_g₂ τ,
    PeriodPair.g₂_finite_coset_sum (standardPeriodPair τ) M T hLM hTM hTi hcover h0,
    mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr (by ext t; simp)
  intro t _
  rw [jInvariantKernelX_periodPoint]
  ring

/-- The actual finite kernel second-invariant expression is the scaled analytic target invariant. -/
theorem jInvariantKernelG₃_finite_coset_sum [DecidableEq ℂ]
    (τ : UpperHalfPlane) (M : PeriodPair) (T : Finset ℂ)
    (hLM : ((standardPeriodPair τ).lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ (standardPeriodPair τ).lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ (standardPeriodPair τ).lattice)
    (h0 : 0 ∈ T) :
    jInvariantKernelG₃ τ (T.image (jInvariantPeriodPoint τ)) =
      ((jInvariantCurveChange τ).u : ℂ) ^ 6 * M.g₃ := by
  classical
  rw [jInvariantKernelG₃, jInvariantPeriodPoint_image_erase τ T hTi h0,
    Finset.sum_image (fun s hs t ht h =>
      jInvariantPeriodPoint_injOn τ T hTi (Finset.mem_erase.mp hs).2
        (Finset.mem_erase.mp ht).2 h),
    ← jInvariantCurveChange_g₂ τ, ← jInvariantCurveChange_g₃ τ,
    PeriodPair.g₃_finite_coset_sum (standardPeriodPair τ) M T hLM hTM hTi hcover h0,
    mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr (by ext t; simp)
  intro t _
  rw [jInvariantKernelX_periodPoint]
  ring

private theorem weighted_j (u a b : ℂ) (hu : u ≠ 0) :
    1728 * (u ^ 4 * a) ^ 3 / ((u ^ 4 * a) ^ 3 - 27 * (u ^ 6 * b) ^ 2) =
      1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2) := by
  rw [show 1728 * (u ^ 4 * a) ^ 3 = u ^ 12 * (1728 * a ^ 3) by ring,
    show (u ^ 4 * a) ^ 3 - 27 * (u ^ 6 * b) ^ 2 =
      u ^ 12 * (a ^ 3 - 27 * b ^ 2) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 12 hu)]

/-- A genuine finite lattice quotient identifies the finite j-expression with its target period j. -/
theorem jInvariantKernelJ_finite_coset_sum [DecidableEq ℂ]
    (τ : UpperHalfPlane) (M : PeriodPair) (T : Finset ℂ)
    (hLM : ((standardPeriodPair τ).lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ (standardPeriodPair τ).lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ (standardPeriodPair τ).lattice)
    (h0 : 0 ∈ T) :
    jInvariantKernelJ τ (T.image (jInvariantPeriodPoint τ)) =
      1728 * M.g₂ ^ 3 / (M.g₂ ^ 3 - 27 * M.g₃ ^ 2) := by
  rw [jInvariantKernelJ,
    jInvariantKernelG₂_finite_coset_sum τ M T hLM hTM hTi hcover h0,
    jInvariantKernelG₃_finite_coset_sum τ M T hLM hTM hTi hcover h0]
  exact weighted_j _ _ _ (Units.ne_zero _)

/-- For a scaled standard target the actual finite expression has a nonzero discriminant. -/
theorem jInvariantKernel_discriminant_scaled_ne_zero [DecidableEq ℂ]
    (τ ν : UpperHalfPlane) (c : ℂˣ) (T : Finset ℂ)
    (hLM : ((standardPeriodPair τ).lattice : Set ℂ) ⊆
      (scalePeriodPair (standardPeriodPair ν) c).lattice)
    (hTM : ∀ t ∈ T, t ∈ (scalePeriodPair (standardPeriodPair ν) c).lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ (standardPeriodPair τ).lattice → s = t)
    (hcover : ∀ a ∈ (scalePeriodPair (standardPeriodPair ν) c).lattice,
      ∃ t ∈ T, a - t ∈ (standardPeriodPair τ).lattice)
    (h0 : 0 ∈ T) :
    jInvariantKernelG₂ τ (T.image (jInvariantPeriodPoint τ)) ^ 3 -
      27 * jInvariantKernelG₃ τ (T.image (jInvariantPeriodPoint τ)) ^ 2 ≠ 0 := by
  rw [jInvariantKernelG₂_finite_coset_sum τ _ T hLM hTM hTi hcover h0,
    jInvariantKernelG₃_finite_coset_sum τ _ T hLM hTM hTi hcover h0,
    scalePeriodPair_g₂, scalePeriodPair_g₃]
  have heq :
      (((jInvariantCurveChange τ).u : ℂ) ^ 4 *
        (((c : ℂ) ^ 4)⁻¹ * (standardPeriodPair ν).g₂)) ^ 3 -
      27 * (((jInvariantCurveChange τ).u : ℂ) ^ 6 *
        (((c : ℂ) ^ 6)⁻¹ * (standardPeriodPair ν).g₃)) ^ 2 =
      ((jInvariantCurveChange τ).u : ℂ) ^ 12 * (c : ℂ)⁻¹ ^ 12 *
        ((standardPeriodPair ν).g₂ ^ 3 - 27 * (standardPeriodPair ν).g₃ ^ 2) := by
    simp only [inv_pow]
    ring
  rw [heq]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 12 (Units.ne_zero _))
    (pow_ne_zero 12 (inv_ne_zero c.ne_zero)))
    (standardPeriodPair_discriminant_ne_zero ν)

/-- The actual finite-kernel j-expression is the analytic j of any homothetic standard target. -/
theorem jInvariantKernelJ_scaled_target [DecidableEq ℂ]
    (τ ν : UpperHalfPlane) (c : ℂˣ) (T : Finset ℂ)
    (hLM : ((standardPeriodPair τ).lattice : Set ℂ) ⊆
      (scalePeriodPair (standardPeriodPair ν) c).lattice)
    (hTM : ∀ t ∈ T, t ∈ (scalePeriodPair (standardPeriodPair ν) c).lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ (standardPeriodPair τ).lattice → s = t)
    (hcover : ∀ a ∈ (scalePeriodPair (standardPeriodPair ν) c).lattice,
      ∃ t ∈ T, a - t ∈ (standardPeriodPair τ).lattice)
    (h0 : 0 ∈ T) :
    jInvariantKernelJ τ (T.image (jInvariantPeriodPoint τ)) = ModularForm.jInvariant ν := by
  rw [jInvariantKernelJ_finite_coset_sum τ _ T hLM hTM hTi hcover h0,
    scalePeriodPair_g₂, scalePeriodPair_g₃]
  simpa only [inv_pow] using
    (weighted_j (c : ℂ)⁻¹ _ _ (inv_ne_zero c.ne_zero)).trans (standardPeriodPair_j ν)

end BakerHeegnerStark
