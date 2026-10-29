/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Orders.Ideals
import BakerHeegnerStark.ModularForms.JInvariant.Basic
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The Modular Invariant of a Period Lattice

Complex homothety of upper-half-plane period lattices is equivalent to the
parameters lying in the same integral modular-group orbit. Consequently `j`
is independent of such a period basis. The converse, from equal `j`-values to
homothety, is proved separately by Weierstrass uniqueness in `ComplexMultiplication/JInvariant/Separation.lean`.
Arithmetic properties of CM values are not assumed.
-/

open scoped Pointwise MatrixGroups nonZeroDivisors

namespace BakerHeegnerStark

/-- A modular transformation changes the period lattice by the nonzero
complex homothety given by its denominator. -/
theorem modular_denom_smul_periodModule (g : SL(2, ℤ)) (σ : UpperHalfPlane) :
    let α : ℂ := (g 1 0 : ℂ) * (σ : ℂ) + (g 1 1 : ℂ)
    α ≠ 0 ∧ α • periodModule (g • σ : UpperHalfPlane) = periodModule σ := by
  let α : ℂ := (g 1 0 : ℂ) * (σ : ℂ) + (g 1 1 : ℂ)
  have hformula : (g • σ : UpperHalfPlane) =
      (((g 0 0 : ℂ) * (σ : ℂ) + (g 0 1 : ℂ)) / α : ℂ) := by
    simpa [α] using UpperHalfPlane.coe_specialLinearGroup_apply g σ
  have hα : α ≠ 0 := by
    intro hzero
    have hz : ((g • σ : UpperHalfPlane) : ℂ) = 0 := by simpa [hzero] using hformula
    have him := (g • σ : UpperHalfPlane).im_pos
    change 0 < ((g • σ : UpperHalfPlane) : ℂ).im at him
    rw [hz, Complex.zero_im] at him
    exact (lt_irrefl 0) him
  refine ⟨hα, (smul_periodModule_eq_iff_of_im_pos _ _ _
    (g • σ : UpperHalfPlane).im_pos σ.im_pos).mpr ?_⟩
  refine ⟨g 1 1, g 1 0, g 0 1, g 0 0, ?_, ?_, ?_⟩
  · have hd := g.property
    rw [Matrix.det_fin_two] at hd
    nlinarith
  · ring
  · change α * ((g • σ : UpperHalfPlane) : ℂ) = _
    rw [hformula]
    calc
      _ = (g 0 0 : ℂ) * (σ : ℂ) + (g 0 1 : ℂ) := mul_div_cancel₀ _ hα
      _ = _ := by ring

/-- Homothetic upper-half-plane period lattices have parameters in the same
integral modular-group orbit, and conversely. -/
theorem periodModule_homothety_iff_modularOrbit (τ σ : UpperHalfPlane) :
    (∃ α : ℂ, α ≠ 0 ∧ α • periodModule τ = periodModule σ) ↔
      ∃ g : SL(2, ℤ), g • σ = τ := by
  constructor
  · rintro ⟨α, hα, heq⟩
    obtain ⟨a, b, c, d, hd, ha, hc⟩ :=
      (smul_periodModule_eq_iff_of_im_pos τ σ α τ.im_pos σ.im_pos).mp heq
    let g : SL(2, ℤ) := ⟨!![d, c; b, a], by simp [Matrix.det_fin_two]; nlinarith [hd]⟩
    refine ⟨g, ?_⟩
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    change (((d : ℝ) : ℂ) * (σ : ℂ) + ((c : ℝ) : ℂ)) /
      (((b : ℝ) : ℂ) * (σ : ℂ) + ((a : ℝ) : ℂ)) = (τ : ℂ)
    simp only [Complex.ofReal_intCast]
    have hden : (b : ℂ) * (σ : ℂ) + (a : ℂ) = α := by rw [ha]; ring
    rw [hden]
    apply (div_eq_iff hα).mpr
    linear_combination -hc
  · rintro ⟨g, rfl⟩
    exact ⟨_, modular_denom_smul_periodModule g σ⟩

/-- The analytic modular invariant depends only on the complex homothety
class of a period lattice. The converse is proved in `ComplexMultiplication/JInvariant/Separation.lean`. -/
theorem jInvariant_eq_of_periodModule_homothety (τ σ : UpperHalfPlane) (α : ℂ)
    (hα : α ≠ 0) (heq : α • periodModule τ = periodModule σ) :
    ModularForm.jInvariant τ = ModularForm.jInvariant σ := by
  obtain ⟨g, rfl⟩ := (periodModule_homothety_iff_modularOrbit τ σ).mp ⟨α, hα, heq⟩
  exact ModularForm.jInvariant_smul g σ

/-- Equality after two nonzero period normalizations also identifies the
analytic modular invariants. -/
theorem jInvariant_eq_of_scaled_periodModules (τ σ : UpperHalfPlane) (a b : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (heq : a • periodModule τ = b • periodModule σ) :
    ModularForm.jInvariant τ = ModularForm.jInvariant σ := by
  apply jInvariant_eq_of_periodModule_homothety τ σ (b⁻¹ * a)
    (mul_ne_zero (inv_ne_zero hb) ha)
  calc
    (b⁻¹ * a) • periodModule τ = b⁻¹ • (a • periodModule τ) := by rw [smul_smul]
    _ = b⁻¹ • (b • periodModule σ) := by rw [heq]
    _ = periodModule σ := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]

/-- For faithfully realized invertible integral ideals, equality of order-ideal
classes is equivalent to modular equivalence of their displayed period bases.
The two complex normalizing factors may be different, but must be nonzero. -/
theorem modularOrbit_iff_idealClass_eq {R : Type*} [CommRing R] [IsDomain R]
    (f : R →ₐ[ℤ] ℂ) (hf : Function.Injective f) (A B : Ideal R)
    (I J : (FractionalIdeal R⁰ (FractionRing R))ˣ)
    (hI : (I : FractionalIdeal R⁰ (FractionRing R)) = A)
    (hJ : (J : FractionalIdeal R⁰ (FractionRing R)) = B)
    (τ σ : UpperHalfPlane) (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hA : Submodule.map f.toLinearMap (A.restrictScalars ℤ) = c • periodModule τ)
    (hB : Submodule.map f.toLinearMap (B.restrictScalars ℤ) = d • periodModule σ) :
    (∃ g : SL(2, ℤ), g • σ = τ) ↔
      ClassGroup.mk (FractionRing R) I = ClassGroup.mk (FractionRing R) J := by
  constructor
  · intro horbit
    obtain ⟨β, hβ, heq⟩ := (periodModule_homothety_iff_modularOrbit τ σ).mpr horbit
    apply idealClass_eq_of_complex_images_homothetic f hf A B I J hI hJ (d * β * c⁻¹)
      (mul_ne_zero (mul_ne_zero hd hβ) (inv_ne_zero hc))
    have hscale : d * β * c⁻¹ * c = d * β := by
      rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
    calc
      _ = (d * β * c⁻¹ * c) • periodModule τ := by rw [hA, smul_smul]
      _ = d • (β • periodModule τ) := by rw [hscale, smul_smul]
      _ = _ := by rw [heq, hB]
  · intro hclass
    obtain ⟨α, hα, heq⟩ :=
      ideal_complex_images_homothetic_of_class_eq f hf A B I J hI hJ hclass
    rw [hA, hB, smul_smul] at heq
    apply (periodModule_homothety_iff_modularOrbit τ σ).mp
    refine ⟨d⁻¹ * (α * c), mul_ne_zero (inv_ne_zero hd) (mul_ne_zero hα hc), ?_⟩
    calc
      _ = d⁻¹ • ((α * c) • periodModule τ) := by rw [smul_smul]
      _ = d⁻¹ • (d • periodModule σ) := by rw [heq]
      _ = _ := by rw [smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- Equal classes of actual invertible ideals give equal analytic `j`-values
when their complex realizations are period lattices. This works for a
nonmaximal order: no Dedekind-domain assumption is used. The lattice
realizations are explicit hypotheses, not a CM arithmetic assertion. -/
theorem jInvariant_eq_of_idealClass_eq {R : Type*} [CommRing R] [IsDomain R]
    (f : R →ₐ[ℤ] ℂ) (hf : Function.Injective f) (A B : Ideal R)
    (I J : (FractionalIdeal R⁰ (FractionRing R))ˣ)
    (hI : (I : FractionalIdeal R⁰ (FractionRing R)) = A)
    (hJ : (J : FractionalIdeal R⁰ (FractionRing R)) = B)
    (hclass : ClassGroup.mk (FractionRing R) I = ClassGroup.mk (FractionRing R) J)
    (τ σ : UpperHalfPlane) (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hA : Submodule.map f.toLinearMap (A.restrictScalars ℤ) = c • periodModule τ)
    (hB : Submodule.map f.toLinearMap (B.restrictScalars ℤ) = d • periodModule σ) :
    ModularForm.jInvariant τ = ModularForm.jInvariant σ := by
  obtain ⟨α, hα, heq⟩ :=
    ideal_complex_images_homothetic_of_class_eq f hf A B I J hI hJ hclass
  rw [hA, hB, smul_smul] at heq
  exact jInvariant_eq_of_scaled_periodModules τ σ (α * c) d (mul_ne_zero hα hc) hd heq

/-- For the actual two invertible ideals constructed in the inert family,
equality of their order-ideal classes implies equality of the corresponding
quarter-period `j`-values. The class equality is an explicit hypothesis. -/
theorem jInvariant_quarter_eq_of_sqrtOrderClass_eq (p : ℕ) (hp8 : p % 8 = 3)
    [Fact (-(p : ℤ) < 0)]
    (hclass : ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
        (sqrtOrderIdeals_isUnit p hp8).1.unit =
      ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
        (sqrtOrderIdeals_isUnit p hp8).2.unit) :
    let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
    ModularForm.jInvariant (UpperHalfPlane.ofComplex ((1 + s) / 4)) =
      ModularForm.jInvariant (UpperHalfPlane.ofComplex ((3 + s) / 4)) := by
  let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
  let τ := UpperHalfPlane.ofComplex ((1 + s) / 4)
  let σ := UpperHalfPlane.ofComplex ((3 + s) / 4)
  have hp : 0 < p := by omega
  have hs : 0 < s.im := by
    simpa [s] using Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp : (0 : ℝ) < (p : ℝ))
  have hτ : (τ : ℂ) = (1 + s) / 4 :=
    congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos (by
      simpa using div_pos hs (by norm_num : (0 : ℝ) < 4)))
  have hσ : (σ : ℂ) = (3 + s) / 4 :=
    congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos (by
      simpa using div_pos hs (by norm_num : (0 : ℝ) < 4)))
  refine jInvariant_eq_of_idealClass_eq (sqrtOrderEmbedding p)
    (sqrtOrderEmbedding_injective p hp) (sqrtOrderIdeal p) (sqrtOrderConjugateIdeal p)
    _ _ (sqrtOrderIdeals_isUnit p hp8).1.unit_spec
    (sqrtOrderIdeals_isUnit p hp8).2.unit_spec hclass τ σ 4 4 (by norm_num) (by norm_num)
    ?_ ?_
  · rw [hτ]
    exact (sqrtOrderIdeals_complex_image p hp8).1
  · rw [hσ]
    exact (sqrtOrderIdeals_complex_image p hp8).2

end BakerHeegnerStark
