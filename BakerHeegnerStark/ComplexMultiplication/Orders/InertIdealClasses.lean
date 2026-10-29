/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Orders.InertLattices
import BakerHeegnerStark.ComplexMultiplication.Orders.ConductorTwoIdeals

/-!
# Ideal Classes in the Inert Family

The two explicit invertible ideals in `ℤ[√-p]` and the unit ideal give three
distinct classes for `p ≡ 3 (mod 8)` and `p > 3`. The proof uses their actual
complex lattice realizations and the elementary nonhomothety theorems.
Under squarefreeness and field class number one, principal extension to the
actual maximal order normalizes every invertible ideal into the conductor-two
interval. Its three proper modules then exhaust the actual order classes.
-/

open scoped Pointwise nonZeroDivisors

namespace BakerHeegnerStark

private theorem sqrtOrderClass_ne_one_of_quarter_image (p : ℕ) (hp : 4 < p) (k : ℤ)
    [Fact (-(p : ℤ) < 0)] (A : Ideal (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
    (I : (FractionalIdeal (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))⁰
      (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))))ˣ)
    (hI : (I : FractionalIdeal (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))⁰
      (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))) = A)
    (himage : Submodule.map (sqrtOrderEmbedding p).toLinearMap (A.restrictScalars ℤ) =
      (4 : ℂ) • periodModule (((k : ℂ) + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 4)) :
    ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) I ≠ 1 := by
  intro hclass
  have hclass' : ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) 1 =
      ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) I := by
    simpa only [map_one] using hclass.symm
  obtain ⟨α, _, heq⟩ := ideal_complex_images_homothetic_of_class_eq (sqrtOrderEmbedding p)
    (sqrtOrderEmbedding_injective p (by omega)) ⊤ A 1 I (by simp) hI hclass'
  rw [sqrtOrder_top_complex_image, himage] at heq
  apply sqrt_periodModule_not_homothetic_quarter p hp k
  refine ⟨(4 : ℂ)⁻¹ * α, ?_⟩
  calc
    _ = (4 : ℂ)⁻¹ • (α • periodModule ((Real.sqrt (p : ℝ) : ℂ) * Complex.I)) := by
      rw [smul_smul]
    _ = (4 : ℂ)⁻¹ • ((4 : ℂ) • periodModule
        (((k : ℂ) + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 4)) := by rw [heq]
    _ = _ := by norm_num [smul_smul]

/-- The unit ideal and the two explicit invertible quadratic ideals represent
three different classes of the actual nonmaximal-order class group. -/
theorem inert_sqrtOrderClasses_distinct (p : ℕ) (hp8 : p % 8 = 3) (hp3 : 3 < p)
    [Fact (-(p : ℤ) < 0)] :
    let I := (sqrtOrderIdeals_isUnit p hp8).1.unit
    let J := (sqrtOrderIdeals_isUnit p hp8).2.unit
    ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) I ≠ 1 ∧
    ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) J ≠ 1 ∧
    ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) I ≠
      ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) J := by
  dsimp only
  have hp4 : 4 < p := by omega
  refine ⟨?_, ?_, ?_⟩
  · apply sqrtOrderClass_ne_one_of_quarter_image p hp4 1 (sqrtOrderIdeal p)
      (sqrtOrderIdeals_isUnit p hp8).1.unit (sqrtOrderIdeals_isUnit p hp8).1.unit_spec
    simpa only [Int.cast_one] using (sqrtOrderIdeals_complex_image p hp8).1
  · apply sqrtOrderClass_ne_one_of_quarter_image p hp4 3 (sqrtOrderConjugateIdeal p)
      (sqrtOrderIdeals_isUnit p hp8).2.unit (sqrtOrderIdeals_isUnit p hp8).2.unit_spec
    simpa only [Int.cast_ofNat] using (sqrtOrderIdeals_complex_image p hp8).2
  · intro hclass
    obtain ⟨α, _, heq⟩ := ideal_complex_images_homothetic_of_class_eq (sqrtOrderEmbedding p)
      (sqrtOrderEmbedding_injective p (by omega)) (sqrtOrderIdeal p) (sqrtOrderConjugateIdeal p)
      _ _ (sqrtOrderIdeals_isUnit p hp8).1.unit_spec (sqrtOrderIdeals_isUnit p hp8).2.unit_spec
      hclass
    rw [(sqrtOrderIdeals_complex_image p hp8).1, (sqrtOrderIdeals_complex_image p hp8).2] at heq
    apply inert_quarter_periodModules_not_homothetic p hp8 hp3
    refine ⟨α, ?_⟩
    have hscaled := congrArg (fun L : Submodule ℤ ℂ => (4 : ℂ)⁻¹ • L) heq
    have hcancel : (4 : ℂ)⁻¹ * (α * 4) = α := by ring
    simpa only [smul_smul, hcancel, inv_mul_cancel₀ (by norm_num : (4 : ℂ) ≠ 0), one_smul]
      using hscaled

/-- The two explicit order-ideal classes are inverse to one another, as
follows from their actual principal ideal product, without a Dedekind assumption. -/
theorem sqrtOrderClasses_mul (p : ℕ) (hp8 : p % 8 = 3) [Fact (-(p : ℤ) < 0)] :
    ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
        (sqrtOrderIdeals_isUnit p hp8).1.unit *
      ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
        (sqrtOrderIdeals_isUnit p hp8).2.unit = 1 := by
  let R := QuadraticNumberFields.Zsqrtd (-(p : ℤ))
  let I := (sqrtOrderIdeals_isUnit p hp8).1.unit
  let J := (sqrtOrderIdeals_isUnit p hp8).2.unit
  change ClassGroup.mk (FractionRing R) I * ClassGroup.mk (FractionRing R) J = 1
  have hI : (I : FractionalIdeal R⁰ (FractionRing R)) = sqrtOrderIdeal p :=
    (sqrtOrderIdeals_isUnit p hp8).1.unit_spec
  have hJ : (J : FractionalIdeal R⁰ (FractionRing R)) = sqrtOrderConjugateIdeal p :=
    (sqrtOrderIdeals_isUnit p hp8).2.unit_spec
  have hIJ : ((I * J : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
      FractionalIdeal R⁰ (FractionRing R)) = (Ideal.span {4} : Ideal R) := by
    rw [Units.val_mul, hI, hJ, ← FractionalIdeal.coeIdeal_mul, sqrtOrderIdeals_mul p hp8]
  rw [← map_mul, ClassGroup.mk_eq_one_iff]
  change (((I * J : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    FractionalIdeal R⁰ (FractionRing R)) : Submodule R (FractionRing R)).IsPrincipal
  rw [hIJ, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_, rfl⟩⟩

/-- The nontrivial explicit class in the nonexceptional inert family is not
two-torsion. This does not assert that its order is exactly three. -/
theorem inert_sqrtOrderClass_sq_ne_one (p : ℕ) (hp8 : p % 8 = 3) (hp3 : 3 < p)
    [Fact (-(p : ℤ) < 0)] :
    (ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
      (sqrtOrderIdeals_isUnit p hp8).1.unit) ^ 2 ≠ 1 := by
  intro hsq
  have hmul := sqrtOrderClasses_mul p hp8
  have hsq' :
      ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
          (sqrtOrderIdeals_isUnit p hp8).1.unit *
        ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
          (sqrtOrderIdeals_isUnit p hp8).1.unit = 1 := by
    simpa only [pow_two] using hsq
  exact (inert_sqrtOrderClasses_distinct p hp8 hp3).2.2 (mul_left_cancel (hsq'.trans hmul.symm))

/-- Under field class number one, the unit class and the two explicit
invertible ideals exhaust the actual conductor-two order class group. -/
theorem inert_sqrtOrderClasses_exhaustive (p : ℕ) (hp8 : p % 8 = 3)
    [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)] [Fact (-(p : ℤ) < 0)]
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1)
    (c : ClassGroup (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) :
    c = 1 ∨
      c = ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
        (sqrtOrderIdeals_isUnit p hp8).1.unit ∨
      c = ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
        (sqrtOrderIdeals_isUnit p hp8).2.unit := by
  obtain ⟨A, I, hI, hc⟩ := classGroup_exists_integral_invertible_ideal c
  rw [← hc]
  let k : ℤ := (-(p : ℤ) - 1) / 4
  have hk : -(p : ℤ) = 1 + 4 * k := by dsimp only [k]; omega
  let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
  obtain ⟨α, hα, heq | heq | heq⟩ :=
    sqrtOrderIdeal_complex_image_three_cases p k hk hclass A I hI
  · left
    simpa only [map_one] using
      idealClass_eq_of_complex_images_homothetic (sqrtOrderEmbedding p)
        (sqrtOrderEmbedding_injective p (by omega)) A ⊤ I 1 hI (by simp) α hα
        (heq.trans (sqrtOrder_top_complex_image p).symm)
  · right; left
    apply idealClass_eq_of_complex_images_homothetic (sqrtOrderEmbedding p)
      (sqrtOrderEmbedding_injective p (by omega)) A (sqrtOrderIdeal p) I _
      hI (sqrtOrderIdeals_isUnit p hp8).1.unit_spec (2 * α)
      (mul_ne_zero (by norm_num) hα)
    calc
      (2 * α) • Submodule.map (sqrtOrderEmbedding p).toLinearMap (A.restrictScalars ℤ) =
          (2 : ℂ) • (α • Submodule.map (sqrtOrderEmbedding p).toLinearMap
            (A.restrictScalars ℤ)) := by rw [smul_smul]
      _ = (2 : ℂ) • ((2 : ℂ) • periodModule ((1 + s) / 4)) := by rw [heq]
      _ = (4 : ℂ) • periodModule ((1 + s) / 4) := by norm_num [smul_smul]
      _ = Submodule.map (sqrtOrderEmbedding p).toLinearMap
          ((sqrtOrderIdeal p).restrictScalars ℤ) := (sqrtOrderIdeals_complex_image p hp8).1.symm
  · right; right
    apply idealClass_eq_of_complex_images_homothetic (sqrtOrderEmbedding p)
      (sqrtOrderEmbedding_injective p (by omega)) A (sqrtOrderConjugateIdeal p) I _
      hI (sqrtOrderIdeals_isUnit p hp8).2.unit_spec (2 * α)
      (mul_ne_zero (by norm_num) hα)
    calc
      (2 * α) • Submodule.map (sqrtOrderEmbedding p).toLinearMap (A.restrictScalars ℤ) =
          (2 : ℂ) • (α • Submodule.map (sqrtOrderEmbedding p).toLinearMap
            (A.restrictScalars ℤ)) := by rw [smul_smul]
      _ = (2 : ℂ) • ((2 : ℂ) • periodModule ((3 + s) / 4)) := by rw [heq]
      _ = (4 : ℂ) • periodModule ((3 + s) / 4) := by norm_num [smul_smul]
      _ = Submodule.map (sqrtOrderEmbedding p).toLinearMap
          ((sqrtOrderConjugateIdeal p).restrictScalars ℤ) :=
        (sqrtOrderIdeals_complex_image p hp8).2.symm

/-- The conductor-two square-root order has exactly three actual ideal classes
in the nonexceptional inert family when the field class number is one. -/
theorem inert_sqrtOrderClassGroup_card (p : ℕ) (hp8 : p % 8 = 3) (hp3 : 3 < p)
    [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)] [Fact (-(p : ℤ) < 0)]
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1) :
    Nat.card (ClassGroup (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) = 3 := by
  classical
  let a := ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
    (sqrtOrderIdeals_isUnit p hp8).1.unit
  let b := ClassGroup.mk (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
    (sqrtOrderIdeals_isUnit p hp8).2.unit
  let f : Fin 3 → ClassGroup (QuadraticNumberFields.Zsqrtd (-(p : ℤ))) := ![1, a, b]
  obtain ⟨ha, hb, hab⟩ := inert_sqrtOrderClasses_distinct p hp8 hp3
  have hinj : Function.Injective f := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [f, a, b]
  have hsurj : Function.Surjective f := by
    intro c
    rcases inert_sqrtOrderClasses_exhaustive p hp8 hclass c with h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
  calc
    Nat.card (ClassGroup (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) =
        Nat.card (Fin 3) := (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
    _ = 3 := by simp

end BakerHeegnerStark
