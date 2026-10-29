/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.PeriodLattice.Homothety
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Explicit Quadratic Ideals

For `p ≡ 3 (mod 8)`, the ideals `(4, 1 + √-p)` and `(4, √-p - 1)`
in QNF's quadratic order have product `(4)`. In particular they become
invertible fractional ideals, without assuming that the order is Dedekind.
No correspondence with reduced forms, ideal classes, or CM values is assumed.
-/

open scoped nonZeroDivisors Pointwise

namespace BakerHeegnerStark

/-- Multiplication of an integral ideal by a principal ideal realizes the
corresponding complex homothety of its image. -/
theorem ideal_complex_image_span_singleton_mul {R : Type*} [CommRing R]
    (f : R →ₐ[ℤ] ℂ) (r : R) (I : Ideal R) :
    Submodule.map f.toLinearMap ((Ideal.span {r} * I).restrictScalars ℤ) =
      f r • Submodule.map f.toLinearMap (I.restrictScalars ℤ) := by
  ext z
  rw [Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Ideal.mem_span_singleton_mul.mp hx
    exact ⟨f y, Submodule.mem_map.mpr ⟨y, hy, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨w, hw, hwz⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw
    refine ⟨r * y, Ideal.mem_span_singleton_mul.mpr ⟨y, hy, rfl⟩, ?_⟩
    change f (r * y) = z
    simpa only [smul_eq_mul, AlgHom.toLinearMap_apply, map_mul] using hwz

/-- Equal classes of actual invertible integral ideals have homothetic
complex images under a faithful realization, including for nonmaximal orders. -/
theorem ideal_complex_images_homothetic_of_class_eq {R : Type*} [CommRing R] [IsDomain R]
    (f : R →ₐ[ℤ] ℂ) (hf : Function.Injective f) (A B : Ideal R)
    (I J : (FractionalIdeal R⁰ (FractionRing R))ˣ)
    (hI : (I : FractionalIdeal R⁰ (FractionRing R)) = A)
    (hJ : (J : FractionalIdeal R⁰ (FractionRing R)) = B)
    (hclass : ClassGroup.mk (FractionRing R) I = ClassGroup.mk (FractionRing R) J) :
    ∃ α : ℂ, α ≠ 0 ∧
      α • Submodule.map f.toLinearMap (A.restrictScalars ℤ) =
        Submodule.map f.toLinearMap (B.restrictScalars ℤ) := by
  obtain ⟨r, s, hr, hs, hAB⟩ := (ClassGroup.mk_eq_mk_of_coe_ideal hI hJ).mp hclass
  have hfr : f r ≠ 0 := by
    intro hzero
    apply hr
    apply hf
    simpa only [map_zero] using hzero
  have hfs : f s ≠ 0 := by
    intro hzero
    apply hs
    apply hf
    simpa only [map_zero] using hzero
  have himages := congrArg
    (fun K : Ideal R => Submodule.map f.toLinearMap (K.restrictScalars ℤ)) hAB
  rw [ideal_complex_image_span_singleton_mul, ideal_complex_image_span_singleton_mul] at himages
  refine ⟨(f s)⁻¹ * f r, mul_ne_zero (inv_ne_zero hfs) hfr, ?_⟩
  calc
    _ = (f s)⁻¹ • (f r • Submodule.map f.toLinearMap (A.restrictScalars ℤ)) := by
      rw [smul_smul]
    _ = (f s)⁻¹ • (f s • Submodule.map f.toLinearMap (B.restrictScalars ℤ)) := by
      rw [himages]
    _ = _ := by rw [smul_smul, inv_mul_cancel₀ hfs, one_smul]

/-- Every class has an actual integral ideal representative that is invertible
as a fractional ideal, without assuming that the order is Dedekind. -/
theorem classGroup_exists_integral_invertible_ideal {R : Type*} [CommRing R] [IsDomain R]
    (c : ClassGroup R) :
    ∃ (A : Ideal R) (I : (FractionalIdeal R⁰ (FractionRing R))ˣ),
      (I : FractionalIdeal R⁰ (FractionRing R)) = A ∧
        ClassGroup.mk (FractionRing R) I = c := by
  classical
  refine ClassGroup.induction (FractionRing R) (fun I => ?_) c
  have hunit := FractionalIdeal.isUnit_num.mpr I.isUnit
  refine ⟨(I : FractionalIdeal R⁰ (FractionRing R)).num, hunit.unit,
    hunit.unit_spec, ?_⟩
  symm
  apply ClassGroup.mk_eq_mk.mpr
  have hden : algebraMap R (FractionRing R) (I : FractionalIdeal R⁰ (FractionRing R)).den ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (SetLike.coe_mem _)
  refine ⟨Units.mk0 _ hden, ?_⟩
  apply Units.ext
  rw [Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, hunit.unit_spec, mul_comm]
  exact FractionalIdeal.den_mul_self_eq_num' R⁰ (FractionRing R) I

/-- An actual invertible integral ideal has precisely the original order as
scalar multiplier ring in any faithful complex realization. No Dedekind-domain
hypothesis is needed: cancellation uses its fractional-ideal inverse. -/
theorem ideal_complex_image_multipliers_iff {R : Type*} [CommRing R] [IsDomain R]
    (f : R →ₐ[ℤ] ℂ) (hf : Function.Injective f) (A : Ideal R)
    (I : (FractionalIdeal R⁰ (FractionRing R))ˣ)
    (hI : (I : FractionalIdeal R⁰ (FractionRing R)) = A) (α : ℂ) :
    (∀ z ∈ Submodule.map f.toLinearMap (A.restrictScalars ℤ),
      α * z ∈ Submodule.map f.toLinearMap (A.restrictScalars ℤ)) ↔
      α ∈ f.toRingHom.range := by
  constructor
  · intro h
    have hA : A ≠ ⊥ := by
      intro hz
      apply I.ne_zero
      rw [hI, hz]
      rfl
    obtain ⟨a, ha, ha0⟩ := A.ne_bot_iff.mp hA
    have hfa : f a ≠ 0 := by
      intro hz
      apply ha0
      apply hf
      simpa only [map_zero] using hz
    obtain ⟨b, hb, hba⟩ := Submodule.mem_map.mp
      (h _ (Submodule.mem_map.mpr ⟨a, ha, rfl⟩))
    change f b = α * f a at hba
    have hideal : Ideal.span ({b} : Set R) * A ≤ Ideal.span ({a} : Set R) * A := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Ideal.mem_span_singleton_mul.mp hx
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp
        (h _ (Submodule.mem_map.mpr ⟨y, hy, rfl⟩))
      change f z = α * f y at hzy
      apply Ideal.mem_span_singleton_mul.mpr
      refine ⟨z, hz, hf ?_⟩
      simp only [map_mul]
      rw [hzy, hba]
      ring
    have hmul := (FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing R)).mpr hideal
    simp only [FractionalIdeal.coeIdeal_mul, ← hI] at hmul
    have hcancel := mul_le_mul_left hmul (↑(I⁻¹) : FractionalIdeal R⁰ (FractionRing R))
    have hiinv : (I : FractionalIdeal R⁰ (FractionRing R)) * ↑(I⁻¹) = 1 := I.val_inv
    simp only [mul_assoc, hiinv, mul_one] at hcancel
    have hle : Ideal.span ({b} : Set R) ≤ Ideal.span ({a} : Set R) :=
      (FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing R)).mp hcancel
    have hbmem : b ∈ Ideal.span ({a} : Set R) := hle (Ideal.subset_span (by simp))
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hbmem
    refine ⟨r, ?_⟩
    apply mul_right_cancel₀ hfa
    calc
      f r * f a = f (r * a) := (map_mul f r a).symm
      _ = f b := congrArg f hr
      _ = α * f a := hba
  · rintro ⟨r, rfl⟩ z hz
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
    exact Submodule.mem_map.mpr ⟨r * x, A.mul_mem_left r hx, map_mul f r x⟩

/-- A nonzero complex homothety between actual invertible ideal images
comes from equality of their order-ideal classes. Clearing the scalar uses
one nonzero element of the source ideal, not a presumed CM correspondence. -/
theorem idealClass_eq_of_complex_images_homothetic {R : Type*} [CommRing R] [IsDomain R]
    (f : R →ₐ[ℤ] ℂ) (hf : Function.Injective f) (A B : Ideal R)
    (I J : (FractionalIdeal R⁰ (FractionRing R))ˣ)
    (hI : (I : FractionalIdeal R⁰ (FractionRing R)) = A)
    (hJ : (J : FractionalIdeal R⁰ (FractionRing R)) = B) (α : ℂ) (hα : α ≠ 0)
    (heq : α • Submodule.map f.toLinearMap (A.restrictScalars ℤ) =
      Submodule.map f.toLinearMap (B.restrictScalars ℤ)) :
    ClassGroup.mk (FractionRing R) I = ClassGroup.mk (FractionRing R) J := by
  have hA : A ≠ ⊥ := by
    intro hz
    apply I.ne_zero
    rw [hI, hz]
    rfl
  obtain ⟨a, ha, ha0⟩ := A.ne_bot_iff.mp hA
  have hfa : f a ≠ 0 := by
    intro hz
    apply ha0
    apply hf
    simpa only [map_zero] using hz
  have hαa : α * f a ∈ Submodule.map f.toLinearMap (B.restrictScalars ℤ) := by
    rw [← heq]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_map.mpr ⟨a, ha, rfl⟩)
  obtain ⟨b, hb, hba⟩ := Submodule.mem_map.mp hαa
  change f b = α * f a at hba
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hba
    exact (mul_ne_zero hα hfa) hba.symm
  apply (ClassGroup.mk_eq_mk_of_coe_ideal hI hJ).mpr
  refine ⟨b, a, hb0, ha0, ?_⟩
  ext x
  rw [Ideal.mem_span_singleton_mul, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hαy : α * f y ∈ Submodule.map f.toLinearMap (B.restrictScalars ℤ) := by
      rw [← heq]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hαy
    change f z = α * f y at hzy
    refine ⟨z, hz, hf ?_⟩
    simp only [map_mul]
    rw [hzy, hba]
    ring
  · rintro ⟨z, hz, rfl⟩
    have hzimage : f z ∈ α • Submodule.map f.toLinearMap (A.restrictScalars ℤ) := by
      rw [heq]
      exact Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hzimage
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw
    change α * f y = f z at hwz
    refine ⟨y, hy, hf ?_⟩
    simp only [map_mul]
    rw [hba, ← hwz]
    ring

/-- Faithfully realized invertible integral ideals have the same class
exactly when their complex images are homothetic. -/
theorem ideal_complex_images_homothetic_iff_class_eq {R : Type*} [CommRing R] [IsDomain R]
    (f : R →ₐ[ℤ] ℂ) (hf : Function.Injective f) (A B : Ideal R)
    (I J : (FractionalIdeal R⁰ (FractionRing R))ˣ)
    (hI : (I : FractionalIdeal R⁰ (FractionRing R)) = A)
    (hJ : (J : FractionalIdeal R⁰ (FractionRing R)) = B) :
    (∃ α : ℂ, α ≠ 0 ∧
      α • Submodule.map f.toLinearMap (A.restrictScalars ℤ) =
        Submodule.map f.toLinearMap (B.restrictScalars ℤ)) ↔
    ClassGroup.mk (FractionRing R) I = ClassGroup.mk (FractionRing R) J :=
  ⟨fun ⟨α, hα, heq⟩ =>
      idealClass_eq_of_complex_images_homothetic f hf A B I J hI hJ α hα heq,
    ideal_complex_images_homothetic_of_class_eq f hf A B I J hI hJ⟩

/-- A primitive quadratic relation gives an explicit product of conjugate
ideals generated by four and a shifted root, in any commutative ring. -/
theorem quadratic_ideals_four_mul {R : Type*} [CommRing R] (s : R) (q : ℤ)
    (hs : s ^ 2 = -(8 * (q : R) + 3)) :
    (Ideal.span {4, 1 + s} : Ideal R) * Ideal.span {4, s - 1} = Ideal.span {4} := by
  rw [Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨4, by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨s - 1, by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨1 + s, by ring⟩
    · apply Ideal.mem_span_singleton.mpr
      refine ⟨-(2 * (q : R) + 1), ?_⟩
      linear_combination hs
  · apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    let J : Ideal R := Ideal.span {4 * 4, 4 * (s - 1), (1 + s) * 4, (1 + s) * (s - 1)}
    have hx : (1 + s) * 4 ∈ J := Ideal.subset_span (by simp)
    have hy : 4 * (s - 1) ∈ J := Ideal.subset_span (by simp)
    have hv : (1 + s) * (s - 1) ∈ J := Ideal.subset_span (by simp)
    have hu : (8 : R) ∈ J := by
      convert J.sub_mem hx hy using 1; ring
    have hfour : (4 : R) = -((1 + s) * (s - 1)) - (q : R) * 8 := by
      linear_combination hs
    change (4 : R) ∈ J
    rw [hfour]
    exact J.sub_mem (J.neg_mem hv) (J.mul_mem_left _ hu)

/-- An integral ideal with an explicit product `(4)` is invertible as a
fractional ideal in a characteristic-zero domain. -/
theorem isUnit_fractionalIdeal_of_mul_eq_four {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] (I J : Ideal R) (hIJ : I * J = Ideal.span {4}) :
    IsUnit (I : FractionalIdeal R⁰ (FractionRing R)) := by
  let A : FractionalIdeal R⁰ (FractionRing R) :=
    FractionalIdeal.spanSingleton R⁰ ((4 : FractionRing R)⁻¹) * J
  apply IsUnit.of_mul_eq_one A
  calc
    (I : FractionalIdeal R⁰ (FractionRing R)) * A =
        FractionalIdeal.spanSingleton R⁰ ((4 : FractionRing R)⁻¹) *
          ((I : FractionalIdeal R⁰ (FractionRing R)) * J) := by dsimp [A]; ac_rfl
    _ = FractionalIdeal.spanSingleton R⁰ ((4 : FractionRing R)⁻¹) *
        (Ideal.span {4} : Ideal R) := by rw [← FractionalIdeal.coeIdeal_mul, hIJ]
    _ = 1 := by
      rw [FractionalIdeal.coeIdeal_span_singleton, map_ofNat]
      calc
        _ = FractionalIdeal.spanSingleton R⁰ ((4 : FractionRing R)⁻¹ * 4) :=
          ((FractionalIdeal.spanSingleton R⁰).map_mul _ _).symm
        _ = 1 := by rw [inv_mul_cancel₀ (by norm_num), map_one]

/-- The ideal `(4,1+√-p)` in QNF's quadratic-order model. -/
def sqrtOrderIdeal (p : ℕ) : Ideal (QuadraticNumberFields.Zsqrtd (-(p : ℤ))) :=
  Ideal.span {4, 1 + QuadraticNumberFields.Zsqrtd.sqrtd}

/-- The conjugate ideal, with the sign of the second generator normalized. -/
def sqrtOrderConjugateIdeal (p : ℕ) : Ideal (QuadraticNumberFields.Zsqrtd (-(p : ℤ))) :=
  Ideal.span {4, QuadraticNumberFields.Zsqrtd.sqrtd - 1}

/-- The explicit ideals in the inert residue family have principal product `(4)`. -/
theorem sqrtOrderIdeals_mul (p : ℕ) (hp8 : p % 8 = 3) :
    sqrtOrderIdeal p * sqrtOrderConjugateIdeal p = Ideal.span {4} := by
  have hpq : (p : ℤ) = 8 * ((p / 8 : ℕ) : ℤ) + 3 := by omega
  have hs : (QuadraticNumberFields.Zsqrtd.sqrtd :
      QuadraticNumberFields.Zsqrtd (-(p : ℤ))) ^ 2 =
      -(8 * (((p / 8 : ℕ) : ℤ) : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) + 3) := by
    have hs0 : (QuadraticNumberFields.Zsqrtd.sqrtd :
        QuadraticNumberFields.Zsqrtd (-(p : ℤ))) ^ 2 =
        ((-(p : ℤ) : ℤ) : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) := by
      change QuadraticAlgebra.omega ^ 2 = _
      rw [QuadraticAlgebra.omega_pow_two_eq_add]
      simp [Algebra.smul_def]
    rw [hs0]
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_ofNat] using
      congrArg (fun z : ℤ => ((-z : ℤ) : QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) hpq
  exact quadratic_ideals_four_mul _ ((p / 8 : ℕ) : ℤ) hs

/-- Both explicit ideals are genuinely invertible fractional ideals. -/
theorem sqrtOrderIdeals_isUnit (p : ℕ) (hp8 : p % 8 = 3) :
    IsUnit (sqrtOrderIdeal p : FractionalIdeal
      (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))⁰
      (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))) ∧
    IsUnit (sqrtOrderConjugateIdeal p : FractionalIdeal
      (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))⁰
      (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))) := by
  have hp : 0 < p := by omega
  have : Fact (-(p : ℤ) < 0) := ⟨by omega⟩
  exact ⟨isUnit_fractionalIdeal_of_mul_eq_four _ _ (sqrtOrderIdeals_mul p hp8),
    isUnit_fractionalIdeal_of_mul_eq_four _ _ (by rw [mul_comm, sqrtOrderIdeals_mul p hp8])⟩

/-- Under the quadratic divisibility condition, the two ideal generators
already span the ideal over the integers, not merely over the quadratic ring. -/
theorem mem_quadratic_ideal_four_iff (p : ℕ) (a : ℤ)
    (ha : (4 : ℤ) ∣ (p : ℤ) + a ^ 2)
    (z : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) :
    z ∈ (Ideal.span {4, (a : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) +
      QuadraticNumberFields.Zsqrtd.sqrtd} :
      Ideal (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) ↔
    ∃ m n : ℤ, z = (m : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) * 4 +
      (n : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) *
        ((a : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) +
          QuadraticNumberFields.Zsqrtd.sqrtd) := by
  obtain ⟨q, hq⟩ := ha
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨x.re - a * x.im - q * y.im, 4 * x.im + y.re + a * y.im, ?_⟩
    rw [← hxy]
    apply QuadraticAlgebra.ext
    · simp [smul_eq_mul, QuadraticNumberFields.Zsqrtd.sqrtd, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat]
      linear_combination -y.im * hq
    · simp [smul_eq_mul, QuadraticNumberFields.Zsqrtd.sqrtd, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat]
      ring
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp only [smul_eq_mul]⟩

/-- The complex realization of the explicit quadratic ideal is exactly the
fourfold homothety of the corresponding quarter-period module. -/
theorem quadratic_ideal_four_complex_image (p : ℕ) (a : ℤ)
    (ha : (4 : ℤ) ∣ (p : ℤ) + a ^ 2) :
    Submodule.map (sqrtOrderEmbedding p).toLinearMap
      ((Ideal.span {4, (a : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) +
        QuadraticNumberFields.Zsqrtd.sqrtd} :
        Ideal (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))).restrictScalars ℤ) =
    (4 : ℂ) • periodModule (((a : ℂ) + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 4) := by
  let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
  have hs : sqrtOrderEmbedding p QuadraticNumberFields.Zsqrtd.sqrtd = s := by
    simp [sqrtOrderEmbedding_apply, QuadraticNumberFields.Zsqrtd.sqrtd, s]
  ext z
  rw [Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, n, rfl⟩ := (mem_quadratic_ideal_four_iff p a ha x).mp hx
    refine ⟨(m : ℂ) + (n : ℂ) * (((a : ℂ) + s) / 4),
      (mem_periodModule_iff _ _).mpr ⟨m, n, rfl⟩, ?_⟩
    change (4 : ℂ) * ((m : ℂ) + (n : ℂ) * (((a : ℂ) + s) / 4)) = _
    simp only [AlgHom.toLinearMap_apply, map_add, map_mul, map_intCast, map_ofNat, hs]
    ring
  · rintro ⟨w, hw, hwz⟩
    obtain ⟨m, n, rfl⟩ := (mem_periodModule_iff _ w).mp hw
    refine ⟨(m : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) * 4 +
      (n : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) *
        ((a : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) +
          QuadraticNumberFields.Zsqrtd.sqrtd), ?_, ?_⟩
    · exact (mem_quadratic_ideal_four_iff p a ha _).mpr ⟨m, n, rfl⟩
    · change sqrtOrderEmbedding p _ = z
      simp only [map_add, map_mul, map_intCast, map_ofNat, hs]
      rw [← hwz]
      change (m : ℂ) * 4 + (n : ℂ) * ((a : ℂ) + s) =
        4 * ((m : ℂ) + (n : ℂ) * (((a : ℂ) + s) / 4))
      ring

/-- The two nontrivial explicit ideals realize the two quarter-period lattices
in the inert family, up to the same nonzero homothety by four. -/
theorem sqrtOrderIdeals_complex_image (p : ℕ) (hp8 : p % 8 = 3) :
    let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
    Submodule.map (sqrtOrderEmbedding p).toLinearMap
      ((sqrtOrderIdeal p).restrictScalars ℤ) = (4 : ℂ) • periodModule ((1 + s) / 4) ∧
    Submodule.map (sqrtOrderEmbedding p).toLinearMap
      ((sqrtOrderConjugateIdeal p).restrictScalars ℤ) =
        (4 : ℂ) • periodModule ((3 + s) / 4) := by
  let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
  have hdiv : (4 : ℤ) ∣ (p : ℤ) + 1 := by omega
  constructor
  · simpa only [sqrtOrderIdeal, Int.cast_one] using
      quadratic_ideal_four_complex_image p 1 (by simpa using hdiv)
  · have hm := quadratic_ideal_four_complex_image p (-1) (by simpa using hdiv)
    have hring : ((-1 : ℤ) : QuadraticNumberFields.Zsqrtd (-(p : ℤ))) +
        QuadraticNumberFields.Zsqrtd.sqrtd =
        QuadraticNumberFields.Zsqrtd.sqrtd - 1 := by push_cast; ring
    rw [hring] at hm
    simp only [Int.cast_neg, Int.cast_one] at hm
    change Submodule.map (sqrtOrderEmbedding p).toLinearMap
      ((sqrtOrderConjugateIdeal p).restrictScalars ℤ) =
        (4 : ℂ) • periodModule (((-1 : ℂ) + s) / 4) at hm
    have hperiod : periodModule (((-1 : ℂ) + s) / 4) =
        periodModule ((3 + s) / 4) := by
      have heq : (3 + s) / 4 = (1 : ℂ) + ((-1 + s) / 4) := by ring
      rw [heq]
      simpa only [Int.cast_one] using
        (periodModule_add_int (((-1 : ℂ) + s) / 4) 1).symm
    rwa [hperiod] at hm

/-- Each explicitly realized ideal is proper: its scalar multipliers are
exactly the realized quadratic order, not a larger ring. -/
theorem sqrtOrderIdeals_complex_multipliers (p : ℕ) (hp8 : p % 8 = 3) (α : ℂ) :
    let I := Submodule.map (sqrtOrderEmbedding p).toLinearMap
      ((sqrtOrderIdeal p).restrictScalars ℤ)
    let J := Submodule.map (sqrtOrderEmbedding p).toLinearMap
      ((sqrtOrderConjugateIdeal p).restrictScalars ℤ)
    ((∀ z ∈ I, α * z ∈ I) ↔ α ∈ (sqrtOrderEmbedding p).toRingHom.range) ∧
    ((∀ z ∈ J, α * z ∈ J) ↔ α ∈ (sqrtOrderEmbedding p).toRingHom.range) := by
  dsimp only
  rw [(sqrtOrderIdeals_complex_image p hp8).1, (sqrtOrderIdeals_complex_image p hp8).2,
    mul_preserves_smul_iff _ 4 α (by norm_num),
    mul_preserves_smul_iff _ 4 α (by norm_num)]
  exact ⟨(inert_periodModule_multipliers p hp8 α).2.1,
    (inert_periodModule_multipliers p hp8 α).2.2⟩

/-- The unit ideal realizes the square-root period module itself. -/
theorem sqrtOrder_top_complex_image (p : ℕ) :
    Submodule.map (sqrtOrderEmbedding p).toLinearMap
      ((⊤ : Ideal (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))).restrictScalars ℤ) =
      periodModule ((Real.sqrt (p : ℝ) : ℂ) * Complex.I) := by
  ext z
  rw [Submodule.mem_map, ← mem_sqrtOrderEmbedding_range_iff]
  simp

end BakerHeegnerStark
