/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Orders.IntegerLattice
import BakerHeegnerStark.ComplexMultiplication.Orders.Ideals
import BakerHeegnerStark.ComplexMultiplication.Orders.ConductorTwoLattices
import QNFMathlib.RingTheory.Ideal.Maps

/-!
# Conductor-Two Normalization of Actual Ideals

A conductor element carries an extended ideal back into the original ideal's
actual image. If the larger order is principal, a generator of that extension
normalizes its complex image into the conductor interval. The specialization
uses QNF's actual half-integer order and the genuine field-class-number-one
hypothesis, not an assumed list of small-order classes.
-/

namespace BakerHeegnerStark

open scoped Pointwise nonZeroDivisors

/-- A principal extension normalizes every nonzero integral ideal image into
the actual conductor interval in the complex plane. -/
theorem ideal_complex_image_normalization {R S : Type*} [CommRing R] [CommRing S]
    [IsPrincipalIdealRing S] (j : R →ₐ[ℤ] S) (g : S →ₐ[ℤ] ℂ)
    (hj : Function.Injective j) (hg : Function.Injective g)
    (c : S) (hc : ∀ s : S, c * s ∈ j.toRingHom.range)
    (A : Ideal R) (hA : A ≠ ⊥) :
    ∃ α : ℂ, α ≠ 0 ∧
      g c • Submodule.map g.toLinearMap (⊤ : Submodule ℤ S) ≤
        α • Submodule.map (g.comp j).toLinearMap (A.restrictScalars ℤ) ∧
      α • Submodule.map (g.comp j).toLinearMap (A.restrictScalars ℤ) ≤
        Submodule.map g.toLinearMap (⊤ : Submodule ℤ S) := by
  let B := Ideal.map j.toRingHom A
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal B
  obtain ⟨x, hx, hx0⟩ := A.ne_bot_iff.mp hA
  have ha0 : a ≠ 0 := by
    intro h0
    have hm : j x ∈ B := Ideal.mem_map_of_mem j.toRingHom hx
    rw [ha, h0] at hm
    have hjx : j x = 0 := by simpa using hm
    apply hx0
    apply hj
    simpa only [map_zero] using hjx
  have hga : g a ≠ 0 := by
    intro h0
    apply ha0
    apply hg
    simpa only [map_zero] using h0
  have haB : a ∈ B := by
    rw [ha]
    exact Ideal.subset_span (by simp)
  refine ⟨(g a)⁻¹, inv_ne_zero hga, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨r, hr, her⟩ := Ideal.conductor_mul_mem_map j.toRingHom c hc A (a * t)
      (B.mul_mem_right t haB)
    change j r = c * (a * t) at her
    apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    refine ⟨(g.comp j) r, Submodule.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    change (g a)⁻¹ * g (j r) = g c * g t
    rw [her, map_mul, map_mul]
    field_simp [hga]
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
    obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hw
    have hrB : j r ∈ B := Ideal.mem_map_of_mem j.toRingHom hr
    rw [ha] at hrB
    obtain ⟨t, het⟩ := Ideal.mem_span_singleton'.mp hrB
    apply Submodule.mem_map.mpr
    refine ⟨t, by simp, ?_⟩
    change g t = (g a)⁻¹ * g (j r)
    rw [← het, map_mul]
    field_simp [hga]

/-- Field class number one normalizes every nonzero actual square-root-order
ideal image between twice the full integer-ring lattice and that lattice. -/
theorem sqrtOrderIdeal_complex_image_normalization (p : ℕ) (k : ℤ)
    [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)]
    (hk : -(p : ℤ) = 1 + 4 * k)
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1)
    (A : Ideal (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))) (hA : A ≠ ⊥) :
    ∃ α : ℂ, α ≠ 0 ∧
      (2 : ℂ) • periodModule ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2) ≤
        α • Submodule.map (sqrtOrderEmbedding p).toLinearMap (A.restrictScalars ℤ) ∧
      α • Submodule.map (sqrtOrderEmbedding p).toLinearMap (A.restrictScalars ℤ) ≤
        periodModule ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2) := by
  have := halfOrder_isPrincipalIdealRing_of_classNumber_eq_one p k hk hclass
  let j := ZOnePlusSqrtdOverTwo.fromZsqrtd k hk
  let g := halfOrderEmbedding p k hk
  have hc : ∀ s : ZOnePlusSqrtdOverTwo k, (2 : ZOnePlusSqrtdOverTwo k) * s ∈
      j.toRingHom.range := by
    change ∀ s, (2 : ZOnePlusSqrtdOverTwo k) * s ∈
      (ZOnePlusSqrtdOverTwo.fromZsqrtd k hk).range
    rw [ZOnePlusSqrtdOverTwo.range_fromZsqrtd, ← mem_conductor_iff,
      ZOnePlusSqrtdOverTwo.conductor_eq_span_two]
    exact Ideal.subset_span (by simp)
  have hcomp : g.comp j = sqrtOrderEmbedding p :=
    AlgHom.ext fun x => halfOrderEmbedding_comp_fromZsqrtd p k hk x
  have hlarge : Submodule.map g.toLinearMap (⊤ : Submodule ℤ (ZOnePlusSqrtdOverTwo k)) =
      periodModule ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
      exact (mem_halfOrderEmbedding_range_iff p k hk _).mp ⟨x, rfl⟩
    · intro hz
      obtain ⟨x, hx⟩ := (mem_halfOrderEmbedding_range_iff p k hk _).mpr hz
      exact Submodule.mem_map.mpr ⟨x, by simp, hx⟩
  obtain ⟨α, hα, hlo, hhi⟩ := ideal_complex_image_normalization j g
    (ZOnePlusSqrtdOverTwo.fromZsqrtd_injective k hk) (halfOrderEmbedding_injective p k hk)
    2 hc A hA
  refine ⟨α, hα, ?_, ?_⟩
  · simpa only [map_ofNat, hlarge, hcomp] using hlo
  · simpa only [hlarge, hcomp] using hhi

/-- Every actual invertible integral small-order ideal has one of the three
displayed normalized period lattices when the field class number is one. -/
theorem sqrtOrderIdeal_complex_image_three_cases (p : ℕ) (k : ℤ)
    [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)]
    (hk : -(p : ℤ) = 1 + 4 * k)
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1)
    (A : Ideal (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))
    (I : (FractionalIdeal (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))⁰
      (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))))ˣ)
    (hI : (I : FractionalIdeal (QuadraticNumberFields.Zsqrtd (-(p : ℤ)))⁰
      (FractionRing (QuadraticNumberFields.Zsqrtd (-(p : ℤ))))) = A) :
    let s := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
    ∃ α : ℂ, α ≠ 0 ∧
      (α • Submodule.map (sqrtOrderEmbedding p).toLinearMap (A.restrictScalars ℤ) =
          periodModule s ∨
        α • Submodule.map (sqrtOrderEmbedding p).toLinearMap (A.restrictScalars ℤ) =
          (2 : ℂ) • periodModule ((1 + s) / 4) ∨
        α • Submodule.map (sqrtOrderEmbedding p).toLinearMap (A.restrictScalars ℤ) =
          (2 : ℂ) • periodModule ((3 + s) / 4)) := by
  dsimp only
  have : Fact (-(p : ℤ) < 0) := ⟨by omega⟩
  have hA : A ≠ ⊥ := by
    intro hz
    apply I.ne_zero
    rw [hI, hz]
    rfl
  obtain ⟨α, hα, hlo, hhi⟩ := sqrtOrderIdeal_complex_image_normalization p k hk hclass A hA
  refine ⟨α, hα, sqrtOrder_conductor_two_periodModule_cases p k hk
    (α • Submodule.map (sqrtOrderEmbedding p).toLinearMap (A.restrictScalars ℤ)) hlo hhi ?_⟩
  intro β
  exact (mul_preserves_smul_iff _ α β hα).trans
    (ideal_complex_image_multipliers_iff (sqrtOrderEmbedding p)
      (sqrtOrderEmbedding_injective p (by omega)) A I hI β)

end BakerHeegnerStark
