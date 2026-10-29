/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Tactic.Ring

/-!
# Real elements of quadratic complex adjunctions

If the square of `u` belongs to a complex subfield `K`, every element of `K(u)`
has the form `a + b*u`, with `a, b ∈ K`. If `K` consists of real elements and
`u` is nonreal, a real element of `K(u)` already belongs to `K`.

The proof uses the integral quadratic to identify the field and algebra
adjunctions, then explicitly reduces algebra expressions to degree at most one.
No CM reciprocity or field-degree hypothesis is used.
-/

open Polynomial
namespace IntermediateField

/-- A quadratic generator gives a linear representation of every adjoined element. -/
theorem exists_eq_add_mul_of_sq_mem (K : IntermediateField ℚ ℂ) {u : ℂ}
    (hu : u ^ 2 ∈ K) {x : ℂ} (hx : x ∈ K⟮u⟯) :
    ∃ a b : K, x = (a : ℂ) + (b : ℂ) * u := by
  let k : K := ⟨u ^ 2, hu⟩
  have hui : IsIntegral K u := by
    refine ⟨X ^ 2 - C k, monic_X_pow_sub_C k (by decide), ?_⟩
    simp [k]
  have hxa : x ∈ Algebra.adjoin K {u} := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hui.isAlgebraic]
    exact hx
  clear hx
  induction hxa using Algebra.adjoin_induction with
  | mem y hy =>
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact ⟨0, 1, by simp⟩
  | algebraMap a => exact ⟨a, 0, by simp⟩
  | add y z hy hz hyp hzp =>
      obtain ⟨a, b, rfl⟩ := hyp
      obtain ⟨c, d, rfl⟩ := hzp
      refine ⟨a + c, b + d, ?_⟩
      push_cast
      ring
  | mul y z hy hz hyp hzp =>
      obtain ⟨a, b, rfl⟩ := hyp
      obtain ⟨c, d, rfl⟩ := hzp
      refine ⟨a * c + b * d * k, a * d + b * c, ?_⟩
      push_cast
      dsimp [k]
      ring

/-- Adjoining a nonreal square root to a real subfield adds no real elements. -/
theorem mem_adjoin_of_im_eq_zero_iff (K : IntermediateField ℚ ℂ)
    (hK : ∀ z ∈ K, Complex.im z = 0) {u : ℂ} (hu : u.im ≠ 0)
    (hu2 : u ^ 2 ∈ K) {x : ℂ} (hx : x.im = 0) :
    x ∈ K⟮u⟯ ↔ x ∈ K := by
  constructor
  · intro hmem
    obtain ⟨a, b, heq⟩ := exists_eq_add_mul_of_sq_mem K hu2 hmem
    have ha : (a : ℂ).im = 0 := hK a a.property
    have hb : (b : ℂ).im = 0 := hK b b.property
    have hbmul : (b : ℂ).re * u.im = 0 := by
      simpa only [Complex.add_im, Complex.mul_im, ha, hb, hx, zero_mul, add_zero,
        zero_add] using (congrArg Complex.im heq).symm
    have hbre : (b : ℂ).re = 0 := (mul_eq_zero.mp hbmul).resolve_right hu
    have hbzero : (b : ℂ) = 0 := Complex.ext hbre hb
    rw [hbzero, zero_mul, add_zero] at heq
    rw [heq]
    exact a.property
  · intro hmem
    exact (K⟮u⟯).algebraMap_mem ⟨x, hmem⟩

/-- A field generated over the rationals by a real number consists of real numbers. -/
theorem im_eq_zero_of_mem_adjoin {u x : ℂ} (hu : u.im = 0) (hx : x ∈ ℚ⟮u⟯) :
    x.im = 0 := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hu
  | algebraMap a => simp
  | add y z hy hz hyp hzp => simp [Complex.add_im, hyp, hzp]
  | inv y hy hyp => simp [Complex.inv_im, hyp]
  | mul y z hy hz hyp hzp => simp [Complex.mul_im, hyp, hzp]

end IntermediateField
