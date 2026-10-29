/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Orders.HalfIntegral
import QuadraticNumberFields.RingOfIntegers.Basis
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The Actual Quadratic Integer Period Lattice

The normalized complex embedding sends `√-p` to `i√p`. QNF's proved
ring-of-integers classification and integral basis then identify the image
of the actual full ring of integers with `ℤ+ℤ(1+i√p)/2` in the squarefree
half-integer branch. This is a lattice/order correspondence, not a theorem
about algebraicity or integrality of modular-function values.
-/

open scoped NumberField

namespace BakerHeegnerStark

/-- The normalized complex realization of the quadratic rational algebra. -/
noncomputable def quadraticComplexEmbedding (p : ℕ) :
    Qsqrtd ((-(p : ℤ) : ℤ) : ℚ) →ₐ[ℚ] ℂ := by
  refine QuadraticAlgebra.lift ⟨(Real.sqrt (p : ℝ) : ℂ) * Complex.I, ?_⟩
  simp only [Algebra.smul_def, mul_one, map_zero, zero_mul, add_zero]
  rw [← pow_two, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (Nat.cast_nonneg p)]
  push_cast
  ring

/-- The rational coordinates evaluate at the chosen positive imaginary root. -/
theorem quadraticComplexEmbedding_apply (p : ℕ)
    (z : Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) :
    quadraticComplexEmbedding p z = (z.re : ℂ) + (z.im : ℂ) *
      ((Real.sqrt (p : ℝ) : ℂ) * Complex.I) := by
  change z.re • (1 : ℂ) + z.im • ((Real.sqrt (p : ℝ) : ℂ) * Complex.I) = _
  simp [Algebra.smul_def]

/-- The chosen complex realization is injective for a positive parameter. -/
theorem quadraticComplexEmbedding_injective (p : ℕ) (hp : 0 < p) :
    Function.Injective (quadraticComplexEmbedding p) := by
  let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
  have hs : s.im ≠ 0 := by
    simpa [s] using ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp : (0 : ℝ) < (p : ℝ)))
  intro x y h
  rw [quadraticComplexEmbedding_apply, quadraticComplexEmbedding_apply] at h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ratCast_im, Complex.mul_im, Complex.ratCast_re,
    zero_mul, zero_add, add_zero] at hi
  have hxy : x.im = y.im := by exact_mod_cast mul_right_cancel₀ hs hi
  rw [hxy] at h
  have hre : (x.re : ℂ) = (y.re : ℂ) := add_right_cancel h
  exact QuadraticAlgebra.ext (by exact_mod_cast hre) hxy

section Squarefree

variable (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)]

/-- The restriction of the actual field realization to its full ring of integers. -/
noncomputable def quadraticIntegerEmbedding :
    𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) →ₐ[ℤ] ℂ :=
  ((quadraticComplexEmbedding p).toRingHom.comp
    (algebraMap (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))
      (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))).toIntAlgHom

/-- The integer embedding is the restriction of the normalized field embedding. -/
theorem quadraticIntegerEmbedding_apply (x : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))) :
    quadraticIntegerEmbedding p x =
      quadraticComplexEmbedding p (x : Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) := rfl

/-- QNF's actual ring-of-integers basis evaluates at `1,(1+i√p)/2`. -/
theorem quadraticIntegerEmbedding_eq_coordinates (k : ℤ) (hk : -(p : ℤ) = 1 + 4 * k)
    (x : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))) :
    let b := QuadraticNumberFields.RingOfIntegers.ringOfIntegersBasisOfEq
      (d := -(p : ℤ)) k hk
    quadraticIntegerEmbedding p x = ((b.repr x 0 : ℤ) : ℂ) +
      ((b.repr x 1 : ℤ) : ℂ) * ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2) := by
  let b := QuadraticNumberFields.RingOfIntegers.ringOfIntegersBasisOfEq
    (d := -(p : ℤ)) k hk
  have hm := QuadraticNumberFields.RingOfIntegers.ringOfIntegersBasisOfEq_repr_zero k hk x
  have hn := QuadraticNumberFields.RingOfIntegers.ringOfIntegersBasisOfEq_repr_one k hk x
  have hmc : ((b.repr x 0 : ℤ) : ℂ) =
      ((x : Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)).re : ℂ) -
      ((x : Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)).im : ℂ) := by exact_mod_cast hm
  have hnc : ((b.repr x 1 : ℤ) : ℂ) =
      2 * ((x : Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)).im : ℂ) := by exact_mod_cast hn
  rw [quadraticIntegerEmbedding_apply, quadraticComplexEmbedding_apply]
  linear_combination -hmc - ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2) * hnc

/-- The image of the full ring of integers is the actual half-period module. -/
theorem mem_quadraticIntegerEmbedding_range_iff (k : ℤ)
    (hk : -(p : ℤ) = 1 + 4 * k) (α : ℂ) :
    α ∈ (quadraticIntegerEmbedding p).toRingHom.range ↔
      α ∈ periodModule ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2) := by
  let b := QuadraticNumberFields.RingOfIntegers.ringOfIntegersBasisOfEq
    (d := -(p : ℤ)) k hk
  constructor
  · rintro ⟨x, rfl⟩
    exact (mem_periodModule_iff _ _).mpr
      ⟨b.repr x 0, b.repr x 1, quadraticIntegerEmbedding_eq_coordinates p k hk x⟩
  · intro h
    obtain ⟨m, n, hα⟩ := (mem_periodModule_iff _ α).mp h
    let x := b.repr.symm (Finsupp.single 0 m + Finsupp.single 1 n)
    have hcoords : b.repr x = Finsupp.single 0 m + Finsupp.single 1 n :=
      b.repr.apply_symm_apply _
    have hxm : b.repr x 0 = m := by rw [hcoords]; simp
    have hxn : b.repr x 1 = n := by rw [hcoords]; simp
    refine ⟨x, ?_⟩
    change quadraticIntegerEmbedding p x = α
    rw [quadraticIntegerEmbedding_eq_coordinates p k hk]
    change ((b.repr x 0 : ℤ) : ℂ) + ((b.repr x 1 : ℤ) : ℂ) * _ = α
    rw [hxm, hxn]
    exact hα.symm

/-- The restriction to the actual ring of integers is faithful. -/
theorem quadraticIntegerEmbedding_injective (hp : 0 < p) :
    Function.Injective (quadraticIntegerEmbedding p) := by
  intro x y h
  apply Subtype.ext
  apply quadraticComplexEmbedding_injective p hp
  exact h

/-- The full quadratic integer ring, in its actual complex realization, is
exactly the scalar multiplier ring of the half-period lattice. -/
theorem mul_preserves_quadraticInteger_periodModule_iff (k : ℤ)
    (hk : -(p : ℤ) = 1 + 4 * k) (α : ℂ) :
    (∀ z ∈ periodModule ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2),
      α * z ∈ periodModule ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2)) ↔
      α ∈ (quadraticIntegerEmbedding p).toRingHom.range := by
  exact (mul_preserves_periodModule_iff _ α k 1 (by
    simpa using halfPeriod_quadratic p k hk)).trans
      (mem_quadraticIntegerEmbedding_range_iff p k hk α).symm

/-- Field class number one makes QNF's actual half-integer order a principal
ideal ring, by its proved isomorphism with the full integer ring. -/
theorem halfOrder_isPrincipalIdealRing_of_classNumber_eq_one (k : ℤ)
    (hk : -(p : ℤ) = 1 + 4 * k)
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1) :
    IsPrincipalIdealRing (ZOnePlusSqrtdOverTwo k) := by
  have : IsPrincipalIdealRing (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))) :=
    NumberField.classNumber_eq_one_iff.mp hclass
  let e := QuadraticNumberFields.RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq
    (-(p : ℤ)) k hk
  exact IsPrincipalIdealRing.of_surjective e e.surjective

/-- Field class number one gives a trivial class group of the actual maximal
half-integer order. It does not give a trivial class group of the smaller order. -/
theorem halfOrderClassGroup_subsingleton_of_classNumber_eq_one (k : ℤ)
    (hk : -(p : ℤ) = 1 + 4 * k)
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1) :
    letI := halfOrder_isDomain p k hk
    Subsingleton (ClassGroup (ZOnePlusSqrtdOverTwo k)) := by
  have := halfOrder_isDomain p k hk
  have := halfOrder_isPrincipalIdealRing_of_classNumber_eq_one p k hk hclass
  obtain ⟨c, hc⟩ := Fintype.card_eq_one_iff.mp
    (card_classGroup_eq_one (R := ZOnePlusSqrtdOverTwo k))
  exact ⟨fun x y => (hc x).trans (hc y).symm⟩

end Squarefree

end BakerHeegnerStark
