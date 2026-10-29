/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Small primitive values of the canonical quadratic norms

The odd and even discriminant normal forms have norms
`x² - xk + ck²` and `x² + ck²`. Away from the scalar coordinate `k = 0`,
their minimum is `c` when `c ≥ 2`. The odd norm misses `c + 1` but
primitively represents `c + 2`; the even norm primitively represents `c + 1`.
The unit cases `c = 1` have different small primitive spectra. All the
exclusions below follow from completed squares and finite integer bounds.
-/

namespace BakerHeegnerStark

/-- The norm in the odd-discriminant canonical coordinates. -/
def oddQuadraticNorm (c x k : ℤ) : ℤ := x ^ 2 - x * k + c * k ^ 2

/-- The norm in the even-discriminant canonical coordinates. -/
def evenQuadraticNorm (c x k : ℤ) : ℤ := x ^ 2 + c * k ^ 2

/-- An integer primitively represented by the odd canonical norm. -/
def PrimitiveOddNormValue (c n : ℤ) : Prop :=
  ∃ x k : ℤ, Nat.Coprime x.natAbs k.natAbs ∧ oddQuadraticNorm c x k = n

/-- An integer primitively represented by the even canonical norm. -/
def PrimitiveEvenNormValue (c n : ℤ) : Prop :=
  ∃ x k : ℤ, Nat.Coprime x.natAbs k.natAbs ∧ evenQuadraticNorm c x k = n

/-- Completing the square in the odd norm, without denominators. -/
theorem oddQuadraticNorm_completed_square (c x k : ℤ) :
    4 * oddQuadraticNorm c x k = (2 * x - k) ^ 2 + (4 * c - 1) * k ^ 2 := by
  dsimp [oddQuadraticNorm]
  ring

/-- The corresponding completed-square identity for the even norm. -/
theorem evenQuadraticNorm_completed_square (c x k : ℤ) :
    4 * evenQuadraticNorm c x k = (2 * x) ^ 2 + 4 * c * k ^ 2 := by
  dsimp [evenQuadraticNorm]
  ring

private theorem int_sq_sub_self_nonneg (x : ℤ) : 0 ≤ x ^ 2 - x := by
  rcases le_or_gt x 0 with hx | hx
  · nlinarith [sq_nonneg x]
  · have hx' : 1 ≤ x := by omega
    nlinarith [sq_nonneg (x - 1)]

private theorem int_sq_sub_self_ne_one (x : ℤ) : x ^ 2 - x ≠ 1 := by
  intro h
  have hlo : -1 ≤ x := by nlinarith [sq_nonneg x]
  have hhi : x ≤ 2 := by nlinarith [sq_nonneg (x - 1)]
  interval_cases x <;> norm_num at h

private theorem int_sq_ge_one_of_ne_zero {k : ℤ} (hk : k ≠ 0) : 1 ≤ k ^ 2 := by
  have hsign : k ≤ -1 ∨ 1 ≤ k := by omega
  rcases hsign with hk | hk
  · nlinarith [sq_nonneg (k + 1)]
  · nlinarith [sq_nonneg (k - 1)]

/-- Once the non-scalar coordinate has absolute value at least two, the odd
norm is already at least `4c - 1`. -/
theorem oddQuadraticNorm_ge_four_mul_sub_one {c x k : ℤ} (hc : 1 ≤ c)
    (hk : k ≤ -2 ∨ 2 ≤ k) : 4 * c - 1 ≤ oddQuadraticNorm c x k := by
  have hk2 : 4 ≤ k ^ 2 := by
    rcases hk with hk | hk
    · nlinarith [sq_nonneg (k + 2)]
    · nlinarith [sq_nonneg (k - 2)]
  have hprod : 0 ≤ (4 * c - 1) * (k ^ 2 - 4) :=
    mul_nonneg (by omega) (sub_nonneg.mpr hk2)
  have hsq := oddQuadraticNorm_completed_square c x k
  nlinarith [sq_nonneg (2 * x - k)]

/-- A non-scalar odd norm is at least `c`; this also holds in the unit case. -/
theorem oddQuadraticNorm_ge_of_k_ne_zero {c x k : ℤ} (hc : 1 ≤ c)
    (hk : k ≠ 0) : c ≤ oddQuadraticNorm c x k := by
  by_cases hk1 : k = 1
  · subst k
    dsimp [oddQuadraticNorm]
    nlinarith [int_sq_sub_self_nonneg x]
  by_cases hkm1 : k = -1
  · subst k
    dsimp [oddQuadraticNorm]
    nlinarith [int_sq_sub_self_nonneg (-x)]
  have hlarge : k ≤ -2 ∨ 2 ≤ k := by omega
  have hbound := oddQuadraticNorm_ge_four_mul_sub_one hc hlarge (x := x)
  omega

/-- A non-scalar even norm is at least `c`. -/
theorem evenQuadraticNorm_ge_of_k_ne_zero {c x k : ℤ} (hc : 0 ≤ c)
    (hk : k ≠ 0) : c ≤ evenQuadraticNorm c x k := by
  have hk2 := int_sq_ge_one_of_ne_zero hk
  have hprod : 0 ≤ c * (k ^ 2 - 1) := mul_nonneg hc (sub_nonneg.mpr hk2)
  dsimp [evenQuadraticNorm]
  nlinarith [sq_nonneg x]

/-- The gap after `c` in the odd norm, provided the coordinate is non-scalar.
The nonzero-coordinate hypothesis is essential: a scalar square can be `c + 1`. -/
theorem oddQuadraticNorm_ne_c_add_one {c x k : ℤ} (hc : 1 ≤ c)
    (hk : k ≠ 0) : oddQuadraticNorm c x k ≠ c + 1 := by
  intro h
  by_cases hk1 : k = 1
  · subst k
    apply int_sq_sub_self_ne_one x
    dsimp [oddQuadraticNorm] at h
    nlinarith
  by_cases hkm1 : k = -1
  · subst k
    apply int_sq_sub_self_ne_one (-x)
    dsimp [oddQuadraticNorm] at h
    nlinarith
  have hlarge : k ≤ -2 ∨ 2 ≤ k := by omega
  have hbound := oddQuadraticNorm_ge_four_mul_sub_one hc hlarge (x := x)
  omega

private theorem sq_eq_one_of_coprime_zero {x : ℤ}
    (hcop : Nat.Coprime x.natAbs (0 : ℤ).natAbs) : x ^ 2 = 1 := by
  have hx : x.natAbs = 1 := by simpa using hcop
  obtain hx | hx := Int.natAbs_eq_iff.mp hx
  · simp [hx]
  · simp [hx]

/-- A primitive scalar odd norm is exactly one. -/
theorem oddQuadraticNorm_eq_one_of_k_eq_zero {c x k : ℤ}
    (hcop : Nat.Coprime x.natAbs k.natAbs) (hk : k = 0) :
    oddQuadraticNorm c x k = 1 := by
  subst k
  simpa [oddQuadraticNorm] using sq_eq_one_of_coprime_zero hcop

/-- A primitive scalar even norm is exactly one. -/
theorem evenQuadraticNorm_eq_one_of_k_eq_zero {c x k : ℤ}
    (hcop : Nat.Coprime x.natAbs k.natAbs) (hk : k = 0) :
    evenQuadraticNorm c x k = 1 := by
  subst k
  simpa [evenQuadraticNorm] using sq_eq_one_of_coprime_zero hcop

/-- Every primitive odd representation of a value other than one is nonscalar. -/
theorem oddQuadraticNorm_k_ne_zero {c x k : ℤ}
    (hcop : Nat.Coprime x.natAbs k.natAbs) (hn : oddQuadraticNorm c x k ≠ 1) :
    k ≠ 0 := by
  intro hk
  exact hn (oddQuadraticNorm_eq_one_of_k_eq_zero hcop hk)

/-- Every primitive even representation of a value other than one is nonscalar. -/
theorem evenQuadraticNorm_k_ne_zero {c x k : ℤ}
    (hcop : Nat.Coprime x.natAbs k.natAbs) (hn : evenQuadraticNorm c x k ≠ 1) :
    k ≠ 0 := by
  intro hk
  exact hn (evenQuadraticNorm_eq_one_of_k_eq_zero hcop hk)

/-- The primitive pair `(0, 1)` represents `c` in the odd norm. -/
theorem primitiveOddNormValue_c (c : ℤ) : PrimitiveOddNormValue c c := by
  refine ⟨0, 1, ?_, ?_⟩
  · norm_num [Nat.Coprime]
  · simp [oddQuadraticNorm]

/-- The primitive pair `(-1, 1)` represents `c + 2` in the odd norm. -/
theorem primitiveOddNormValue_c_add_two (c : ℤ) :
    PrimitiveOddNormValue c (c + 2) := by
  refine ⟨-1, 1, ?_, ?_⟩
  · norm_num [Nat.Coprime]
  · dsimp [oddQuadraticNorm]
    ring

/-- The primitive pair `(0, 1)` represents `c` in the even norm. -/
theorem primitiveEvenNormValue_c (c : ℤ) : PrimitiveEvenNormValue c c := by
  refine ⟨0, 1, ?_, ?_⟩
  · norm_num [Nat.Coprime]
  · simp [evenQuadraticNorm]

/-- The primitive pair `(1, 1)` represents `c + 1` in the even norm. -/
theorem primitiveEvenNormValue_c_add_one (c : ℤ) :
    PrimitiveEvenNormValue c (c + 1) := by
  refine ⟨1, 1, ?_, ?_⟩
  · norm_num [Nat.Coprime]
  · dsimp [evenQuadraticNorm]
    ring

/-- For `c ≥ 2`, every nontrivial primitive odd value is at least `c`. -/
theorem primitiveOddNormValue_ge {c n : ℤ} (hc : 2 ≤ c) (hn : 1 < n)
    (h : PrimitiveOddNormValue c n) : c ≤ n := by
  obtain ⟨x, k, hcop, hnorm⟩ := h
  have hk : k ≠ 0 := oddQuadraticNorm_k_ne_zero (c := c) hcop (by omega)
  simpa only [hnorm] using
    oddQuadraticNorm_ge_of_k_ne_zero (x := x) (by omega : 1 ≤ c) hk

/-- For `c ≥ 2`, every nontrivial primitive even value is at least `c`. -/
theorem primitiveEvenNormValue_ge {c n : ℤ} (hc : 2 ≤ c) (hn : 1 < n)
    (h : PrimitiveEvenNormValue c n) : c ≤ n := by
  obtain ⟨x, k, hcop, hnorm⟩ := h
  have hk : k ≠ 0 := evenQuadraticNorm_k_ne_zero (c := c) hcop (by omega)
  simpa only [hnorm] using
    evenQuadraticNorm_ge_of_k_ne_zero (x := x) (by omega : 0 ≤ c) hk

/-- The primitive odd spectrum does not contain `c + 1`, including for `c = 1`. -/
theorem not_primitiveOddNormValue_c_add_one {c : ℤ} (hc : 1 ≤ c) :
    ¬ PrimitiveOddNormValue c (c + 1) := by
  rintro ⟨x, k, hcop, hnorm⟩
  have hk : k ≠ 0 := oddQuadraticNorm_k_ne_zero (c := c) hcop (by omega)
  exact oddQuadraticNorm_ne_c_add_one hc hk hnorm

private theorem int_bounds_of_sq_lt_nine {z : ℤ} (hz : z ^ 2 < 9) :
    -2 ≤ z ∧ z ≤ 2 := by
  constructor
  · by_contra h
    have hz' : z ≤ -3 := by omega
    nlinarith [sq_nonneg (z + 3)]
  · by_contra h
    have hz' : 3 ≤ z := by omega
    nlinarith [sq_nonneg (z - 3)]

private theorem oddQuadraticNorm_one_small_bounds {x k : ℤ}
    (h : oddQuadraticNorm 1 x k ≤ 5) :
    (-2 ≤ x ∧ x ≤ 2) ∧ (-2 ≤ k ∧ k ≤ 2) := by
  have hx : x ^ 2 < 9 := by
    dsimp [oddQuadraticNorm] at h
    nlinarith [sq_nonneg (2 * k - x)]
  have hk : k ^ 2 < 9 := by
    dsimp [oddQuadraticNorm] at h
    nlinarith [sq_nonneg (2 * x - k)]
  exact ⟨int_bounds_of_sq_lt_nine hx, int_bounds_of_sq_lt_nine hk⟩

/-- The odd unit norm never represents two, without a primitivity hypothesis. -/
theorem oddQuadraticNorm_one_ne_two (x k : ℤ) : oddQuadraticNorm 1 x k ≠ 2 := by
  intro h
  have hsmall : oddQuadraticNorm 1 x k ≤ 5 := by omega
  obtain ⟨⟨hxlo, hxhi⟩, ⟨hklo, hkhi⟩⟩ := oddQuadraticNorm_one_small_bounds hsmall
  interval_cases x <;> interval_cases k <;> norm_num [oddQuadraticNorm] at h

/-- The odd unit norm never represents five, without a primitivity hypothesis. -/
theorem oddQuadraticNorm_one_ne_five (x k : ℤ) : oddQuadraticNorm 1 x k ≠ 5 := by
  intro h
  have hsmall : oddQuadraticNorm 1 x k ≤ 5 := by omega
  obtain ⟨⟨hxlo, hxhi⟩, ⟨hklo, hkhi⟩⟩ := oddQuadraticNorm_one_small_bounds hsmall
  interval_cases x <;> interval_cases k <;> norm_num [oddQuadraticNorm] at h

/-- Four is represented by the odd unit norm only imprimitive coordinates. -/
theorem oddQuadraticNorm_one_ne_four_of_primitive {x k : ℤ}
    (hcop : Nat.Coprime x.natAbs k.natAbs) : oddQuadraticNorm 1 x k ≠ 4 := by
  intro h
  have hsmall : oddQuadraticNorm 1 x k ≤ 5 := by omega
  obtain ⟨⟨hxlo, hxhi⟩, ⟨hklo, hkhi⟩⟩ := oddQuadraticNorm_one_small_bounds hsmall
  interval_cases x <;> interval_cases k <;>
    norm_num [oddQuadraticNorm] at h <;> norm_num [Nat.Coprime] at hcop

private theorem evenQuadraticNorm_one_small_bounds {x k : ℤ}
    (h : evenQuadraticNorm 1 x k ≤ 4) :
    (-2 ≤ x ∧ x ≤ 2) ∧ (-2 ≤ k ∧ k ≤ 2) := by
  have hx : x ^ 2 < 9 := by
    dsimp [evenQuadraticNorm] at h
    nlinarith [sq_nonneg k]
  have hk : k ^ 2 < 9 := by
    dsimp [evenQuadraticNorm] at h
    nlinarith [sq_nonneg x]
  exact ⟨int_bounds_of_sq_lt_nine hx, int_bounds_of_sq_lt_nine hk⟩

/-- The even unit norm never represents three, even imprimitive coordinates. -/
theorem evenQuadraticNorm_one_ne_three (x k : ℤ) : evenQuadraticNorm 1 x k ≠ 3 := by
  intro h
  have hsmall : evenQuadraticNorm 1 x k ≤ 4 := by omega
  obtain ⟨⟨hxlo, hxhi⟩, ⟨hklo, hkhi⟩⟩ := evenQuadraticNorm_one_small_bounds hsmall
  interval_cases x <;> interval_cases k <;> norm_num [evenQuadraticNorm] at h

/-- Four is represented by the even unit norm only imprimitive coordinates. -/
theorem evenQuadraticNorm_one_ne_four_of_primitive {x k : ℤ}
    (hcop : Nat.Coprime x.natAbs k.natAbs) : evenQuadraticNorm 1 x k ≠ 4 := by
  intro h
  have hsmall : evenQuadraticNorm 1 x k ≤ 4 := by omega
  obtain ⟨⟨hxlo, hxhi⟩, ⟨hklo, hkhi⟩⟩ := evenQuadraticNorm_one_small_bounds hsmall
  interval_cases x <;> interval_cases k <;>
    norm_num [evenQuadraticNorm] at h <;> norm_num [Nat.Coprime] at hcop

/-- Two is absent from the primitive odd unit spectrum. -/
theorem not_primitiveOddNormValue_one_two : ¬ PrimitiveOddNormValue 1 2 := by
  rintro ⟨x, k, _, h⟩
  exact oddQuadraticNorm_one_ne_two x k h

/-- Four is absent from the primitive odd unit spectrum. -/
theorem not_primitiveOddNormValue_one_four : ¬ PrimitiveOddNormValue 1 4 := by
  rintro ⟨x, k, hcop, h⟩
  exact oddQuadraticNorm_one_ne_four_of_primitive hcop h

/-- Five is absent from the primitive odd unit spectrum. -/
theorem not_primitiveOddNormValue_one_five : ¬ PrimitiveOddNormValue 1 5 := by
  rintro ⟨x, k, _, h⟩
  exact oddQuadraticNorm_one_ne_five x k h

/-- Three is absent from the primitive even unit spectrum. -/
theorem not_primitiveEvenNormValue_one_three : ¬ PrimitiveEvenNormValue 1 3 := by
  rintro ⟨x, k, _, h⟩
  exact evenQuadraticNorm_one_ne_three x k h

/-- Four is absent from the primitive even unit spectrum. -/
theorem not_primitiveEvenNormValue_one_four : ¬ PrimitiveEvenNormValue 1 4 := by
  rintro ⟨x, k, hcop, h⟩
  exact evenQuadraticNorm_one_ne_four_of_primitive hcop h

/-- The least nontrivial primitive odd unit value is at least three;
`primitiveOddNormValue_c_add_two 1` supplies equality. -/
theorem primitiveOddNormValue_one_ge_three {n : ℤ} (hn : 1 < n)
    (h : PrimitiveOddNormValue 1 n) : 3 ≤ n := by
  have hne : n ≠ 2 := by
    intro heq
    subst n
    exact not_primitiveOddNormValue_one_two h
  omega

end BakerHeegnerStark
