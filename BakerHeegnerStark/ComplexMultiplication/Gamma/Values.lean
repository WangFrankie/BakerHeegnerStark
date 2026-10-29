/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.SingularModuli.DegreeBound
import BakerHeegnerStark.ModularForms.Weber.Bounds
import BakerHeegnerStark.ModularForms.Weber.Integrality
import BakerHeegnerStark.FieldTheory.ComplexAdjoin

/-!
# Actual Gamma and Weber Values at CM Points

The normalization at `(3+√-m)/2` is real by the actual Weber quotient formula.
Its cube is the proved integral singular modulus, so it is integral and generates
a finite field of degree at most three times the field class number.
The stronger field-membership theorem is proved separately in `ComplexMultiplication/Gamma/Rationality.lean`.

The real elements of `ℚ(j(√-m), √-m)` are exactly those of `ℚ(j(√-m))` in the
chosen complex embedding. For the actual real Weber square, membership in
these two fields is therefore equivalent. This is a proved algebraic descent,
not a proof that the Weber square belongs to either field.
-/

open ModularForm Polynomial IntermediateField QuadraticNumberFields
open scoped NumberField

namespace BakerHeegnerStark

/-- The normalized shifted CM gamma value is real, independently of arithmetic
CM hypotheses and without selecting a cube root from its cube. -/
theorem gamma₂_cmPointShift_im {m : ℕ} (hm : 0 < m) :
    (gamma₂ (cmPointShift m)).im = 0 := by
  have hy : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hshift : cmPointShift m = UpperHalfPlane.ofComplex
      (((Real.sqrt m : ℂ) * Complex.I + 3) / 2) := by
    rw [cmPointShift, add_comm]
  have hf : weberF ((Real.sqrt m : ℂ) * Complex.I) =
      ((weberF ((Real.sqrt m : ℂ) * Complex.I)).re : ℂ) :=
    Complex.ext rfl (weberF_mul_I_im _ hy)
  rw [hshift, gamma₂_half_add_three_eq_weberF (by simpa using hy), hf]
  have hnum : (256 : ℂ) = ((256 : ℝ) : ℂ) := by norm_num
  rw [hnum, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_sub, ← Complex.ofReal_div]
  exact Complex.ofReal_im _

/-- The actual shifted CM gamma value is integral because its cube is the
unconditionally proved integral singular modulus. -/
theorem isIntegral_gamma₂_cmPointShift {m : ℕ} (hm : 0 < m) (hm4 : m % 4 = 3) :
    IsIntegral ℤ (gamma₂ (cmPointShift m)) := by
  apply IsIntegral.of_pow (n := 3) (by decide)
  rw [gamma₂_cube, jInvariant_cmPointShift hm]
  exact singularModulusIntegrality m hm hm4

/-- Gamma at the normalized CM point generates a genuine finite extension. -/
theorem finiteDimensional_gamma₂_cmPointShift {m : ℕ} (hm : 0 < m) (hm4 : m % 4 = 3) :
    FiniteDimensional ℚ ℚ⟮gamma₂ (cmPointShift m)⟯ :=
  IntermediateField.adjoin.finiteDimensional
    ((isIntegral_gamma₂_cmPointShift hm hm4).tower_top (A := ℚ))

/-- The actual gamma-generated field has degree at most three times the field
class number, including the case `3 ∣ m`. For `3 ∤ m`, membership in the
j-generated field is proved separately in `ComplexMultiplication/Gamma/Rationality.lean`. -/
theorem gamma₂_cmPointShift_finrank_le_three_mul_classNumber
    (m : ℕ) [Fact (Squarefree (-(m : ℤ)))] [Fact (-(m : ℤ) ≠ 1)]
    (hm4 : m % 4 = 3) :
    Module.finrank ℚ ℚ⟮gamma₂ (cmPointShift m)⟯ ≤
      3 * NumberField.classNumber (Qsqrtd ((-(m : ℤ) : ℤ) : ℚ)) := by
  have hm : 0 < m := by omega
  have hj : IsIntegral ℚ (jInvariant (cmPoint m)) :=
    (singularModulusIntegrality m hm hm4).tower_top
  have hγ : IsIntegral ℚ (gamma₂ (cmPointShift m)) :=
    (isIntegral_gamma₂_cmPointShift hm hm4).tower_top
  let P : ℚ[X] := (minpoly ℚ (jInvariant (cmPoint m))).comp (X ^ 3)
  have hmonic : P.Monic := (minpoly.monic hj).comp (monic_X_pow 3) (by simp)
  have hroot : aeval (gamma₂ (cmPointShift m)) P = 0 := by
    change aeval (gamma₂ (cmPointShift m))
      ((minpoly ℚ (jInvariant (cmPoint m))).comp (X ^ 3)) = 0
    rw [aeval_comp, aeval_X_pow, gamma₂_cube, jInvariant_cmPointShift hm]
    exact minpoly.aeval ℚ (jInvariant (cmPoint m))
  calc
    Module.finrank ℚ ℚ⟮gamma₂ (cmPointShift m)⟯ =
        (minpoly ℚ (gamma₂ (cmPointShift m))).natDegree :=
      IntermediateField.adjoin.finrank hγ
    _ ≤ P.natDegree := natDegree_le_of_dvd (minpoly.dvd ℚ _ hroot) hmonic.ne_zero
    _ = (minpoly ℚ (jInvariant (cmPoint m))).natDegree * 3 := by
      simp only [P, natDegree_comp, natDegree_X_pow]
    _ = Module.finrank ℚ ℚ⟮jInvariant (cmPoint m)⟯ * 3 := by
      rw [IntermediateField.adjoin.finrank hj]
    _ ≤ NumberField.classNumber (Qsqrtd ((-(m : ℤ) : ℤ) : ℚ)) * 3 :=
      Nat.mul_le_mul_right 3 (singularModulusDegree m hm4)
    _ = _ := Nat.mul_comm _ _

/-- The actual Weber square is integral at every positive square-root CM
parameter, including squares and nonsquarefree parameters. -/
theorem isIntegral_weberF_sq_sqrtPoint {m : ℕ} (hm : 0 < m) :
    IsIntegral ℤ (weberF ((Real.sqrt m : ℂ) * Complex.I) ^ 2) := by
  have h := isIntegral_weberF_sq_of_isIntegral_jInvariant (sqrtPoint m)
    (isIntegral_jInvariant_sqrtPoint hm)
  rwa [coe_sqrtPoint hm] at h

/-- Heegner's actual `2/𝔣(√-m)²` is integral without class number one or
Weber reciprocity whenever the shifted maximal-order CM point is defined. -/
theorem isIntegral_two_div_weberF_sq_sqrtPoint {m : ℕ} (hm : 0 < m) (hm4 : m % 4 = 3) :
    IsIntegral ℤ (2 / weberF ((Real.sqrt m : ℂ) * Complex.I) ^ 2) := by
  have hy : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hshift : cmPointShift m = UpperHalfPlane.ofComplex
      (((Real.sqrt m : ℂ) * Complex.I + 3) / 2) := by
    rw [cmPointShift, add_comm]
  have hγ := isIntegral_gamma₂_cmPointShift hm hm4
  rw [hshift] at hγ
  exact isIntegral_two_div_weberF_sq_of_isIntegral_gamma₂ (by simpa using hy) hγ

/-- The square-root-order singular modulus is real in the chosen complex embedding. -/
theorem jInvariant_sqrtPoint_im {m : ℕ} (hm : 0 < m) :
    (jInvariant (sqrtPoint m)).im = 0 := by
  have hy : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hp : sqrtPoint m =
      (⟨(Real.sqrt m : ℂ) * Complex.I, by simpa using hy⟩ : UpperHalfPlane) :=
    UpperHalfPlane.ext (coe_sqrtPoint hm)
  have hγ : (gamma₂ (sqrtPoint m)).im = 0 := by
    rw [hp]
    exact gamma₂_mul_I_im (Real.sqrt m) hy
  have hreal : gamma₂ (sqrtPoint m) = ((gamma₂ (sqrtPoint m)).re : ℂ) :=
    Complex.ext rfl hγ
  rw [← gamma₂_cube, hreal, ← Complex.ofReal_pow]
  rfl

/-- The real elements of `ℚ(j(√-m), √-m)` are exactly those of its `j`-generated subfield. -/
theorem mem_adjoin_sqrtPoint_iff_of_im_eq_zero {m : ℕ} (hm : 0 < m)
    {x : ℂ} (hx : x.im = 0) :
    x ∈ ℚ⟮jInvariant (sqrtPoint m)⟯⟮(sqrtPoint m : ℂ)⟯ ↔
      x ∈ ℚ⟮jInvariant (sqrtPoint m)⟯ := by
  have hsq : (sqrtPoint m : ℂ) ^ 2 ∈ ℚ⟮jInvariant (sqrtPoint m)⟯ := by
    have hs : (sqrtPoint m : ℂ) ^ 2 = -(m : ℂ) := by
      linear_combination sqrtPoint_quadratic hm
    rw [hs]
    exact (ℚ⟮jInvariant (sqrtPoint m)⟯).neg_mem
      ((ℚ⟮jInvariant (sqrtPoint m)⟯).natCast_mem m)
  exact IntermediateField.mem_adjoin_of_im_eq_zero_iff
    ℚ⟮jInvariant (sqrtPoint m)⟯
    (fun z hz ↦ IntermediateField.im_eq_zero_of_mem_adjoin (jInvariant_sqrtPoint_im hm) hz)
    (ne_of_gt (sqrtPoint m).im_pos) hsq hx

/-- Reality reduces Weber-square descent to membership in the CM-generated compositum.
This equivalence does not prove either membership assertion. -/
theorem weberF_sq_mem_cmAdjoin_iff {m : ℕ} (hm : 0 < m) :
    weberF ((Real.sqrt m : ℂ) * Complex.I) ^ 2 ∈
        ℚ⟮jInvariant (sqrtPoint m)⟯⟮(sqrtPoint m : ℂ)⟯ ↔
      weberF ((Real.sqrt m : ℂ) * Complex.I) ^ 2 ∈ ℚ⟮jInvariant (sqrtPoint m)⟯ := by
  have hy : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hx : (weberF ((Real.sqrt m : ℂ) * Complex.I) ^ 2).im = 0 := by
    simp only [pow_two, Complex.mul_im, weberF_mul_I_im (Real.sqrt m) hy,
      mul_zero, zero_mul, add_zero]
  exact mem_adjoin_sqrtPoint_iff_of_im_eq_zero hm hx

end BakerHeegnerStark
