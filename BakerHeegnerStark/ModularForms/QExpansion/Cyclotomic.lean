/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.CyclicSublattice.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Cyclotomic q-Expansions of Cyclic-Sublattice Transforms

The affine transform `(aτ+b)/d` splits its q-parameter into a finite-order
phase and a power of the width-`d` q-parameter. The full convergent integral
numerator expansion of `j` therefore gives a convergent expansion of each
transformed j-value with algebraic-integer coefficients. This does not assert
Galois descent or integrality of the general modular polynomial.
-/

open UpperHalfPlane ModularForm

noncomputable section

namespace BakerHeegnerStark

/-- The finite-order phase contributed by the translation `b/d`. -/
def cyclicSublatticePhase (b d : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * b / d)

theorem cyclicSublatticePhase_ne_zero (b d : ℕ) :
    cyclicSublatticePhase b d ≠ 0 :=
  Complex.exp_ne_zero _

/-- For positive `d`, the translation phase is a `d`-th root of unity. -/
theorem cyclicSublatticePhase_pow {b d : ℕ} (hd : 0 < d) :
    cyclicSublatticePhase b d ^ d = 1 := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hexp : (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * b / d) =
      (b : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp [hdC]
  rw [cyclicSublatticePhase, ← Complex.exp_nat_mul, hexp, Complex.exp_nat_mul]
  simp

/-- The phase is an algebraic integer because a positive power is one. -/
theorem isIntegral_cyclicSublatticePhase {b d : ℕ} (hd : 0 < d) :
    IsIntegral ℤ (cyclicSublatticePhase b d) := by
  apply IsIntegral.of_pow hd
  rw [cyclicSublatticePhase_pow hd]
  exact isIntegral_one

/-- The inverse phase has the same finite order. -/
theorem cyclicSublatticePhase_inv_pow {b d : ℕ} (hd : 0 < d) :
    (cyclicSublatticePhase b d)⁻¹ ^ d = 1 := by
  rw [inv_pow, cyclicSublatticePhase_pow hd, inv_one]

/-- Inverse-phase integrality follows from finite order, not division closure
of algebraic integers. -/
theorem isIntegral_cyclicSublatticePhase_inv {b d : ℕ} (hd : 0 < d) :
    IsIntegral ℤ ((cyclicSublatticePhase b d)⁻¹) := by
  apply IsIntegral.of_pow hd
  rw [cyclicSublatticePhase_inv_pow hd]
  exact isIntegral_one

/-- Exact separation of the translation phase and the width-`d` q-parameter. -/
theorem qParam_cyclicSublatticePoint {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (cyclicSublatticePoint t τ : ℂ) =
      cyclicSublatticePhase t.2.1 t.2.2 *
        Function.Periodic.qParam (t.2.2 : ℝ) (τ : ℂ) ^ t.1 := by
  rw [cyclicSublatticePoint_coe ha hd]
  simp only [Function.Periodic.qParam, cyclicSublatticePhase, Complex.ofReal_one,
    div_one, Complex.ofReal_natCast, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

/-- The full convergent expansion of the transformed j-value, normalized by
`Q^a`, where `Q` is the width-`d` q-parameter. -/
theorem hasSum_jInvariant_cyclicSublatticePoint {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      (((jInvariantIntegralNumerator.coeff n : ℂ) *
        cyclicSublatticePhase t.2.1 t.2.2 ^ n) /
          cyclicSublatticePhase t.2.1 t.2.2) *
        Function.Periodic.qParam (t.2.2 : ℝ) (τ : ℂ) ^ (t.1 * n))
      (Function.Periodic.qParam (t.2.2 : ℝ) (τ : ℂ) ^ t.1 *
        jInvariant (cyclicSublatticePoint t τ)) := by
  have h := (hasSum_jInvariantIntegralNumerator (cyclicSublatticePoint t τ)).div_const
    (cyclicSublatticePhase t.2.1 t.2.2)
  rw [qParam_cyclicSublatticePoint ha hd] at h
  convert h using 1
  · funext n
    rw [mul_pow, ← pow_mul]
    ring
  · field_simp [cyclicSublatticePhase_ne_zero]

/-- Every coefficient in the transformed convergent expansion is an algebraic
integer; the denominator is specifically a finite-order phase. -/
theorem isIntegral_jInvariant_cyclicSublatticePoint_coeff {b d : ℕ}
    (hd : 0 < d) (n : ℕ) :
    IsIntegral ℤ (((jInvariantIntegralNumerator.coeff n : ℂ) *
      cyclicSublatticePhase b d ^ n) / cyclicSublatticePhase b d) := by
  have hpow : IsIntegral ℤ (cyclicSublatticePhase b d ^ n) := by
    apply IsIntegral.of_pow hd
    rw [← pow_mul, Nat.mul_comm n d, pow_mul, cyclicSublatticePhase_pow hd, one_pow]
    exact isIntegral_one
  rw [div_eq_mul_inv]
  exact ((isIntegral_intCast (jInvariantIntegralNumerator.coeff n)).mul hpow).mul
    (isIntegral_cyclicSublatticePhase_inv hd)

end BakerHeegnerStark
