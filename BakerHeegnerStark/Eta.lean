/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Dedekind Eta on the Positive Imaginary Axis

The real product expansion identifies eta with a nonnegative real number.
Nonvanishing on the upper half-plane then gives strict positivity.
-/

namespace ModularForm

private theorem qParam_mul_I (h y : ℝ) :
    Function.Periodic.qParam h ((y : ℂ) * Complex.I) =
      (Real.exp (-2 * Real.pi * y / h) : ℂ) := by
  rw [Function.Periodic.qParam, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The real product expansion of eta at a point on the positive imaginary axis. -/
theorem eta_mul_I_eq (y : ℝ) (hy : 0 < y) :
    eta ((y : ℂ) * Complex.I) =
      ((Real.exp (-2 * Real.pi * y / 24) *
        ∏' n : ℕ, (1 - Real.exp (-2 * Real.pi * y) ^ (n + 1))) : ℝ) := by
  let r := Real.exp (-2 * Real.pi * y)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [Real.pi_pos]
  have hsum : Summable (fun n : ℕ ↦ r ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
  have hprod : Multipliable (fun n : ℕ ↦ 1 - r ^ (n + 1)) := by
    simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hsum.neg
  have hmap := hprod.map_tprod Complex.ofRealHom Complex.continuous_ofReal
  change ((∏' n : ℕ, (1 - r ^ (n + 1)) : ℝ) : ℂ) =
    ∏' n : ℕ, ((1 - r ^ (n + 1) : ℝ) : ℂ) at hmap
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] at hmap
  simp only [eta, eta_q, qParam_mul_I, div_one]
  rw [← hmap]
  exact (Complex.ofReal_mul _ _).symm

/-- Eta is real on the positive imaginary axis. -/
theorem eta_mul_I_im (y : ℝ) (hy : 0 < y) :
    (eta ((y : ℂ) * Complex.I)).im = 0 := by
  rw [eta_mul_I_eq y hy]
  exact Complex.ofReal_im _

/-- Eta has strictly positive real part on the positive imaginary axis. -/
theorem eta_mul_I_re_pos (y : ℝ) (hy : 0 < y) :
    0 < (eta ((y : ℂ) * Complex.I)).re := by
  have hr1 : Real.exp (-2 * Real.pi * y) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [Real.pi_pos]
  have hnonneg : 0 ≤ (eta ((y : ℂ) * Complex.I)).re := by
    rw [eta_mul_I_eq y hy, Complex.ofReal_re]
    apply mul_nonneg (Real.exp_pos _).le
    apply tprod_nonneg
    intro n
    exact sub_nonneg.mpr (pow_le_one₀ (Real.exp_pos _).le hr1.le)
  have hne : eta ((y : ℂ) * Complex.I) ≠ 0 :=
    eta_ne_zero (by simpa using hy)
  apply lt_of_le_of_ne hnonneg
  intro hzero
  apply hne
  apply Complex.ext
  · simpa using hzero.symm
  · exact eta_mul_I_im y hy

end ModularForm
