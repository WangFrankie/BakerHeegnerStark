/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.Rationality
import BakerHeegnerStark.ModularForms.ModularPolynomial.DiagonalLimit
import BakerHeegnerStark.ModularForms.ModularPolynomial.LeadingTerm
import Mathlib.Data.Int.Order.Units

/-!
# The Unit Diagonal Leading Coefficient of the Modular Polynomial

At nonsquare levels the actual diagonal root product has a nonzero normalized
cusp limit of norm one. The leading-term theorem identifies this limit with
the leading coefficient of the actual integral diagonal polynomial. Its
integer leading coefficient is therefore a unit.
-/

open UpperHalfPlane ModularForm Polynomial Filter
open scoped Polynomial.Bivariate Topology

noncomputable section

namespace BakerHeegnerStark

/-- The product formula realizes the actual diagonal polynomial on j-values. -/
theorem eval_modularPolynomial_diagonal {N : ℕ} (Φ : ℤ[X][Y])
    (hΦ : ∀ τ : UpperHalfPlane,
      aevalAeval (C (jInvariant τ)) X Φ = cyclicSublatticePolynomial N τ)
    (τ : UpperHalfPlane) :
    ((aevalAeval (X : ℤ[X]) X Φ).map (Int.castRingHom ℂ)).eval (jInvariant τ) =
      (cyclicSublatticePolynomial N τ).eval (jInvariant τ) := by
  have hbase : Int.castRingHom ℂ = algebraMap ℤ ℂ := RingHom.ext_int _ _
  calc
    _ = aeval (jInvariant τ) (aevalAeval (X : ℤ[X]) X Φ) := by
      simp only [Polynomial.eval_map, Polynomial.aeval_def, hbase]
    _ = aevalAeval (jInvariant τ) (jInvariant τ) Φ :=
      aeval_aevalAeval_X_X Φ (jInvariant τ)
    _ = (aevalAeval (C (jInvariant τ)) X Φ).eval (jInvariant τ) :=
      (eval_aevalAeval_C_X Φ (jInvariant τ) (jInvariant τ)).symm
    _ = _ := by rw [hΦ τ]

/-- An integer polynomial whose complex leading coefficient has norm one has
unit leading coefficient over the integers. -/
theorem isUnit_leadingCoeff_of_norm_map_eq_one (p : ℤ[X])
    (hnorm : ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖ = 1) : IsUnit p.leadingCoeff := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  rw [Polynomial.leadingCoeff_map_of_injective hinj] at hnorm
  have habsR : |(p.leadingCoeff : ℝ)| = 1 := by
    simpa only [Int.coe_castRingHom, Complex.norm_intCast] using hnorm
  have habsZ : |p.leadingCoeff| = 1 := by exact_mod_cast habsR
  exact Int.isUnit_iff_abs_eq.mpr habsZ

/-- The diagonal leading coefficient at every positive nonsquare level is a
unit, for any integral polynomial satisfying the actual product formula. -/
theorem isUnit_modularPolynomial_diagonal_leadingCoeff {N : ℕ}
    (hN : 0 < N) (hns : ¬ IsSquare N) (Φ : ℤ[X][Y])
    (hΦ : ∀ τ : UpperHalfPlane,
      aevalAeval (C (jInvariant τ)) X Φ = cyclicSublatticePolynomial N τ) :
    IsUnit (aevalAeval (X : ℤ[X]) X Φ).leadingCoeff := by
  let p : ℤ[X] := aevalAeval (X : ℤ[X]) X Φ
  let pC : ℂ[X] := p.map (Int.castRingHom ℂ)
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ cyclicSublatticeDiagonalPoleOrder N *
        pC.eval (jInvariant τ)) atImInfty (𝓝 (cyclicSublatticeDiagonalConstant N)) := by
    convert tendsto_cyclicSublatticeDiagonal hN hns using 1
    funext τ
    exact congrArg (fun z : ℂ => Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^
      cyclicSublatticeDiagonalPoleOrder N * z) (eval_modularPolynomial_diagonal Φ hΦ τ)
  have hlead := leadingCoeff_eq_of_tendsto_qParam_mul_polynomial_jInvariant hN pC
    (cyclicSublatticeDiagonalPoleOrder N) (cyclicSublatticeDiagonalConstant N)
    (cyclicSublatticeDiagonalConstant_ne_zero N) hlim
  apply isUnit_leadingCoeff_of_norm_map_eq_one p
  change ‖pC.leadingCoeff‖ = 1
  rw [hlead.2, norm_cyclicSublatticeDiagonalConstant]

/-- **The classical modular polynomial theorem** (Cox, Theorem 11.18), including
integral coefficients, the actual cyclic-sublattice product, and unit diagonal
leading coefficient at every positive nonsquare level. -/
theorem modularPolynomialTheorem : ModularPolynomialTheorem := by
  intro N hN
  obtain ⟨Φ, hΦ⟩ := exists_integer_modularPolynomial hN
  exact ⟨Φ, hΦ, fun hns =>
    isUnit_modularPolynomial_diagonal_leadingCoeff hN hns Φ hΦ⟩

end BakerHeegnerStark
