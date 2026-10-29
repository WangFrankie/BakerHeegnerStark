/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.BranchSpace

/-!
# Full coefficient-field power series of actual Weber branches

The canonical coefficients of the actual function span determine a full power
series over `weberBranchCoefficientField`. Its complex embedding is the width-24
q-expansion of the common cusp regularization, and it converges to that function
everywhere on the upper half-plane. Coefficient automorphisms act only on the
formal coefficients; the convergence proof uses a finite combination of the
three known branch sums, not continuity of any field automorphism.
-/

open BakerHeegnerStark UpperHalfPlane Filter Complex Module
open scoped Topology Manifold ModularForm MatrixGroups

noncomputable section
namespace ModularForm

/-- The entire coefficient-field series attached to the canonical coefficients
of an actual element of the Weber-branch function space. -/
def weberBranchSpacePowerSeries (f : weberBranchSpace) :
    PowerSeries weberBranchCoefficientField :=
  ∑ i : Fin 3, PowerSeries.C (weberBranchCoefficientEquiv.symm f i) *
    PowerSeries.map (Int.castRingHom weberBranchCoefficientField)
      (weberSquareBranchIntegralQExpansion i)

/-- Every coefficient is the canonical finite combination of the actual integer
branch coefficients. -/
theorem weberBranchSpacePowerSeries_coeff (f : weberBranchSpace) (n : ℕ) :
    (weberBranchSpacePowerSeries f).coeff n =
      ∑ i : Fin 3, weberBranchCoefficientEquiv.symm f i *
        (weberSquareBranchIntegralQExpansion i).coeff n := by
  simp [weberBranchSpacePowerSeries]

/-- Coefficient action on the actual function space agrees with mapping the
entire formal series, not merely a finite truncation. -/
theorem weberBranchSpacePowerSeries_coefficientAction
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (f : weberBranchSpace) :
    weberBranchSpacePowerSeries (weberBranchCoefficientAction σ f) =
      PowerSeries.map σ.toRingHom (weberBranchSpacePowerSeries f) := by
  ext n
  simp [weberBranchSpacePowerSeries_coeff]

/-- The embedded series is the finite linear combination of the three complete
integer branch series with the embedded canonical coefficients. -/
theorem map_weberBranchSpacePowerSeries (f : weberBranchSpace) :
    PowerSeries.map (algebraMap weberBranchCoefficientField ℂ)
        (weberBranchSpacePowerSeries f) =
      ∑ i : Fin 3, (weberBranchCoefficientEquiv.symm f i : ℂ) •
        PowerSeries.map (Int.castRingHom ℂ) (weberSquareBranchIntegralQExpansion i) := by
  ext n
  simp [weberBranchSpacePowerSeries_coeff]

/-- The embedded canonical coefficient formula holds at every degree. -/
theorem coe_weberBranchSpacePowerSeries_coeff (f : weberBranchSpace) (n : ℕ) :
    ((weberBranchSpacePowerSeries f).coeff n : ℂ) =
      ∑ i : Fin 3, (weberBranchCoefficientEquiv.symm f i : ℂ) *
        ((weberSquareBranchIntegralQExpansion i).coeff n : ℂ) := by
  simpa only [PowerSeries.coeff_map, map_sum, PowerSeries.coeff_smul,
    Int.coe_castRingHom, smul_eq_mul, IntermediateField.algebraMap_apply] using
      congrArg (fun P : PowerSeries ℂ => P.coeff n) (map_weberBranchSpacePowerSeries f)

/-- Each entry of the integer branch array sums to its actual common-width
regularization at every upper-half-plane point. -/
theorem hasSum_weberSquareBranchIntegralQExpansion (i : Fin 3) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => ((weberSquareBranchIntegralQExpansion i).coeff n : ℂ) *
      Function.Periodic.qParam 24 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 24 (τ : ℂ) * weberSquareBranch i τ) := by
  fin_cases i
  · exact hasSum_weberSquareIntegralQExpansion τ
  · exact hasSum_weberF₁SquareIntegralQExpansion τ
  · exact hasSum_weberF₂SquareIntegralQExpansion τ

/-- The full canonical coefficient-field series converges to the actual
regularized function everywhere on `ℍ`. Only finite linear combinations are
formed after applying the complex embedding. -/
theorem hasSum_weberBranchSpacePowerSeries (f : weberBranchSpace) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => ((weberBranchSpacePowerSeries f).coeff n : ℂ) *
      Function.Periodic.qParam 24 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 24 (τ : ℂ) * (f : UpperHalfPlane → ℂ) τ) := by
  have hs := hasSum_sum (s := Finset.univ) (fun i _ =>
    (hasSum_weberSquareBranchIntegralQExpansion i τ).mul_left
      (weberBranchCoefficientEquiv.symm f i : ℂ))
  convert hs using 1
  · funext n
    rw [coe_weberBranchSpacePowerSeries_coeff, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  · rw [weberBranchSpace_eval, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

private theorem analyticAt_regularizedWeberSquareBranch (i : Fin 3) :
    AnalyticAt ℂ (cuspFunction 24 (regularizedWeberSquareBranch i)) 0 := by
  fin_cases i
  · apply analyticAt_cuspFunction_zero (by norm_num : (0 : ℝ) < 24)
      (by convert periodic_qParam_twentyFour_mul_weberF_sq.nat_mul 12 using 1; norm_num)
      mdifferentiable_qParam_twentyFour_mul_weberF_sq
      (tendsto_qParam_twentyFour_mul_weberF_sq.isBigO_one ℝ)
  · apply analyticAt_cuspFunction_zero (by norm_num : (0 : ℝ) < 24)
      (by convert periodic_qParam_twentyFour_mul_weberF₁_sq.nat_mul 12 using 1; norm_num)
      mdifferentiable_qParam_twentyFour_mul_weberF₁_sq
      (tendsto_qParam_twentyFour_mul_weberF₁_sq.isBigO_one ℝ)
  · exact analyticAt_cuspFunction_zero (by norm_num : (0 : ℝ) < 24)
      periodic_qParam_twentyFour_mul_weberF₂_sq
      mdifferentiable_qParam_twentyFour_mul_weberF₂_sq
      (tendsto_qParam_twentyFour_mul_weberF₂_sq.isBigO_one ℝ)

/-- The full width-24 q-expansion of the actual regularization is exactly the
complex embedding of its canonical coefficient-field power series. -/
theorem qExpansion_weberBranchSpace_eq_map (f : weberBranchSpace) :
    qExpansion 24 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * (f : UpperHalfPlane → ℂ) τ) =
      PowerSeries.map (algebraMap weberBranchCoefficientField ℂ)
        (weberBranchSpacePowerSeries f) := by
  let c : Fin 3 → ℂ := fun i => (weberBranchCoefficientEquiv.symm f i : ℂ)
  have hs (i : Fin 3) : AnalyticAt ℂ
      (cuspFunction 24 (c i • regularizedWeberSquareBranch i)) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul
      (analyticAt_regularizedWeberSquareBranch i).continuousAt]
    exact (analyticAt_regularizedWeberSquareBranch i).const_smul
  have h01 : AnalyticAt ℂ (cuspFunction 24
      (c 0 • regularizedWeberSquareBranch 0 + c 1 • regularizedWeberSquareBranch 1)) 0 := by
    rw [UpperHalfPlane.cuspFunction_add (hs 0).continuousAt (hs 1).continuousAt]
    exact (hs 0).add (hs 1)
  have hfun : (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * (f : UpperHalfPlane → ℂ) τ) =
      c 0 • regularizedWeberSquareBranch 0 + c 1 • regularizedWeberSquareBranch 1 +
        c 2 • regularizedWeberSquareBranch 2 := by
    funext τ
    rw [weberBranchSpace_eval, Fin.sum_univ_three]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, regularizedWeberSquareBranch, c]
    ring
  rw [hfun, UpperHalfPlane.qExpansion_add h01 (hs 2),
    UpperHalfPlane.qExpansion_add (hs 0) (hs 1)]
  simp only [UpperHalfPlane.qExpansion_smul (analyticAt_regularizedWeberSquareBranch _),
    qExpansion_regularizedWeberSquareBranch, map_weberBranchSpacePowerSeries,
    Fin.sum_univ_three, c]

end ModularForm
end
