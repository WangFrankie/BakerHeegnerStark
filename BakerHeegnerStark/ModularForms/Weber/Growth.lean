/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.BranchSpace
import BakerHeegnerStark.ModularForms.Weber.Bounds
import BakerHeegnerStark.ModularForms.CyclicSublattice.Basic

/-!
# Holomorphicity and cusp growth of the actual Weber branch space

Every element of the concrete three-dimensional Weber function space is
holomorphic and grows at most linearly in the actual `j`-invariant at infinity.
The proof uses its canonical finite basis expansion. The normalized `T` and `S`
identities express each actual branch as a unit-norm phase times a modular
transform of the original Weber square, whose cubic gives a global norm bound.
In particular these conclusions apply to every actual coefficient or modular
transform in the space, without any hypothesis about CM evaluation or the
continuity of field automorphisms.
-/

open UpperHalfPlane Filter Asymptotics
open scoped Topology Manifold MatrixGroups

noncomputable section
namespace ModularForm

private theorem exists_weberSquareBranch_eq_phase_mul_weberF_sq (i : Fin 3) :
    ∃ (g : SL(2, ℤ)) (c : ℂ), ‖c‖ = 1 ∧ ∀ τ : UpperHalfPlane,
      weberSquareBranch i τ = c * weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2 := by
  have hphase : (zeta48 ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 zeta48_ne_zero
  have hnorm : ‖(zeta48 ^ 2 : ℂ)‖ = 1 := by
    rw [zeta48_sq, Complex.norm_exp]
    simp
  have hT (τ : UpperHalfPlane) :
      weberSquareBranch 0 (ModularGroup.T • τ) =
        (zeta48 ^ 2)⁻¹ * weberSquareBranch 1 τ := by
    simpa only [show (0 : Fin 3) ≠ 2 by decide, ite_false,
      Equiv.swap_apply_left, zpow_neg_one] using weberSquareBranch_T 0 τ
  have hTS (τ : UpperHalfPlane) :
      weberSquareBranch 0 ((ModularGroup.T * ModularGroup.S) • τ) =
        (zeta48 ^ 2)⁻¹ * weberSquareBranch 2 τ := by
    rw [mul_smul, hT, weberSquareBranch_S, Equiv.swap_apply_left]
  fin_cases i
  · exact ⟨1, 1, norm_one, by intro τ; simp [weberSquareBranch]⟩
  · refine ⟨ModularGroup.T, zeta48 ^ 2, hnorm, ?_⟩
    intro τ
    change weberSquareBranch 1 τ =
      zeta48 ^ 2 * weberSquareBranch 0 (ModularGroup.T • τ)
    rw [hT, ← mul_assoc, mul_inv_cancel₀ hphase, one_mul]
  · refine ⟨ModularGroup.T * ModularGroup.S, zeta48 ^ 2, hnorm, ?_⟩
    intro τ
    change weberSquareBranch 2 τ =
      zeta48 ^ 2 * weberSquareBranch 0 ((ModularGroup.T * ModularGroup.S) • τ)
    rw [hTS, ← mul_assoc, mul_inv_cancel₀ hphase, one_mul]

/-- Every actual Weber-square branch is holomorphic on the upper half-plane. -/
theorem mdifferentiable_weberSquareBranch (i : Fin 3) :
    MDiff (weberSquareBranch i) := by
  obtain ⟨g, c, _, he⟩ := exists_weberSquareBranch_eq_phase_mul_weberF_sq i
  have hW : MDiff (fun τ : UpperHalfPlane => weberF (τ : ℂ)) :=
    fun τ => (analyticOnNhd_weberF (τ : ℂ) τ.im_pos).differentiableAt.mdifferentiableAt.comp
      τ τ.mdifferentiable_coe
  have hg : MDiff (fun τ : UpperHalfPlane => g • τ) := by
    simpa using UpperHalfPlane.mdifferentiable_smul
      (g := (g : GL (Fin 2) ℝ)) (by simp)
  have hf : weberSquareBranch i =
      fun τ : UpperHalfPlane => c * weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2 :=
    funext he
  rw [hf]
  exact mdifferentiable_const.mul ((hW.pow 2).comp hg)

/-- The actual Weber cubic gives a root-free linear norm bound, uniformly in the
integral modular transformation and throughout the upper half-plane. -/
theorem norm_weberF_sq_smul_le (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ‖weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2‖ ≤ 1024 + 8 * ‖jInvariant τ‖ := by
  by_cases h : ‖weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2‖ ≤ 1
  · nlinarith [norm_nonneg (jInvariant τ)]
  · have hpow : ‖weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2‖ ≤
        ‖weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2‖ ^ 24 := by
      simpa only [pow_one] using
        pow_le_pow_right₀ (le_of_not_ge h) (by decide : 1 ≤ (24 : ℕ))
    exact hpow.trans (norm_weberF_sq_smul_pow_24_le g τ)

/-- All three actual branches satisfy the same global norm bound. -/
theorem norm_weberSquareBranch_le (i : Fin 3) (τ : UpperHalfPlane) :
    ‖weberSquareBranch i τ‖ ≤ 1024 + 8 * ‖jInvariant τ‖ := by
  obtain ⟨g, c, hc, he⟩ := exists_weberSquareBranch_eq_phase_mul_weberF_sq i
  rw [he, norm_mul, hc, one_mul]
  exact norm_weberF_sq_smul_le g τ

/-- Every actual branch has at most linear `j`-growth at infinity. -/
theorem isBigO_weberSquareBranch_jInvariant (i : Fin 3) :
    weberSquareBranch i =O[atImInfty] jInvariant := by
  apply IsBigO.of_bound 1032
  filter_upwards [BakerHeegnerStark.eventually_one_le_norm_jInvariant] with τ hτ
  have h := norm_weberSquareBranch_le i τ
  nlinarith

/-- Every actual function in the Weber branch space is holomorphic. -/
theorem mdifferentiable_weberBranchSpace (f : weberBranchSpace) :
    MDiff (f : UpperHalfPlane → ℂ) := by
  have hf : (f : UpperHalfPlane → ℂ) =
      ∑ i : Fin 3, fun τ : UpperHalfPlane =>
        (weberBranchCoefficientEquiv.symm f i : ℂ) * weberSquareBranch i τ := by
    funext τ
    simpa only [Finset.sum_apply] using weberBranchSpace_eval f τ
  rw [hf]
  apply MDifferentiable.sum
  intro i _
  exact mdifferentiable_const.mul (mdifferentiable_weberSquareBranch i)

/-- The canonical coefficients give an explicit global bound for the actual
function, not for an independently chosen formal coefficient vector. -/
theorem norm_weberBranchSpace_le (f : weberBranchSpace) (τ : UpperHalfPlane) :
    ‖(f : UpperHalfPlane → ℂ) τ‖ ≤
      (∑ i : Fin 3, ‖(weberBranchCoefficientEquiv.symm f i : ℂ)‖) *
        (1024 + 8 * ‖jInvariant τ‖) := by
  rw [weberBranchSpace_eval, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_weberSquareBranch_le i τ) (norm_nonneg _)

/-- Every actual function in the Weber branch space has polynomial cusp growth;
the exponent one already suffices. -/
theorem isBigO_weberBranchSpace_jInvariant (f : weberBranchSpace) :
    (f : UpperHalfPlane → ℂ) =O[atImInfty] jInvariant := by
  apply IsBigO.of_bound
    (1032 * ∑ i : Fin 3, ‖(weberBranchCoefficientEquiv.symm f i : ℂ)‖)
  filter_upwards [BakerHeegnerStark.eventually_one_le_norm_jInvariant] with τ hτ
  have hbound : 1024 + 8 * ‖jInvariant τ‖ ≤ 1032 * ‖jInvariant τ‖ := by
    nlinarith
  calc
    ‖(f : UpperHalfPlane → ℂ) τ‖ ≤
        (∑ i : Fin 3, ‖(weberBranchCoefficientEquiv.symm f i : ℂ)‖) *
          (1024 + 8 * ‖jInvariant τ‖) := norm_weberBranchSpace_le f τ
    _ ≤ (∑ i : Fin 3, ‖(weberBranchCoefficientEquiv.symm f i : ℂ)‖) *
          (1032 * ‖jInvariant τ‖) :=
      mul_le_mul_of_nonneg_left hbound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by ring

end ModularForm
