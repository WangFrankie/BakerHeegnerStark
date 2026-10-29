/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Algebra.Module.Submodule.Pointwise
import BakerHeegnerStark.ModularForms.JInvariant.Basic

/-!
# Weierstrass Lattice Invariants and Modular Forms

The actual lattice sums of the standard period pair `1,τ` agree with the
normalized Eisenstein series, including their powers of π. We reuse mathlib's
proved all-pairs/primitive-pairs summation formula rather than reconstructing
the gcd decomposition. This analytic module has no QNF dependency.
-/

namespace BakerHeegnerStark

/-- The positively oriented standard period pair attached to an upper-half-plane point. -/
noncomputable def standardPeriodPair (τ : UpperHalfPlane) : PeriodPair := by
  refine ⟨1, τ, ?_⟩
  rw [linearIndependent_fin2]
  change (τ : ℂ) ≠ 0 ∧ ∀ a : ℝ, a • (τ : ℂ) ≠ 1
  constructor
  · intro h
    have := congrArg Complex.im h
    simpa using (ne_of_gt τ.im_pos) this
  · intro a ha
    have hi := congrArg Complex.im ha
    simp only [Complex.smul_im, smul_eq_mul, Complex.one_im] at hi
    have ha0 : a = 0 := (mul_eq_zero.mp hi).resolve_right (ne_of_gt τ.im_pos)
    simp [ha0] at ha

/-- Reindex the actual lattice sum by all integer pairs, with the coefficient
order matched to mathlib's Eisenstein summand. -/
theorem standardPeriodPair_G_eq_eisSummand (τ : UpperHalfPlane) (k : ℕ) :
    (standardPeriodPair τ).G k =
      ∑' v : Fin 2 → ℤ, EisensteinSeries.eisSummand (k : ℤ) v τ := by
  let e : (Fin 2 → ℤ) ≃ (standardPeriodPair τ).lattice :=
    ((finTwoArrowEquiv ℤ).trans (Equiv.prodComm ℤ ℤ)).trans
      (standardPeriodPair τ).latticeEquivProd.symm.toEquiv
  have he (v : Fin 2 → ℤ) : ((e v : (standardPeriodPair τ).lattice) : ℂ) =
      (v 1 : ℂ) + (v 0 : ℂ) * (τ : ℂ) := by
    change (((standardPeriodPair τ).latticeEquivProd.symm (v 1, v 0) :
      (standardPeriodPair τ).lattice) : ℂ) = _
    rw [PeriodPair.latticeEquiv_symm_apply]
    simp only [standardPeriodPair, mul_one]
  rw [PeriodPair.G, ← e.tsum_eq]
  apply tsum_congr
  intro v
  rw [he]
  simp [EisensteinSeries.eisSummand, add_comm]

/-- The actual lattice sum differs from the normalized modular form by `2ζ(k)`. -/
theorem standardPeriodPair_G_eq_zeta_mul_E (τ : UpperHalfPlane) (k : ℕ) (hk : 3 ≤ k) :
    (standardPeriodPair τ).G k =
      2 * riemannZeta (k : ℂ) * ModularForm.E hk τ := by
  rw [standardPeriodPair_G_eq_eisSummand,
    tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ]
  rw [show ModularForm.E hk τ =
    (1 / 2 : ℂ) • EisensteinSeries.eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
    EisensteinSeries.eisensteinSeriesSIF_apply]
  simp only [smul_eq_mul]
  ring

/-- The sixth zeta value, computed from mathlib's proved even-value formula. -/
theorem riemannZeta_six : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have hb : bernoulli 6 = (1 / 42 : ℚ) := by decide +kernel
  have h := riemannZeta_two_mul_nat (k := 3) (by decide)
  norm_num [hb] at h
  linear_combination h

/-- The actual fourth-power lattice sum has the classical `π⁴/45` normalization. -/
theorem standardPeriodPair_G_four (τ : UpperHalfPlane) :
    (standardPeriodPair τ).G 4 = (Real.pi : ℂ) ^ 4 / 45 * ModularForm.E₄ τ := by
  rw [standardPeriodPair_G_eq_zeta_mul_E τ 4 (by decide)]
  norm_num only [Nat.cast_ofNat]
  rw [riemannZeta_four]
  ring

/-- The actual sixth-power lattice sum has the classical `2π⁶/945` normalization. -/
theorem standardPeriodPair_G_six (τ : UpperHalfPlane) :
    (standardPeriodPair τ).G 6 = 2 * (Real.pi : ℂ) ^ 6 / 945 * ModularForm.E₆ τ := by
  rw [standardPeriodPair_G_eq_zeta_mul_E τ 6 (by decide)]
  norm_num only [Nat.cast_ofNat]
  rw [riemannZeta_six]
  ring

/-- The actual Weierstrass invariant `g₂` of `ℤ+ℤτ`. -/
theorem standardPeriodPair_g₂ (τ : UpperHalfPlane) :
    (standardPeriodPair τ).g₂ = 4 * (Real.pi : ℂ) ^ 4 / 3 * ModularForm.E₄ τ := by
  rw [PeriodPair.g₂, standardPeriodPair_G_four]
  ring

/-- The actual Weierstrass invariant `g₃` of `ℤ+ℤτ`. -/
theorem standardPeriodPair_g₃ (τ : UpperHalfPlane) :
    (standardPeriodPair τ).g₃ = 8 * (Real.pi : ℂ) ^ 6 / 27 * ModularForm.E₆ τ := by
  rw [PeriodPair.g₃, standardPeriodPair_G_six]
  ring

/-- The actual lattice discriminant is the modular discriminant with its
classical nonzero factor; no abstract elliptic-curve realization is assumed. -/
theorem standardPeriodPair_discriminant (τ : UpperHalfPlane) :
    (standardPeriodPair τ).g₂ ^ 3 - 27 * (standardPeriodPair τ).g₃ ^ 2 =
      4096 * (Real.pi : ℂ) ^ 12 * ModularForm.discriminant τ := by
  rw [standardPeriodPair_g₂, standardPeriodPair_g₃,
    ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

/-- The Weierstrass equation obtained from the actual lattice is nonsingular. -/
theorem standardPeriodPair_discriminant_ne_zero (τ : UpperHalfPlane) :
    (standardPeriodPair τ).g₂ ^ 3 - 27 * (standardPeriodPair τ).g₃ ^ 2 ≠ 0 := by
  rw [standardPeriodPair_discriminant]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt Real.pi_pos)
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 12 hπ))
    (ModularForm.discriminant_ne_zero τ)

/-- Multiply both actual periods by a nonzero complex scalar. -/
noncomputable def scalePeriodPair (L : PeriodPair) (c : ℂˣ) : PeriodPair := by
  refine ⟨(c : ℂ) * L.ω₁, (c : ℂ) * L.ω₂, ?_⟩
  have hi := L.indep
  rw [linearIndependent_fin2] at hi ⊢
  change L.ω₂ ≠ 0 ∧ ∀ a : ℝ, a • L.ω₂ ≠ L.ω₁ at hi
  change (c : ℂ) * L.ω₂ ≠ 0 ∧ ∀ a : ℝ, a • ((c : ℂ) * L.ω₂) ≠ (c : ℂ) * L.ω₁
  constructor
  · exact mul_ne_zero c.ne_zero hi.1
  · intro a ha
    apply hi.2 a
    apply mul_left_cancel₀ c.ne_zero
    simpa only [Algebra.mul_smul_comm] using ha

open scoped Pointwise

/-- Scaling the actual periods scales their integer lattice in the ambient plane. -/
theorem scalePeriodPair_lattice (L : PeriodPair) (c : ℂˣ) :
    (scalePeriodPair L c).lattice = (c : ℂ) • L.lattice := by
  simp [PeriodPair.lattice, scalePeriodPair, Submodule.smul_span,
    Set.smul_set_insert, Set.smul_set_singleton, smul_eq_mul]

/-- The actual lattice power sums have weight minus their exponent. -/
theorem scalePeriodPair_G (L : PeriodPair) (c : ℂˣ) (k : ℕ) :
    (scalePeriodPair L c).G k = ((c : ℂ) ^ k)⁻¹ * L.G k := by
  let e := (scalePeriodPair L c).latticeEquivProd.symm.toEquiv
  let f := L.latticeEquivProd.symm.toEquiv
  rw [PeriodPair.G, ← e.tsum_eq, PeriodPair.G, ← f.tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro x
  dsimp only [e, f]
  change (((scalePeriodPair L c).latticeEquivProd.symm x : ℂ) ^ k)⁻¹ =
    ((c : ℂ) ^ k)⁻¹ * ((L.latticeEquivProd.symm x : ℂ) ^ k)⁻¹
  rw [PeriodPair.latticeEquiv_symm_apply, PeriodPair.latticeEquiv_symm_apply]
  change ((((x.1 : ℤ) : ℂ) * ((c : ℂ) * L.ω₁) +
    ((x.2 : ℤ) : ℂ) * ((c : ℂ) * L.ω₂)) ^ k)⁻¹ = _
  have heq : ((x.1 : ℤ) : ℂ) * ((c : ℂ) * L.ω₁) +
      ((x.2 : ℤ) : ℂ) * ((c : ℂ) * L.ω₂) =
      (c : ℂ) * (((x.1 : ℤ) : ℂ) * L.ω₁ + ((x.2 : ℤ) : ℂ) * L.ω₂) := by ring
  rw [heq, mul_pow, mul_inv]

/-- The actual first Weierstrass invariant has weight minus four. -/
theorem scalePeriodPair_g₂ (L : PeriodPair) (c : ℂˣ) :
    (scalePeriodPair L c).g₂ = ((c : ℂ) ^ 4)⁻¹ * L.g₂ := by
  rw [PeriodPair.g₂, scalePeriodPair_G, PeriodPair.g₂]
  ring

/-- The actual second Weierstrass invariant has weight minus six. -/
theorem scalePeriodPair_g₃ (L : PeriodPair) (c : ℂˣ) :
    (scalePeriodPair L c).g₃ = ((c : ℂ) ^ 6)⁻¹ * L.g₃ := by
  rw [PeriodPair.g₃, scalePeriodPair_G, PeriodPair.g₃]
  ring

/-- The classical algebraic `j` expression of the actual period invariants is
the analytic modular `j`, with the same normalization at every point. -/
theorem standardPeriodPair_j (τ : UpperHalfPlane) :
    1728 * (standardPeriodPair τ).g₂ ^ 3 /
      ((standardPeriodPair τ).g₂ ^ 3 - 27 * (standardPeriodPair τ).g₃ ^ 2) =
        ModularForm.jInvariant τ := by
  rw [standardPeriodPair_discriminant, standardPeriodPair_g₂, ModularForm.jInvariant]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt Real.pi_pos)
  field_simp [hπ, ModularForm.discriminant_ne_zero τ]
  ring

/-- Homothety of the actual lattices gives the weight-minus-two transformation
of their Weierstrass functions, including the prescribed values at poles. -/
theorem scalePeriodPair_weierstrassP (L : PeriodPair) (c : ℂˣ) (z : ℂ) :
    (scalePeriodPair L c).weierstrassP ((c : ℂ) * z) =
      ((c : ℂ) ^ 2)⁻¹ * L.weierstrassP z := by
  let e := (scalePeriodPair L c).latticeEquivProd.symm.toEquiv
  let f := L.latticeEquivProd.symm.toEquiv
  rw [PeriodPair.weierstrassP, ← e.tsum_eq, PeriodPair.weierstrassP,
    ← f.tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro x
  dsimp only [e, f]
  change (1 / ((c : ℂ) * z -
      ((scalePeriodPair L c).latticeEquivProd.symm x : ℂ)) ^ 2 -
    1 / ((scalePeriodPair L c).latticeEquivProd.symm x : ℂ) ^ 2) =
    ((c : ℂ) ^ 2)⁻¹ * (1 / (z - (L.latticeEquivProd.symm x : ℂ)) ^ 2 -
      1 / (L.latticeEquivProd.symm x : ℂ) ^ 2)
  rw [PeriodPair.latticeEquiv_symm_apply, PeriodPair.latticeEquiv_symm_apply]
  change (1 / ((c : ℂ) * z - (((x.1 : ℤ) : ℂ) * ((c : ℂ) * L.ω₁) +
      ((x.2 : ℤ) : ℂ) * ((c : ℂ) * L.ω₂))) ^ 2 -
    1 / (((x.1 : ℤ) : ℂ) * ((c : ℂ) * L.ω₁) +
      ((x.2 : ℤ) : ℂ) * ((c : ℂ) * L.ω₂)) ^ 2) = _
  have heq : ((x.1 : ℤ) : ℂ) * ((c : ℂ) * L.ω₁) +
      ((x.2 : ℤ) : ℂ) * ((c : ℂ) * L.ω₂) =
      (c : ℂ) * (((x.1 : ℤ) : ℂ) * L.ω₁ + ((x.2 : ℤ) : ℂ) * L.ω₂) := by ring
  rw [heq]
  simp only [← mul_sub, one_div, mul_pow, mul_inv]

/-- The actual pole locus recovers the period lattice from the Weierstrass
function. Recovery from the numerical invariants uses analytic continuation. -/
theorem weierstrassP_eq_iff_lattice_eq (L M : PeriodPair) :
    L.weierstrassP = M.weierstrassP ↔ L.lattice = M.lattice := by
  constructor
  · intro h
    have hle (L M : PeriodPair) (h : L.weierstrassP = M.weierstrassP) :
        L.lattice ≤ M.lattice := by
      intro z hz
      by_contra hm
      apply L.not_continuousAt_weierstrassP z hz
      rw [h]
      exact (M.analyticOnNhd_weierstrassP z hm).continuousAt
    exact le_antisymm (hle L M h) (hle M L h.symm)
  · intro h
    funext z
    let e : L.lattice ≃ M.lattice := (LinearEquiv.ofEq L.lattice M.lattice h).toEquiv
    have he (l : L.lattice) : (e l : ℂ) = l := rfl
    simpa only [PeriodPair.weierstrassP, he] using
      e.tsum_eq (fun l : M.lattice => 1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)

end BakerHeegnerStark
