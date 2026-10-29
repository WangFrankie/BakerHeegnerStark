/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Gamma.Roots
import BakerHeegnerStark.ComplexMultiplication.Gamma.Values
import BakerHeegnerStark.FieldTheory.AlgebraicConjugates
import BakerHeegnerStark.ModularForms.Gamma.ModularPolynomialRationality

/-!
# Gamma Rationality from Rational Twisted Modular Polynomials

A rational bivariate realization of the actual twisted cyclic-sublattice
products suffices for Weber's cube-root rationality theorem. At a shifted CM
point, the square of gamma is a common root of one such specialization and
`Z³ - j²`. Every conjugate over the actual j-generated field remains a common
root. The exact CM-root theorem makes all these conjugates equal, so their
simple extension has degree one. Dividing `j = gamma³` by the gamma square
then recovers gamma itself, with its zero value handled separately.
-/

open ModularForm Polynomial IntermediateField
open scoped Polynomial.Bivariate

noncomputable section

namespace BakerHeegnerStark

/-- Specializing a rational bivariate polynomial inside an intermediate field
and then including its coefficients in `ℂ` gives the actual complex specialization. -/
private theorem map_rational_bivariate_specialization
    (K : IntermediateField ℚ ℂ) (u : K) (Ψ : ℚ[X][Y]) :
    (Ψ.map (aeval u).toRingHom).map (algebraMap K ℂ) =
      aevalAeval (C (u : ℂ)) (X : ℂ[X]) Ψ := by
  have h : (Polynomial.mapRingHom (algebraMap K ℂ)).comp
      (Polynomial.mapRingHom (aeval u).toRingHom) =
      (aevalAeval (C (u : ℂ)) (X : ℂ[X]) : ℚ[X][Y] →ₐ[ℚ] ℂ[X]).toRingHom := by
    ext <;> simp [aevalAeval_C]
  exact congrArg (fun f : ℚ[X][Y] →+* ℂ[X] => f Ψ) h

/-- Rational bivariate realizations of the actual twisted gamma products imply
Weber's normalized cube-root rationality theorem (Cox, §12.A). The coefficient
hypothesis concerns the actual analytic products at every point and contains
no CM field-membership or class-number assumption. -/
theorem gammaTwoRationality_of_rational_gammaModularPolynomial
    (hmod : ∀ N : ℕ, 0 < N → N % 3 = 2 → ∃ Ψ : ℚ[X][Y],
      ∀ τ : UpperHalfPlane,
        aevalAeval (C (jInvariant τ)) (X : ℂ[X]) Ψ =
          cyclicSublatticeGammaPolynomial N τ) :
    GammaTwoRationality := by
  classical
  intro m hm hm4 hm3 _hmSq
  let K : IntermediateField ℚ ℂ := ℚ⟮jInvariant (cmPointShift m)⟯
  let α : ℂ := gamma₂ (cmPointShift m) ^ 2
  let jK : K := ⟨jInvariant (cmPointShift m), mem_adjoin_simple_self ℚ _⟩
  have hjK : algebraMap K ℂ jK = jInvariant (cmPointShift m) := rfl
  have hα : IsIntegral K α :=
    ((isIntegral_gamma₂_cmPointShift hm hm4).pow 2).tower_top
  obtain ⟨N, hN, hN3, hroot⟩ :=
    exists_level_gamma₂_cmPointShift_sq_isRoot hm hm4 hm3
  obtain ⟨Ψ, hΨ⟩ := hmod N (by omega) hN3
  let P : K[X] := Ψ.map (aeval jK).toRingHom
  have hPmap : P.map (algebraMap K ℂ) =
      cyclicSublatticeGammaPolynomial N (cmPointShift m) := by
    change (Ψ.map (aeval jK).toRingHom).map (algebraMap K ℂ) = _
    rw [map_rational_bivariate_specialization, hΨ (cmPointShift m)]
  have hPα : aeval α P = 0 := by
    rw [← eval_map_algebraMap, hPmap]
    exact hroot
  let Q : K[X] := X ^ 3 - C (jK ^ 2)
  have hQα : aeval α Q = 0 := by
    simp only [Q, map_sub, map_pow, aeval_X, aeval_C, hjK]
    change (gamma₂ (cmPointShift m) ^ 2) ^ 3 -
      jInvariant (cmPointShift m) ^ 2 = 0
    rw [← gamma₂_cube (cmPointShift m)]
    ring
  have hroots : ∀ x : ℂ, aeval x (minpoly K α) = 0 → x ∈ ({α} : Finset ℂ) := by
    intro x hx
    have hxP : aeval x P = 0 :=
      aeval_eq_zero_of_dvd_aeval_eq_zero (minpoly.dvd K α hPα) hx
    have hxQ : aeval x Q = 0 :=
      aeval_eq_zero_of_dvd_aeval_eq_zero (minpoly.dvd K α hQα) hx
    have hxroot : (cyclicSublatticeGammaPolynomial N (cmPointShift m)).IsRoot x := by
      change (cyclicSublatticeGammaPolynomial N (cmPointShift m)).eval x = 0
      rw [← hPmap, eval_map_algebraMap]
      exact hxP
    have hcube : x ^ 3 = jInvariant (cmPointShift m) ^ 2 := by
      simpa only [Q, map_sub, map_pow, aeval_X, aeval_C, hjK, sub_eq_zero] using hxQ
    have hxeq : x = α :=
      eq_gamma₂_cmPointShift_sq_of_isRoot_of_cube hm hm4 (by omega) hN3 hxroot hcube
    simpa only [Finset.mem_singleton] using hxeq
  have hle : Module.finrank K K⟮α⟯ ≤ 1 := by
    simpa only [Finset.card_singleton] using
      finrank_adjoin_le_card_of_minpoly_roots_subset α hα {α} hroots
  letI : FiniteDimensional K K⟮α⟯ := IntermediateField.adjoin.finiteDimensional hα
  have hpos : 0 < Module.finrank K K⟮α⟯ := Module.finrank_pos
  have hdegree : Module.finrank K K⟮α⟯ = 1 := by omega
  have hαbot : α ∈ (⊥ : IntermediateField K ℂ) :=
    finrank_adjoin_simple_eq_one_iff.mp hdegree
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hαbot
  have hαmem : α ∈ K := by
    change (a : ℂ) = α at ha
    exact ha ▸ a.property
  by_cases hγ : gamma₂ (cmPointShift m) = 0
  · rw [hγ]
    exact K.zero_mem
  · have hquot : jInvariant (cmPointShift m) / α ∈ K :=
      K.div_mem (mem_adjoin_simple_self ℚ _) hαmem
    have heq : jInvariant (cmPointShift m) / α = gamma₂ (cmPointShift m) := by
      change jInvariant (cmPointShift m) / gamma₂ (cmPointShift m) ^ 2 = _
      rw [← gamma₂_cube (cmPointShift m)]
      field_simp [hγ] <;> ring
    exact heq ▸ hquot

/-- Weber's cube-root rationality at the shifted CM point for `3 ∤ m`
(Cox, §12.A). The rational twisted modular polynomial and its exact unique
common root prove membership in the actual j-generated field, without a
CM reciprocity hypothesis. -/
theorem gammaTwoRationality : GammaTwoRationality :=
  gammaTwoRationality_of_rational_gammaModularPolynomial
    (fun _ hN hN3 => exists_rational_gammaModularPolynomial hN hN3)

end BakerHeegnerStark
