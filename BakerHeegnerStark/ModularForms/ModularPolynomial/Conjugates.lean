/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.Monic
import BakerHeegnerStark.ModularForms.JInvariant.Surjectivity
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Modular Polynomial Root Multiplicities under Field Embeddings

The integral modular polynomial specializes over any coefficient field.
Injective field maps preserve its root multiplicities. Together with actual
j-surjectivity, this realizes each embedded j-value by an upper-half-plane
point with the same diagonal root multiplicities at every positive level.
This does not yet identify the CM order of the resulting point.
-/

open ModularForm Polynomial
open scoped Polynomial.Bivariate

noncomputable section

namespace BakerHeegnerStark

/-- Mapping an integral modular-polynomial specialization is the actual complex
specialization at the mapped value. -/
theorem map_modularPolynomial_specialization {K : Type*} [CommRing K]
    (f : K →+* ℂ) (u : K) (Φ : ℤ[X][Y]) :
    (Φ.map (eval₂RingHom (Int.castRingHom K) u)).map f =
      aevalAeval (C (f u)) X Φ := by
  rw [Polynomial.map_map, aevalAeval_C_X_eq_map]
  have h : f.comp (eval₂RingHom (Int.castRingHom K) u) =
      (aeval (f u) : ℤ[X] →ₐ[ℤ] ℂ).toRingHom := by
    ext <;> simp
  rw [h]

/-- Two embeddings of the same field element preserve the multiplicity of the
actual j-value in every actual cyclic-sublattice polynomial. -/
theorem rootMultiplicity_cyclicSublatticePolynomial_eq_of_embeddings
    {K : Type*} [Field K] (ι σ : K →+* ℂ) (u : K)
    {τ τ' : UpperHalfPlane} (hτ : jInvariant τ = ι u) (hτ' : jInvariant τ' = σ u)
    {N : ℕ} (hN : 0 < N) :
    rootMultiplicity (jInvariant τ) (cyclicSublatticePolynomial N τ) =
      rootMultiplicity (jInvariant τ') (cyclicSublatticePolynomial N τ') := by
  obtain ⟨Φ, hΦ, _⟩ := modularPolynomialTheorem N hN
  let P : K[X] := Φ.map (eval₂RingHom (Int.castRingHom K) u)
  have hmap (f : K →+* ℂ) (z : UpperHalfPlane) (hz : jInvariant z = f u) :
      P.map f = cyclicSublatticePolynomial N z := by
    change (Φ.map (eval₂RingHom (Int.castRingHom K) u)).map f = _
    rw [map_modularPolynomial_specialization, ← hz, hΦ z]
    rfl
  calc
    _ = rootMultiplicity (ι u) (P.map ι) := by rw [hτ, hmap ι τ hτ]
    _ = rootMultiplicity u P := (eq_rootMultiplicity_map ι.injective u).symm
    _ = rootMultiplicity (σ u) (P.map σ) := eq_rootMultiplicity_map σ.injective u
    _ = _ := by rw [hmap σ τ' hτ', ← hτ']

/-- An embedded j-value has an actual upper-half-plane representative preserving
all positive-level diagonal root multiplicities simultaneously. No CM or
algebraicity hypothesis is needed for this analytic-algebraic statement. -/
theorem exists_jInvariant_embedding_preserving_rootMultiplicity
    {K : Type*} [Field K] (ι σ : K →+* ℂ) (u : K)
    (τ₀ : UpperHalfPlane) (hτ₀ : jInvariant τ₀ = ι u) :
    ∃ τ : UpperHalfPlane, jInvariant τ = σ u ∧
      ∀ N : ℕ, 0 < N →
        rootMultiplicity (jInvariant τ₀) (cyclicSublatticePolynomial N τ₀) =
          rootMultiplicity (jInvariant τ) (cyclicSublatticePolynomial N τ) := by
  obtain ⟨τ, hτ⟩ := jInvariant_surjective (σ u)
  exact ⟨τ, hτ, fun _ hN =>
    rootMultiplicity_cyclicSublatticePolynomial_eq_of_embeddings ι σ u hτ₀ hτ hN⟩

/-- Every algebraic conjugate of an actual algebraic j-value is realized by an
actual j-value with the same diagonal root multiplicities at all positive levels.
This preserves modular-equation data, not yet the quadratic CM order. -/
theorem exists_jInvariant_minpoly_root_preserving_rootMultiplicity
    (τ₀ : UpperHalfPlane) (hj : IsIntegral ℚ (jInvariant τ₀))
    {x : ℂ} (hx : aeval x (minpoly ℚ (jInvariant τ₀)) = 0) :
    ∃ τ : UpperHalfPlane, jInvariant τ = x ∧
      ∀ N : ℕ, 0 < N →
        rootMultiplicity (jInvariant τ₀) (cyclicSublatticePolynomial N τ₀) =
          rootMultiplicity (jInvariant τ) (cyclicSublatticePolynomial N τ) := by
  let xr : { z : ℂ // z ∈ (minpoly ℚ (jInvariant τ₀)).aroots ℂ } :=
    ⟨x, Polynomial.mem_aroots.mpr ⟨minpoly.ne_zero hj, hx⟩⟩
  let σ : IntermediateField.adjoin ℚ {jInvariant τ₀} →ₐ[ℚ] ℂ :=
    (IntermediateField.algHomAdjoinIntegralEquiv ℚ hj).symm xr
  let u := IntermediateField.AdjoinSimple.gen ℚ (jInvariant τ₀)
  obtain ⟨τ, hτ, hroot⟩ := exists_jInvariant_embedding_preserving_rootMultiplicity
    (algebraMap (IntermediateField.adjoin ℚ {jInvariant τ₀}) ℂ) σ.toRingHom u τ₀
    (IntermediateField.AdjoinSimple.algebraMap_gen ℚ (jInvariant τ₀)).symm
  have hgen : σ u = x :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hj xr
  exact ⟨τ, hτ.trans hgen, hroot⟩

end BakerHeegnerStark
