/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Orders.InertLattices
import BakerHeegnerStark.ComplexMultiplication.Orders.LatticeInvariant
import BakerHeegnerStark.EllipticFunctions.Uniformization.Curve
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Uniqueness

/-!
# Separation of Actual Period Lattices by the Analytic j-Invariant

Algebraic curve classification supplies a scaling with equal numerical
Weierstrass invariants. Analytic uniqueness recovers the actual scaled lattice,
so equality of analytic `j` is equivalent to homothety and modular equivalence.
For faithfully realized invertible order ideals, it also detects ideal classes.
In the nonexceptional inert family, the three roots of the level-two modular
equation at `(1+√-p)/2` are therefore pairwise distinct.
No CM algebraicity, integrality, or Galois reciprocity is assumed or concluded.
-/

open scoped Pointwise MatrixGroups nonZeroDivisors

namespace BakerHeegnerStark

/-- Analytic `j` separates complex homothety classes of actual period lattices,
including the two exceptional values `0` and `1728`. -/
theorem jInvariant_eq_iff_periodModule_homothety (τ σ : UpperHalfPlane) :
    ModularForm.jInvariant τ = ModularForm.jInvariant σ ↔
      ∃ α : ℂ, α ≠ 0 ∧ α • periodModule τ = periodModule σ := by
  constructor
  · intro hj
    obtain ⟨c, h₂, h₃⟩ := standardPeriodPair_exists_scale_of_jInvariant_eq τ σ hj
    refine ⟨c, c.ne_zero, ?_⟩
    have h := periodPair_lattice_eq_of_invariants
      (scalePeriodPair (standardPeriodPair τ) c) (standardPeriodPair σ) h₂ h₃
    rw [scalePeriodPair_lattice] at h
    exact h
  · rintro ⟨α, hα, heq⟩
    exact jInvariant_eq_of_periodModule_homothety τ σ α hα heq

/-- Two upper-half-plane parameters have equal analytic `j` precisely when
an integral modular transformation identifies them. -/
theorem jInvariant_eq_iff_modularOrbit (τ σ : UpperHalfPlane) :
    ModularForm.jInvariant τ = ModularForm.jInvariant σ ↔
      ∃ g : SL(2, ℤ), g • σ = τ :=
  (jInvariant_eq_iff_periodModule_homothety τ σ).trans
    (periodModule_homothety_iff_modularOrbit τ σ)

/-- For actual invertible integral ideals with faithful complex realizations,
analytic `j` equality detects equality in the actual order ideal-class group.
The two displayed period normalizations may use different nonzero scalars. -/
theorem jInvariant_eq_iff_idealClass_eq {R : Type*} [CommRing R] [IsDomain R]
    (f : R →ₐ[ℤ] ℂ) (hf : Function.Injective f) (A B : Ideal R)
    (I J : (FractionalIdeal R⁰ (FractionRing R))ˣ)
    (hI : (I : FractionalIdeal R⁰ (FractionRing R)) = A)
    (hJ : (J : FractionalIdeal R⁰ (FractionRing R)) = B)
    (τ σ : UpperHalfPlane) (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hA : Submodule.map f.toLinearMap (A.restrictScalars ℤ) = c • periodModule τ)
    (hB : Submodule.map f.toLinearMap (B.restrictScalars ℤ) = d • periodModule σ) :
    ModularForm.jInvariant τ = ModularForm.jInvariant σ ↔
      ClassGroup.mk (FractionRing R) I = ClassGroup.mk (FractionRing R) J :=
  (jInvariant_eq_iff_modularOrbit τ σ).trans
    (modularOrbit_iff_idealClass_eq f hf A B I J hI hJ τ σ c d hc hd hA hB)

/-- In the nonexceptional inert family, the three analytic roots of
`Φ₂(j((1+√-p)/2), Y)` are pairwise distinct. Their actual period lattices are
the three pairwise nonhomothetic lattices of the conductor-two order. -/
theorem inert_modularPolynomialTwo_roots_pairwise_distinct (p : ℕ) (hp8 : p % 8 = 3)
    (hp3 : 3 < p) :
    let τ := UpperHalfPlane.ofComplex ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2)
    ModularForm.jInvariant (UpperHalfPlane.ofComplex (2 * (τ : ℂ))) ≠
        ModularForm.jInvariant (UpperHalfPlane.ofComplex ((τ : ℂ) / 2)) ∧
      ModularForm.jInvariant (UpperHalfPlane.ofComplex (2 * (τ : ℂ))) ≠
        ModularForm.jInvariant (UpperHalfPlane.ofComplex (((τ : ℂ) + 1) / 2)) ∧
      ModularForm.jInvariant (UpperHalfPlane.ofComplex ((τ : ℂ) / 2)) ≠
        ModularForm.jInvariant (UpperHalfPlane.ofComplex (((τ : ℂ) + 1) / 2)) := by
  intro τ
  let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
  have hs : 0 < s.im := by
    simpa [s] using Real.sqrt_pos.mpr
      (show (0 : ℝ) < p by exact_mod_cast (by omega : 0 < p))
  have hcoe (z : ℂ) (hz : 0 < z.im) : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z :=
    congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos hz)
  have hτ : (τ : ℂ) = (1 + s) / 2 :=
    hcoe ((1 + s) / 2) (by simpa using div_pos hs (by norm_num : (0 : ℝ) < 2))
  have hroot₁ : 2 * (τ : ℂ) = 1 + s := by rw [hτ]; ring
  have hroot₂ : (τ : ℂ) / 2 = (1 + s) / 4 := by rw [hτ]; ring
  have hroot₃ : ((τ : ℂ) + 1) / 2 = (3 + s) / 4 := by rw [hτ]; ring
  have him₁ : 0 < (1 + s).im := by simpa using hs
  have him₂ : 0 < ((1 + s) / 4).im := by simpa using div_pos hs (by norm_num : (0 : ℝ) < 4)
  have him₃ : 0 < ((3 + s) / 4).im := by simpa using div_pos hs (by norm_num : (0 : ℝ) < 4)
  have hsqrt : periodModule (1 + s) = periodModule s := by
    simpa using periodModule_add_int s 1
  rw [hroot₁, hroot₂, hroot₃]
  refine ⟨?_, ?_, ?_⟩
  · intro hj
    obtain ⟨α, -, heq⟩ := (jInvariant_eq_iff_periodModule_homothety _ _).mp hj
    rw [hcoe _ him₁, hcoe _ him₂, hsqrt] at heq
    exact sqrt_periodModule_not_homothetic_quarter p (by omega) 1 ⟨α, by simpa using heq⟩
  · intro hj
    obtain ⟨α, -, heq⟩ := (jInvariant_eq_iff_periodModule_homothety _ _).mp hj
    rw [hcoe _ him₁, hcoe _ him₃, hsqrt] at heq
    exact sqrt_periodModule_not_homothetic_quarter p (by omega) 3 ⟨α, by simpa using heq⟩
  · intro hj
    obtain ⟨α, -, heq⟩ := (jInvariant_eq_iff_periodModule_homothety _ _).mp hj
    rw [hcoe _ him₂, hcoe _ him₃] at heq
    exact inert_quarter_periodModules_not_homothetic p hp8 hp3 ⟨α, heq⟩

end BakerHeegnerStark
