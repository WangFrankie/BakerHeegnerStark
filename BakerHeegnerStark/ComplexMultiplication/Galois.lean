/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.JInvariant.Coordinates
import BakerHeegnerStark.EllipticFunctions.Weierstrass.IsogenyLocalParameter
import BakerHeegnerStark.EllipticFunctions.Uniformization.Endomorphism

/-!
# Actual coefficient Galois compatibility of quadratic-period CM

Finite actual point-coordinate formulas for conjugated CM yield analytic
remainders and a genuine analytic local lift at infinity. Its differential is
`σ(τ)`. Actual point-group differential uniqueness then identifies the
conjugated map globally with multiplication of the period argument by `σ(τ)`.
Only finite field formulas are conjugated; no continuity of `σ` is assumed.

Consequently coefficient automorphisms fixing the quadratic period commute
with actual CM on the j-generated curve model and every torsion subgroup,
including level zero. At every positive level their genuine Galois matrices
centralize the specified CM companion matrix. Modular-function evaluation
compatibility and the remaining Weber fixed-field conclusion are not asserted
by these point-group and torsion results.
-/

open scoped IntermediateField Matrix Topology
namespace BakerHeegnerStark

/-- Actual coefficient-conjugate CM has a genuine analytic lift with conjugated-period differential. -/
theorem periodCMGaloisConjugate_exists_analytic_lift [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ HasDerivAt g (σ (τ : ℂ)) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), periodCMGaloisConjugate τ m hτ σ (standardPeriodPoint τ z) =
        standardPeriodPoint τ (g z) := by
  have hτ0 : (τ : ℂ) ≠ 0 := by
    intro h
    exact (ne_of_gt τ.im_pos) (by simpa using congrArg Complex.im h)
  have hd : σ (τ : ℂ) ≠ 0 := by
    intro h
    apply hτ0
    apply σ.injective
    simpa only [map_zero] using h
  have hab : (((σ (τ : ℂ)) ^ 2)⁻¹) ^ 3 = (((σ (τ : ℂ)) ^ 3)⁻¹) ^ 2 := by
    field_simp [hd]
  have hratio : ((σ (τ : ℂ)) ^ 2)⁻¹ / ((σ (τ : ℂ)) ^ 3)⁻¹ = σ (τ : ℂ) := by
    field_simp [hd]
  obtain ⟨g, hg, hg₀, hgd, hlocal⟩ :=
    periodCurveEnd_exists_analytic_lift_of_finite_coordinates τ (⟨0, hm⟩ : Fin m)
      (periodCMConjugateKernelPoint τ m hm hτ σ)
      (periodCMConjugateKernelPoint_zero τ m hm hτ σ)
      (fun i hi hq => hi ((periodCMConjugateKernelPoint_eq_zero_iff τ m hm hτ σ i).mp hq))
      (((σ (τ : ℂ)) ^ 2)⁻¹) (((σ (τ : ℂ)) ^ 3)⁻¹)
      (inv_ne_zero (pow_ne_zero 3 hd)) hab (periodCMGaloisConjugate τ m hτ σ)
      (periodCurveX_CMGaloisConjugate_finite_sum τ m hm hτ σ)
      (periodCurveY_CMGaloisConjugate_finite_sum τ m hm hτ σ)
  exact ⟨g, hg, hg₀, by simpa only [hratio] using hgd, hlocal⟩

/-- Coefficient conjugation sends the actual CM uniformizing scalar to `σ(τ)`, globally. -/
theorem periodCMGaloisConjugate_apply_standardPeriodPoint [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) (z : ℂ) :
    periodCMGaloisConjugate τ m hτ σ (standardPeriodPoint τ z) =
      standardPeriodPoint τ ((σ (τ : ℂ)) * z) := by
  obtain ⟨g, hg, hg₀, hdg, hlocal⟩ := periodCMGaloisConjugate_exists_analytic_lift τ m hm hτ σ
  have h := periodCurveEnd_apply_of_analytic_lift τ (periodCMGaloisConjugate τ m hτ σ)
    hg hg₀ hlocal z
  simpa only [hdg.deriv] using h

/-- Fixing the quadratic period preserves the actual CM endomorphism under coefficient conjugation. -/
theorem periodCMGaloisConjugate_eq_CM [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) (hσ : σ (τ : ℂ) = (τ : ℂ)) :
    periodCMGaloisConjugate τ m hτ σ =
      periodCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ) := by
  ext P
  obtain ⟨z, rfl⟩ := standardPeriodPoint_surjective τ P
  rw [periodCMGaloisConjugate_apply_standardPeriodPoint τ m hm hτ σ z, hσ,
    periodCurveCMEnd_standardPeriodPoint]

/-- Coefficient automorphisms fixing the quadratic period commute with actual model CM at every point. -/
theorem jInvariantCurveCMEnd_galois_commute [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) (hσ : σ (τ : ℂ) = (τ : ℂ))
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
        (jInvariantCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ) P) =
      jInvariantCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ)
        ((weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd P) := by
  let e := jInvariantCurvePointEquiv τ
  let s := (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
  have h := DFunLike.congr_fun (periodCMGaloisConjugate_eq_CM τ m hm hτ σ hσ) (e.symm (s P))
  have he := congrArg e h
  simpa [periodCMGaloisConjugate, jInvariantCurveCMEnd, e, s] using he

/-- Actual coefficient Galois and CM actions commute on every torsion subgroup when the period is fixed. -/
theorem jInvariantCurveTorsionCMEnd_galois_commute [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) (hσ : σ (τ : ℂ) = (τ : ℂ))
    (N : ℕ) (P : WeierstrassTorsion (jInvariantCurve τ).toAffine ℂ N) :
    (weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd
        (jInvariantCurveTorsionCMEnd τ N m (by simpa only [Int.cast_natCast] using hτ) P) =
      jInvariantCurveTorsionCMEnd τ N m (by simpa only [Int.cast_natCast] using hτ)
        ((weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd P) := by
  apply Subtype.ext
  change (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd
      (jInvariantCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ) P) =
    jInvariantCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ)
      ((weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd P)
  exact jInvariantCurveCMEnd_galois_commute τ m hm hτ σ hσ P

/-- At every positive level, the genuine fixed-period Galois matrix centralizes the actual CM matrix. -/
theorem jInvariantCurveTorsionGaloisMatrix_commute_CM [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) (hσ : σ (τ : ℂ) = (τ : ℂ))
    (N : ℕ) (hN : 0 < N) :
    Commute (jInvariantCurveTorsionGaloisMatrix τ N hN σ : Matrix (Fin 2) (Fin 2) (ZMod N))
      !![0, -(m : ZMod N); 1, 0] := by
  have h := (jInvariantCurveTorsionGaloisMatrix_commute_iff τ N hN m
    (by simpa only [Int.cast_natCast] using hτ) σ).mpr
      (jInvariantCurveTorsionCMEnd_galois_commute τ m hm hτ σ hσ N)
  simpa only [Int.cast_natCast] using h

end BakerHeegnerStark
