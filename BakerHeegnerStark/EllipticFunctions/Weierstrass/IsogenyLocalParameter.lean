/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticCurves.JInvariant.Coordinates
import BakerHeegnerStark.EllipticFunctions.Weierstrass.AnalyticLift

/-!
# Analytic remainder terms from actual finite-kernel coordinates

Choose actual uniformization representatives for a finite family of curve
points with exactly one zero point. All other representatives are off the
actual period lattice, so their translated Weierstrass coordinates are
analytic at the origin. Splitting off the unique zero point yields the
prescribed double/triple principal parts with genuine analytic remainders.
No continuity of the point-valued map is assumed.
-/

namespace BakerHeegnerStark

open scoped Topology

/-- Actual finite point-coordinate formulas with a unique zero summand have analytic remainder terms. -/
theorem exists_analytic_remainders_of_finite_coordinates [DecidableEq ℂ]
    (τ : UpperHalfPlane) {ι : Type*} [Fintype ι] (i₀ : ι)
    (q : ι → (periodCurve (standardPeriodPair τ)).toAffine.Point)
    (hq₀ : q i₀ = 0) (hqn : ∀ i, i ≠ i₀ → q i ≠ 0) (a b : ℂ)
    (Φ : (periodCurve (standardPeriodPair τ)).toAffine.Point →
      (periodCurve (standardPeriodPair τ)).toAffine.Point)
    (hX : ∀ P, periodCurveX τ (Φ P) = a *
      ((∑ i, periodCurveX τ (P - q i)) - ∑ i, periodCurveX τ (q i)))
    (hY : ∀ P, periodCurveY τ (Φ P) = b * ∑ i, periodCurveY τ (P - q i)) :
    ∃ A B : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧
      (∀ z, periodCurveX τ (Φ (standardPeriodPoint τ z)) =
        a * (standardPeriodPair τ).weierstrassP z + A z) ∧
      (∀ z, periodCurveY τ (Φ (standardPeriodPoint τ z)) =
        b * (standardPeriodPair τ).derivWeierstrassP z / 2 + B z) := by
  classical
  choose w hw using fun i => standardPeriodPoint_surjective τ (q i)
  have hw₀ : w i₀ ∈ periodModule (τ : ℂ) :=
    (standardPeriodPoint_eq_zero_iff τ _).mp ((hw i₀).trans hq₀)
  have hwn (i : ι) (hi : i ≠ i₀) : w i ∉ (standardPeriodPair τ).lattice := by
    intro h
    apply hqn i hi
    exact (hw i).symm.trans (standardPeriodPoint_of_mem τ h)
  have hsub (z : ℂ) (i : ι) :
      standardPeriodPoint τ z - q i = standardPeriodPoint τ (z - w i) := by
    calc
      _ = standardPeriodPoint τ z + standardPeriodPoint τ (-w i) := by
        rw [standardPeriodPoint_neg, hw]
        rfl
      _ = standardPeriodPoint τ (z + -w i) := (standardPeriodPoint_add τ z (-w i)).symm
      _ = _ := rfl
  let A : ℂ → ℂ := fun z => a *
    ((∑ i ∈ Finset.univ.erase i₀, (standardPeriodPair τ).weierstrassP (z - w i)) -
      ∑ i, (standardPeriodPair τ).weierstrassP (w i))
  let B : ℂ → ℂ := fun z => b *
    (∑ i ∈ Finset.univ.erase i₀, (standardPeriodPair τ).derivWeierstrassP (z - w i)) / 2
  have hnot (i : ι) (hi : i ∈ Finset.univ.erase i₀) :
      (0 : ℂ) - w i ∉ (standardPeriodPair τ).lattice := by
    intro h
    apply hwn i (Finset.mem_erase.mp hi).1
    simpa using (standardPeriodPair τ).lattice.neg_mem h
  have hA : AnalyticAt ℂ A 0 := by
    apply AnalyticAt.mul analyticAt_const
    apply AnalyticAt.sub
    · refine Finset.analyticAt_fun_sum _ fun i hi => ?_
      exact ((standardPeriodPair τ).analyticOnNhd_weierstrassP (0 - w i) (hnot i hi)).comp
        (f := fun z : ℂ => z - w i) (analyticAt_id.sub analyticAt_const)
    · exact analyticAt_const
  have hB : AnalyticAt ℂ B 0 := by
    apply AnalyticAt.div_const
    apply AnalyticAt.mul analyticAt_const
    refine Finset.analyticAt_fun_sum _ fun i hi => ?_
    have hd : AnalyticAt ℂ (standardPeriodPair τ).derivWeierstrassP (0 - w i) := by
      simpa only [PeriodPair.deriv_weierstrassP] using
        ((standardPeriodPair τ).analyticOnNhd_weierstrassP (0 - w i) (hnot i hi)).deriv
    exact hd.comp (f := fun z : ℂ => z - w i) (analyticAt_id.sub analyticAt_const)
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · intro z
    rw [hX]
    simp_rw [hsub, ← hw, periodCurveX_standardPeriodPoint]
    change a * ((∑ i, (standardPeriodPair τ).weierstrassP (z - w i)) -
      ∑ i, (standardPeriodPair τ).weierstrassP (w i)) = _
    rw [← Finset.add_sum_erase Finset.univ
      (fun i => (standardPeriodPair τ).weierstrassP (z - w i)) (Finset.mem_univ i₀),
      (standardPeriodPair τ).weierstrassP_sub_coe z ⟨w i₀, hw₀⟩]
    dsimp only [A]
    ring
  · intro z
    rw [hY]
    simp_rw [hsub, periodCurveY_standardPeriodPoint]
    rw [← Finset.sum_div]
    rw [← Finset.add_sum_erase Finset.univ
      (fun i => (standardPeriodPair τ).derivWeierstrassP (z - w i)) (Finset.mem_univ i₀),
      (standardPeriodPair τ).derivWeierstrassP_sub_coe z ⟨w i₀, hw₀⟩]
    dsimp only [B]
    ring


/-- A genuine point-group endomorphism with finite-kernel coordinates admits an analytic local lift. -/
theorem periodCurveEnd_exists_analytic_lift_of_finite_coordinates [DecidableEq ℂ]
    (τ : UpperHalfPlane) {ι : Type*} [Fintype ι] (i₀ : ι)
    (q : ι → (periodCurve (standardPeriodPair τ)).toAffine.Point)
    (hq₀ : q i₀ = 0) (hqn : ∀ i, i ≠ i₀ → q i ≠ 0) (a b : ℂ)
    (hb : b ≠ 0) (hab : a ^ 3 = b ^ 2)
    (Φ : (periodCurve (standardPeriodPair τ)).toAffine.Point →+
      (periodCurve (standardPeriodPair τ)).toAffine.Point)
    (hX : ∀ P, periodCurveX τ (Φ P) = a *
      ((∑ i, periodCurveX τ (P - q i)) - ∑ i, periodCurveX τ (q i)))
    (hY : ∀ P, periodCurveY τ (Φ P) = b * ∑ i, periodCurveY τ (P - q i)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ HasDerivAt g (a / b) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), Φ (standardPeriodPoint τ z) = standardPeriodPoint τ (g z) := by
  obtain ⟨A, B, hA, hB, hAX, hBY⟩ := exists_analytic_remainders_of_finite_coordinates
    τ i₀ q hq₀ hqn a b Φ hX hY
  have hΦ₀ : Φ (standardPeriodPoint τ (0 : ℂ)) = 0 := by
    rw [standardPeriodPoint_of_mem τ (zero_mem _), map_zero]
  exact exists_analytic_lift_of_pole_coordinates τ _ hΦ₀ a b hb hab A B hA hB
    (Filter.Eventually.of_forall hAX) (Filter.Eventually.of_forall hBY)

end BakerHeegnerStark
