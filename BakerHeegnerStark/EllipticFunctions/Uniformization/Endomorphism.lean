/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Uniformization.Torsion
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Analytic differentials determine actual period-curve endomorphisms

An additive endomorphism of the actual complex period-curve point group, with
an analytic local lift fixing zero, is multiplication of the uniformizing
argument by the derivative of that lift. The lift is locally linear: the
additivity defect lies in the actual period lattice, whose isolated origin
forces the defect to vanish near zero. Connectedness of the source `ℂ`
extends equality of the resulting point-valued homomorphisms globally.

In particular, a local lift with derivative `τ` characterizes the actual
quadratic-period endomorphism. No nonzero-derivative hypothesis is needed.
These results assume analytic regularity explicitly; they neither assert
regularity for arbitrary abstract point-group endomorphisms nor supply an
arithmetic field of definition.
-/

namespace BakerHeegnerStark

open Filter
open scoped Topology

private theorem periodCurveEnd_lift_eventually_add [DecidableEq ℂ]
    (τ : UpperHalfPlane)
    (Φ : (periodCurve (standardPeriodPair τ)).toAffine.Point →+
      (periodCurve (standardPeriodPair τ)).toAffine.Point)
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hΦ : ∀ᶠ z in 𝓝 0, Φ (standardPeriodPoint τ z) = standardPeriodPoint τ (g z)) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), g (p.1 + p.2) = g p.1 + g p.2 := by
  have hfst : Tendsto (fun p : ℂ × ℂ => p.1) (𝓝 (0, 0)) (𝓝 0) :=
    continuous_fst.tendsto _
  have hsnd : Tendsto (fun p : ℂ × ℂ => p.2) (𝓝 (0, 0)) (𝓝 0) :=
    continuous_snd.tendsto _
  have hadd : Tendsto (fun p : ℂ × ℂ => p.1 + p.2) (𝓝 (0, 0)) (𝓝 0) := by
    simpa only [add_zero] using hfst.add hsnd
  have hd : Tendsto (fun p : ℂ × ℂ => g (p.1 + p.2) - (g p.1 + g p.2))
      (𝓝 (0, 0)) (𝓝 0) := by
    simpa only [Function.comp_def, hg0, add_zero, sub_self] using
      (hg.continuousAt.tendsto.comp hadd).sub
        ((hg.continuousAt.tendsto.comp hfst).add (hg.continuousAt.tendsto.comp hsnd))
  filter_upwards [hadd.eventually hΦ, hfst.eventually hΦ, hsnd.eventually hΦ,
    hd.eventually ((standardPeriodPair τ).compl_lattice_sdiff_singleton_mem_nhds 0)]
    with p hp h₁ h₂ hd
  have hmem : g (p.1 + p.2) - (g p.1 + g p.2) ∈ periodModule (τ : ℂ) := by
    apply (standardPeriodPoint_eq_iff_sub_mem τ _ _).mp
    rw [← hp, standardPeriodPoint_add, map_add, h₁, h₂, standardPeriodPoint_add]
  have hzero : g (p.1 + p.2) - (g p.1 + g p.2) = 0 := by
    by_contra hne
    exact hd ⟨hmem, hne⟩
  exact sub_eq_zero.mp hzero

/-- An analytic local lift fixing zero of an actual curve point-group
endomorphism is the germ of multiplication by its derivative at zero. -/
theorem periodCurveEnd_analytic_lift_eventuallyEq [DecidableEq ℂ]
    (τ : UpperHalfPlane)
    (Φ : (periodCurve (standardPeriodPair τ)).toAffine.Point →+
      (periodCurve (standardPeriodPair τ)).toAffine.Point)
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hΦ : ∀ᶠ z in 𝓝 0, Φ (standardPeriodPoint τ z) = standardPeriodPoint τ (g z)) :
    g =ᶠ[𝓝 0] (fun z => deriv g 0 * z) := by
  have hadd := (periodCurveEnd_lift_eventually_add τ Φ hg hg0 hΦ).curry_nhds
  have hd : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z ∧ deriv g z = deriv g 0 := by
    filter_upwards [hadd, hg.eventually_analyticAt] with z hz hgz
    refine ⟨hgz.differentiableAt, ?_⟩
    have hleft : HasDerivAt (fun w => g (z + w)) (deriv g z) 0 := by
      simpa only [Function.comp_def, mul_one] using
        hgz.differentiableAt.hasDerivAt.comp_of_eq 0
          ((hasDerivAt_id' 0).const_add z) (add_zero z).symm
    have hright : HasDerivAt (fun w => g z + g w) (deriv g 0) 0 :=
      hg.differentiableAt.hasDerivAt.const_add (g z)
    apply hleft.unique
    apply hright.congr_of_eventuallyEq
    exact hz
  obtain ⟨r, hr, hdr⟩ := Metric.eventually_nhds_iff.mp hd
  have hlin (z : ℂ) : HasDerivAt (fun w : ℂ => deriv g 0 * w) (deriv g 0) z := by
    simpa only [mul_one] using (hasDerivAt_id' z).const_mul (deriv g 0)
  have heq : Set.EqOn g (fun z => deriv g 0 * z) (Metric.ball 0 r) :=
    Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℂ) r).isPreconnected
      (fun z hz => (hdr hz).1.differentiableWithinAt)
      (fun z _ => (hlin z).differentiableAt.differentiableWithinAt)
      (fun z hz => (hdr hz).2.trans (hlin z).deriv.symm)
      (Metric.mem_ball_self hr) (by simpa only [mul_zero] using hg0)
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hr) heq

private theorem complex_addMonoidHom_eq_of_eventuallyEq
    {G : Type*} [AddGroup G] (f h : ℂ →+ G) (hfh : f =ᶠ[𝓝 0] h) : f = h := by
  let K := f.eqLocus h
  have hopen : IsOpen (K : Set ℂ) := K.isOpen_of_mem_nhds hfh
  have hK : (K : Set ℂ) = Set.univ :=
    (show IsClopen (K : Set ℂ) from ⟨K.isClosed_of_isOpen hopen, hopen⟩).eq_univ
      ⟨0, K.zero_mem⟩
  ext z
  change z ∈ (K : Set ℂ)
  rw [hK]
  exact Set.mem_univ z

/-- The differential of an analytic local lift determines the endomorphism
on every actual Weierstrass point, not only near infinity. -/
theorem periodCurveEnd_apply_of_analytic_lift [DecidableEq ℂ]
    (τ : UpperHalfPlane)
    (Φ : (periodCurve (standardPeriodPair τ)).toAffine.Point →+
      (periodCurve (standardPeriodPair τ)).toAffine.Point)
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hΦ : ∀ᶠ z in 𝓝 0, Φ (standardPeriodPoint τ z) = standardPeriodPoint τ (g z))
    (z : ℂ) :
    Φ (standardPeriodPoint τ z) = standardPeriodPoint τ (deriv g 0 * z) := by
  let p : ℂ →+ (periodCurve (standardPeriodPair τ)).toAffine.Point :=
    (standardPeriodTorusPointHom τ).comp (periodModule (τ : ℂ)).mkQ.toAddMonoidHom
  let a : ℂ →+ ℂ :=
    { toFun := fun w => deriv g 0 * w
      map_zero' := mul_zero _
      map_add' := fun w v => mul_add _ w v }
  have heq : Φ.comp p = p.comp a := by
    apply complex_addMonoidHom_eq_of_eventuallyEq
    filter_upwards [hΦ, periodCurveEnd_analytic_lift_eventuallyEq τ Φ hg hg0 hΦ]
      with w hw hgw
    exact hw.trans (congrArg (standardPeriodPoint τ) hgw)
  exact DFunLike.congr_fun heq z

/-- An actual point-group endomorphism with an analytic local lift of
quadratic-period differential is the real period-curve CM endomorphism. -/
theorem periodCurveEnd_eq_CM_of_analytic_lift [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℤ) (hquad : (τ : ℂ) ^ 2 = -(m : ℂ))
    (Φ : (periodCurve (standardPeriodPair τ)).toAffine.Point →+
      (periodCurve (standardPeriodPair τ)).toAffine.Point)
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hΦ : ∀ᶠ z in 𝓝 0, Φ (standardPeriodPoint τ z) = standardPeriodPoint τ (g z))
    (hdg : HasDerivAt g (τ : ℂ) 0) :
    Φ = periodCurveCMEnd τ m hquad := by
  ext P
  obtain ⟨z, rfl⟩ := standardPeriodPoint_surjective τ P
  rw [periodCurveEnd_apply_of_analytic_lift τ Φ hg hg0 hΦ,
    hdg.deriv, periodCurveCMEnd_standardPeriodPoint]

end BakerHeegnerStark
