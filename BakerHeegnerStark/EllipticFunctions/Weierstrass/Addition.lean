/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Weierstrass.TranslationAnalytic
import BakerHeegnerStark.EllipticFunctions.Weierstrass.TranslationDifferential
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Fibres
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The actual Weierstrass addition formula

The rational chord coordinates satisfy the actual Weierstrass differential
equation. Their regular germ at the origin has the prescribed value and
first derivative, so analytic uniqueness identifies it with translation.
Continuation on the connected complement of the relevant period cosets
proves both coordinate formulas at every pair of unequal x-coordinates.

Equal x-coordinates, including tangent and inverse cases, are not treated
by substituting into a totalized quotient.
-/

open Filter
open scoped Topology

namespace PeriodPair

private def weierstrassAdditionDomain (L : PeriodPair) (z : ℂ) : Set ℂ :=
  (((L.lattice : Set ℂ) \ {0}) ∪
    ((fun u : ℂ => z + u) ⁻¹' (L.lattice : Set ℂ)) ∪
    ((fun u : ℂ => -z + u) ⁻¹' (L.lattice : Set ℂ)))ᶜ

private theorem isOpen_weierstrassAdditionDomain (L : PeriodPair) (z : ℂ) :
    IsOpen (weierstrassAdditionDomain L z) := by
  have h₀ : IsClosed ((L.lattice : Set ℂ) \ {0}) :=
    L.isClosed_of_subset_lattice Set.sdiff_subset
  have h₁ : IsClosed ((fun u : ℂ => z + u) ⁻¹' (L.lattice : Set ℂ)) :=
    L.isClosed_lattice.preimage (by fun_prop)
  have h₂ : IsClosed ((fun u : ℂ => -z + u) ⁻¹' (L.lattice : Set ℂ)) :=
    L.isClosed_lattice.preimage (by fun_prop)
  exact ((h₀.union h₁).union h₂).isOpen_compl

private theorem isPreconnected_weierstrassAdditionDomain (L : PeriodPair) (z : ℂ) :
    IsPreconnected (weierstrassAdditionDomain L z) := by
  have hc : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hc₁ : ((fun u : ℂ => z + u) ⁻¹' (L.lattice : Set ℂ)).Countable :=
    hc.preimage (by intro a b h; exact add_left_cancel h)
  have hc₂ : ((fun u : ℂ => -z + u) ⁻¹' (L.lattice : Set ℂ)).Countable :=
    hc.preimage (by intro a b h; exact add_left_cancel h)
  exact (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    (((hc.mono Set.sdiff_subset).union hc₁).union hc₂)).isPreconnected

private theorem zero_mem_weierstrassAdditionDomain (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) : (0 : ℂ) ∈ weierstrassAdditionDomain L z := by
  simp [weierstrassAdditionDomain, hz]

private theorem weierstrassAdditionDomain_spec (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) {u : ℂ} (hu : u ∈ weierstrassAdditionDomain L z) (hu₀ : u ≠ 0) :
    u ∉ L.lattice ∧ z + u ∉ L.lattice ∧ L.weierstrassP u ≠ L.weierstrassP z := by
  have hs : u ∉ (L.lattice : Set ℂ) \ {0} ∧
      z + u ∉ L.lattice ∧ -z + u ∉ L.lattice := by
    simpa only [weierstrassAdditionDomain, Set.mem_compl_iff, Set.mem_union,
      Set.mem_preimage, SetLike.mem_coe, not_or, and_assoc] using hu
  have huL : u ∉ L.lattice := fun hm => hs.1 ⟨hm, by simpa using hu₀⟩
  refine ⟨huL, hs.2.1, fun hx => ?_⟩
  rcases (L.weierstrassP_eq_iff_sub_mem_or_add_mem_lattice u z huL hz).mp hx with h | h
  · apply hs.2.2
    convert h using 1; ring
  · apply hs.2.1
    convert h using 1; ring

private theorem weierstrassTranslateX_eqOn_additionDomain (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) :
    Set.EqOn (L.weierstrassTranslateX z) (fun u => L.weierstrassP (z + u))
      (weierstrassAdditionDomain L z) := by
  let R := L.weierstrassTranslateX z
  let V := L.weierstrassTranslateY z
  let T : ℂ → ℂ := fun u => L.weierstrassP (z + u)
  let U := weierstrassAdditionDomain L z
  have hzero : (0 : ℂ) ∈ U := zero_mem_weierstrassAdditionDomain L z hz
  have hnear : U ∈ 𝓝 (0 : ℂ) := (isOpen_weierstrassAdditionDomain L z).mem_nhds hzero
  have hR : AnalyticOnNhd ℂ R U := by
    intro u hu
    by_cases hu₀ : u = 0
    · subst u
      exact L.analyticAt_weierstrassTranslateX_zero z
    · have hs := weierstrassAdditionDomain_spec L z hz hu hu₀
      exact L.analyticAt_weierstrassTranslateX_of_not_mem z hs.1 hs.2.2
  have hT : AnalyticOnNhd ℂ T U := by
    intro u hu
    have hzu : z + u ∉ L.lattice := fun hm => hu (Or.inl (Or.inr hm))
    exact (L.analyticOnNhd_weierstrassP _ hzu).comp
      (analyticAt_const.add analyticAt_id)
  have hR₀ : AnalyticAt ℂ R 0 := hR 0 hzero
  have hT₀ : AnalyticAt ℂ T 0 := hT 0 hzero
  have hdR : deriv R =ᶠ[𝓝 (0 : ℂ)] V := by
    filter_upwards [hnear] with u hu
    by_cases hu₀ : u = 0
    · subst u
      exact (L.hasDerivAt_weierstrassTranslateX_zero z).deriv.trans
        (L.weierstrassTranslateY_of_mem z L.lattice.zero_mem).symm
    · have hs := weierstrassAdditionDomain_spec L z hz hu hu₀
      exact (L.hasDerivAt_weierstrassTranslateX_of_not_mem z hz hs.1 hs.2.2).deriv
  have hV₀ : AnalyticAt ℂ V 0 := hR₀.deriv.congr hdR
  have hdVpunct : deriv V =ᶠ[𝓝[≠] (0 : ℂ)] (fun u => 6 * R u ^ 2 - L.g₂ / 2) := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear,
      (self_mem_nhdsWithin : ({0} : Set ℂ)ᶜ ∈ 𝓝[≠] (0 : ℂ))] with u hu hu₀
    have hs := weierstrassAdditionDomain_spec L z hz hu (by simpa using hu₀)
    exact (L.hasDerivAt_weierstrassTranslateY_of_not_mem z hz hs.1 hs.2.2).deriv
  have hRhs : AnalyticAt ℂ (fun u => 6 * R u ^ 2 - L.g₂ / 2) 0 := by fun_prop
  have hdV : deriv V =ᶠ[𝓝 (0 : ℂ)] (fun u => 6 * R u ^ 2 - L.g₂ / 2) :=
    (hV₀.deriv.frequently_eq_iff_eventually_eq hRhs).mp hdVpunct.frequently
  have hddR : deriv (deriv R) =ᶠ[𝓝 (0 : ℂ)] (fun u => 6 * R u ^ 2 - L.g₂ / 2) :=
    hdR.deriv.trans hdV
  have hdT : deriv T = fun u => L.derivWeierstrassP (z + u) := by
    funext u
    simp only [T, deriv_comp_const_add, L.deriv_weierstrassP]
  have hddT : deriv (deriv T) =ᶠ[𝓝 (0 : ℂ)] (fun u => 6 * T u ^ 2 - L.g₂ / 2) := by
    filter_upwards [hnear] with u hu
    have hzu : z + u ∉ L.lattice := fun hm => hu (Or.inl (Or.inr hm))
    rw [hdT, deriv_comp_const_add, L.deriv_derivWeierstrassP _ hzu]
  let f : ℂ → ℂ := fun u => R u - T u
  let A : ℂ → ℂ := fun u => 6 * (R u + T u)
  have hf : AnalyticAt ℂ f 0 := hR₀.sub hT₀
  have hA : AnalyticAt ℂ A 0 := analyticAt_const.mul (hR₀.add hT₀)
  have hf₀ : f 0 = 0 := by
    simp only [f, R, T, L.weierstrassTranslateX_of_mem z L.lattice.zero_mem,
      add_zero, sub_self]
  have hdf : deriv f =ᶠ[𝓝 (0 : ℂ)] (fun u => deriv R u - deriv T u) := by
    filter_upwards [hR₀.eventually_analyticAt, hT₀.eventually_analyticAt] with u hr ht
    change deriv (R - T) u = _
    exact deriv_sub hr.differentiableAt ht.differentiableAt
  have hdf₀ : deriv f 0 = 0 := by
    rw [hdf.eq_of_nhds]
    simp only [R, (L.hasDerivAt_weierstrassTranslateX_zero z).deriv,
      hdT, add_zero, sub_self]
  have hde : ∀ᶠ u in 𝓝 (0 : ℂ), deriv (deriv f) u = A u * f u := by
    filter_upwards [hdf.deriv, hR₀.deriv.eventually_analyticAt,
      hT₀.deriv.eventually_analyticAt, hddR, hddT] with u hu hr ht hrr htt
    rw [hu]
    change deriv (deriv R - deriv T) u = _
    rw [deriv_sub hr.differentiableAt ht.differentiableAt, hrr, htt]
    dsimp only [A, f]
    ring
  have hfg₀ := BakerHeegnerStark.analytic_eventuallyEq_zero_of_deriv_deriv_eq_mul
    f A hf hA hf₀ hdf₀ hde
  have hfg : R =ᶠ[𝓝 (0 : ℂ)] T := by
    filter_upwards [hfg₀] with u hu
    exact sub_eq_zero.mp hu
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hR hT
    (isPreconnected_weierstrassAdditionDomain L z) hzero hfg

private theorem mem_weierstrassAdditionDomain_of_ne (L : PeriodPair) (z u : ℂ)
    (hz : z ∉ L.lattice) (hu : u ∉ L.lattice)
    (hxu : L.weierstrassP u ≠ L.weierstrassP z) :
    u ∈ weierstrassAdditionDomain L z := by
  have hnot : ¬(u - z ∈ L.lattice ∨ u + z ∈ L.lattice) :=
    fun h => hxu ((L.weierstrassP_eq_iff_sub_mem_or_add_mem_lattice u z hu hz).mpr h)
  change ¬((u ∈ (L.lattice : Set ℂ) \ {0} ∨ z + u ∈ L.lattice) ∨ -z + u ∈ L.lattice)
  rintro ((h | h) | h)
  · exact hu h.1
  · apply hnot
    right
    convert h using 1; ring
  · apply hnot
    left
    convert h using 1; ring

/-- The actual Weierstrass addition formula at unequal x-coordinates. -/
theorem weierstrassP_add (L : PeriodPair) (z u : ℂ)
    (hz : z ∉ L.lattice) (hu : u ∉ L.lattice)
    (hxu : L.weierstrassP u ≠ L.weierstrassP z) :
    L.weierstrassP (z + u) =
      ((L.derivWeierstrassP u - L.derivWeierstrassP z) /
        (2 * (L.weierstrassP u - L.weierstrassP z))) ^ 2 -
        L.weierstrassP u - L.weierstrassP z := by
  have h := weierstrassTranslateX_eqOn_additionDomain L z hz
    (mem_weierstrassAdditionDomain_of_ne L z u hz hu hxu)
  simpa only [weierstrassTranslateX, ite_eq_right hu] using h.symm

/-- The matching actual derivative coordinate in the Weierstrass addition formula. -/
theorem derivWeierstrassP_add (L : PeriodPair) (z u : ℂ)
    (hz : z ∉ L.lattice) (hu : u ∉ L.lattice)
    (hxu : L.weierstrassP u ≠ L.weierstrassP z) :
    L.derivWeierstrassP (z + u) = -L.derivWeierstrassP u +
      (L.derivWeierstrassP u - L.derivWeierstrassP z) /
        (L.weierstrassP u - L.weierstrassP z) *
          (L.weierstrassP u - L.weierstrassP (z + u)) := by
  have hdom := mem_weierstrassAdditionDomain_of_ne L z u hz hu hxu
  have hnear : ∀ᶠ v in 𝓝 u, v ∈ weierstrassAdditionDomain L z :=
    (isOpen_weierstrassAdditionDomain L z).mem_nhds hdom
  have hgerm : L.weierstrassTranslateX z =ᶠ[𝓝 u]
      (fun v => L.weierstrassP (z + v)) :=
    hnear.mono fun v hv => weierstrassTranslateX_eqOn_additionDomain L z hz hv
  have hd := hgerm.deriv.eq_of_nhds
  rw [(L.hasDerivAt_weierstrassTranslateX_of_not_mem z hz hu hxu).deriv,
    deriv_comp_const_add, L.deriv_weierstrassP] at hd
  have hx := weierstrassTranslateX_eqOn_additionDomain L z hz hdom
  rw [weierstrassTranslateY, ite_eq_right hu, hx] at hd
  exact hd.symm

end PeriodPair
