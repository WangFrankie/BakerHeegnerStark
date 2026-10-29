/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.Analysis.DifferentialEquation
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Differential
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.Ring

/-!
# Fibres of the actual Weierstrass coordinates

The second-order differential equation and uniqueness of analytic solutions
show that equal values of `wp` and `wp'` give equal translated germs.
Analytic continuation off the two translated lattices then identifies the
poles and recovers the period difference.

All coordinate comparisons explicitly exclude lattice poles: the totalized
values of the two functions at a pole are not affine curve coordinates.
These results prove injectivity modulo periods, not the addition formula.
-/

open Filter
open scoped Topology

namespace PeriodPair

/-- Equal translated Weierstrass germs determine the same period class. -/
theorem sub_mem_lattice_of_weierstrassP_add_eventuallyEq (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h : (fun t => L.weierstrassP (z + t)) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => L.weierstrassP (w + t))) : z - w ∈ L.lattice := by
  classical
  let U : Set ℂ := (((fun t : ℂ => z + t) ⁻¹' (L.lattice : Set ℂ)) ∪
    ((fun t : ℂ => w + t) ⁻¹' (L.lattice : Set ℂ)))ᶜ
  have hcount : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hzc : ((fun t : ℂ => z + t) ⁻¹' (L.lattice : Set ℂ)).Countable :=
    hcount.preimage (by intro a b hab; exact add_left_cancel hab)
  have hwc : ((fun t : ℂ => w + t) ⁻¹' (L.lattice : Set ℂ)).Countable :=
    hcount.preimage (by intro a b hab; exact add_left_cancel hab)
  have hconn : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (hzc.union hwc)).isPreconnected
  have hzero : (0 : ℂ) ∈ U := by simpa [U] using And.intro hz hw
  have hAz : AnalyticOnNhd ℂ (fun t => L.weierstrassP (z + t)) U := by
    intro t ht
    have htz : z + t ∉ L.lattice := fun hh => ht (Or.inl hh)
    exact (L.analyticOnNhd_weierstrassP _ htz).comp (analyticAt_const.add analyticAt_id)
  have hAw : AnalyticOnNhd ℂ (fun t => L.weierstrassP (w + t)) U := by
    intro t ht
    have htw : w + t ∉ L.lattice := fun hh => ht (Or.inr hh)
    exact (L.analyticOnNhd_weierstrassP _ htw).comp (analyticAt_const.add analyticAt_id)
  have heq : Set.EqOn (fun t => L.weierstrassP (z + t))
      (fun t => L.weierstrassP (w + t)) U :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hAz hAw hconn hzero h
  by_contra hzw
  have hwz : w - z ∉ L.lattice := by
    intro hm
    exact hzw (by simpa only [neg_sub] using L.lattice.neg_mem hm)
  have ha : AnalyticAt ℂ (fun t => L.weierstrassP (w - z + t)) 0 :=
    (L.analyticOnNhd_weierstrassP (w - z + 0)
      (by simpa using hwz)).comp (analyticAt_const.add analyticAt_id)
  have htend : Tendsto (fun t : ℂ => w - z + t) (𝓝 0) (𝓝 (w - z)) := by
    have ht := (continuousAt_const.add continuousAt_id :
      ContinuousAt (fun t : ℂ => w - z + t) 0).tendsto
    change Tendsto (fun t : ℂ => w - z + t) (𝓝 0) (𝓝 (w - z + 0)) at ht
    simpa only [add_zero] using ht
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), w - z + t ∉ L.lattice :=
    htend.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hwz)
  have hgerm : L.weierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] (fun t => L.weierstrassP (w - z + t)) := by
    filter_upwards [
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear,
      (self_mem_nhdsWithin : ({0} : Set ℂ)ᶜ ∈ 𝓝[≠] (0 : ℂ))] with t htL htW ht0
    have htn : t ∉ L.lattice := fun hm => htL ⟨hm, by simpa using ht0⟩
    have h1 : z + (t - z) = t := by ring
    have h2 : w + (t - z) = w - z + t := by ring
    have htU : t - z ∈ U := by
      change ¬ (z + (t - z) ∈ L.lattice ∨ w + (t - z) ∈ L.lattice)
      rw [h1, h2]
      exact not_or.mpr ⟨htn, htW⟩
    simpa only [h1, h2] using heq htU
  have horder := ha.meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr hgerm, L.order_weierstrassP 0 L.lattice.zero_mem] at horder
  exact (by decide : ¬ (0 : WithTop ℤ) ≤ -2) horder

/-- The value and first derivative determine the translated Weierstrass germ. -/
theorem weierstrassP_add_eventuallyEq_of_value_deriv_eq (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hx : L.weierstrassP z = L.weierstrassP w)
    (hy : L.derivWeierstrassP z = L.derivWeierstrassP w) :
    (fun t => L.weierstrassP (z + t)) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => L.weierstrassP (w + t)) := by
  let f : ℂ → ℂ := fun t => L.weierstrassP (z + t) - L.weierstrassP (w + t)
  let g : ℂ → ℂ := fun t => L.derivWeierstrassP (z + t) -
    L.derivWeierstrassP (w + t)
  let A : ℂ → ℂ := fun t => 6 * (L.weierstrassP (z + t) + L.weierstrassP (w + t))
  have hAz : AnalyticAt ℂ (fun t => L.weierstrassP (z + t)) 0 :=
    (L.analyticOnNhd_weierstrassP (z + 0) (by simpa using hz)).comp
      (analyticAt_const.add analyticAt_id)
  have hAw : AnalyticAt ℂ (fun t => L.weierstrassP (w + t)) 0 :=
    (L.analyticOnNhd_weierstrassP (w + 0) (by simpa using hw)).comp
      (analyticAt_const.add analyticAt_id)
  have hf : AnalyticAt ℂ f 0 := hAz.sub hAw
  have hA : AnalyticAt ℂ A 0 := analyticAt_const.mul (hAz.add hAw)
  have hf0 : f 0 = 0 := by simp [f, hx]
  have hdf : deriv f =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [hAz.eventually_analyticAt, hAw.eventually_analyticAt] with t htz htw
    change deriv ((fun u => L.weierstrassP (z + u)) -
      (fun u => L.weierstrassP (w + u))) t = _
    rw [deriv_sub htz.differentiableAt htw.differentiableAt]
    simp only [deriv_comp_const_add, L.deriv_weierstrassP, g]
  have hdf0 : deriv f 0 = 0 := by
    rw [hdf.eq_of_nhds]
    simp [g, hy]
  have hnear (a : ℂ) (ha : a ∉ L.lattice) :
      ∀ᶠ t in 𝓝 (0 : ℂ), a + t ∉ L.lattice := by
    have ht := (continuousAt_const.add continuousAt_id :
      ContinuousAt (fun t : ℂ => a + t) 0).tendsto
    change Tendsto (fun t : ℂ => a + t) (𝓝 0) (𝓝 (a + 0)) at ht
    have ht' : Tendsto (fun t : ℂ => a + t) (𝓝 0) (𝓝 a) := by
      simpa only [add_zero] using ht
    exact ht'.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds ha)
  have hdg : deriv g =ᶠ[𝓝 (0 : ℂ)] (fun t => A t * f t) := by
    filter_upwards [hnear z hz, hnear w hw] with t htz htw
    have hDz : AnalyticAt ℂ (fun u => L.derivWeierstrassP (z + u)) t :=
      (L.analyticOnNhd_derivWeierstrassP (z + t) htz).comp
        (analyticAt_const.add analyticAt_id)
    have hDw : AnalyticAt ℂ (fun u => L.derivWeierstrassP (w + u)) t :=
      (L.analyticOnNhd_derivWeierstrassP (w + t) htw).comp
        (analyticAt_const.add analyticAt_id)
    change deriv ((fun u => L.derivWeierstrassP (z + u)) -
      (fun u => L.derivWeierstrassP (w + u))) t = _
    rw [deriv_sub hDz.differentiableAt hDw.differentiableAt,
      deriv_comp_const_add, deriv_comp_const_add,
      L.deriv_derivWeierstrassP _ htz, L.deriv_derivWeierstrassP _ htw]
    dsimp [A, f]
    ring
  have hzero := BakerHeegnerStark.analytic_eventuallyEq_zero_of_deriv_deriv_eq_mul
    f A hf hA hf0 hdf0 (hdf.deriv.trans hdg)
  filter_upwards [hzero] with t ht
  exact sub_eq_zero.mp ht

/-- Away from poles, the pair `(℘, ℘')` separates points modulo the period lattice. -/
theorem sub_mem_lattice_of_weierstrassP_deriv_eq (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hx : L.weierstrassP z = L.weierstrassP w)
    (hy : L.derivWeierstrassP z = L.derivWeierstrassP w) : z - w ∈ L.lattice :=
  L.sub_mem_lattice_of_weierstrassP_add_eventuallyEq z w hz hw
    (L.weierstrassP_add_eventuallyEq_of_value_deriv_eq z w hz hw hx hy)

/-- The complete fibre of the pair `(℘, ℘')`, with poles excluded. -/
theorem weierstrassP_deriv_eq_iff_sub_mem_lattice (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    (L.weierstrassP z = L.weierstrassP w ∧
      L.derivWeierstrassP z = L.derivWeierstrassP w) ↔ z - w ∈ L.lattice := by
  constructor
  · intro h
    exact L.sub_mem_lattice_of_weierstrassP_deriv_eq z w hz hw h.1 h.2
  · intro h
    have hzw : w + (z - w) = z := by ring
    exact ⟨by simpa only [hzw] using L.weierstrassP_add_coe w ⟨z - w, h⟩,
      by simpa only [hzw] using L.derivWeierstrassP_add_coe w ⟨z - w, h⟩⟩

/-- Off the lattice, `wp` identifies exactly the two opposite period classes. -/
theorem weierstrassP_eq_iff_sub_mem_or_add_mem_lattice (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    L.weierstrassP z = L.weierstrassP w ↔
      z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  have hwn : -w ∉ L.lattice := by simpa only [neg_mem_iff] using hw
  constructor
  · intro hx
    have hs : L.derivWeierstrassP z ^ 2 = L.derivWeierstrassP w ^ 2 := by
      rw [L.derivWeierstrassP_sq z hz, L.derivWeierstrassP_sq w hw, hx]
    have hp : (L.derivWeierstrassP z - L.derivWeierstrassP w) *
        (L.derivWeierstrassP z + L.derivWeierstrassP w) = 0 := by
      linear_combination hs
    rcases mul_eq_zero.mp hp with hm | hp
    · exact Or.inl (L.sub_mem_lattice_of_weierstrassP_deriv_eq z w hz hw hx
        (sub_eq_zero.mp hm))
    · have hx' : L.weierstrassP z = L.weierstrassP (-w) := by
        rw [L.weierstrassP_neg]
        exact hx
      have hy' : L.derivWeierstrassP z = L.derivWeierstrassP (-w) := by
        rw [L.derivWeierstrassP_neg]
        exact add_eq_zero_iff_eq_neg.mp hp
      exact Or.inr (by simpa only [sub_neg_eq_add] using
        L.sub_mem_lattice_of_weierstrassP_deriv_eq z (-w) hz hwn hx' hy')
  · rintro (h | h)
    · exact ((L.weierstrassP_deriv_eq_iff_sub_mem_lattice z w hz hw).mpr h).1
    · have h' : z - -w ∈ L.lattice := by simpa only [sub_neg_eq_add] using h
      simpa only [L.weierstrassP_neg] using
        ((L.weierstrassP_deriv_eq_iff_sub_mem_lattice z (-w) hz hwn).mpr h').1

/-- The actual critical points of `wp` off its poles are precisely the nonzero half-periods. -/
theorem derivWeierstrassP_eq_zero_iff_two_mul_mem_lattice (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z = 0 ↔ 2 * z ∈ L.lattice := by
  have hzn : -z ∉ L.lattice := by simpa only [neg_mem_iff] using hz
  have hperiod : z - -z ∈ L.lattice ↔ 2 * z ∈ L.lattice := by
    rw [sub_neg_eq_add, two_mul]
  constructor
  · intro hy
    apply hperiod.mp
    apply L.sub_mem_lattice_of_weierstrassP_deriv_eq z (-z) hz hzn
      (L.weierstrassP_neg z).symm
    simp only [L.derivWeierstrassP_neg, hy, neg_zero]
  · intro h
    have hy := ((L.weierstrassP_deriv_eq_iff_sub_mem_lattice z (-z) hz hzn).mpr
      (hperiod.mpr h)).2
    rw [L.derivWeierstrassP_neg] at hy
    linear_combination (1 / 2 : ℂ) * hy

end PeriodPair
