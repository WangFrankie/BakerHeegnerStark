/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Weierstrass.Isogeny
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Differential

/-!
# Invariant traces for finite-index period lattices

With zero chosen as the representative of the trivial coset, the finite-coset
formula becomes an identity between regular parts at zero. Comparing its second
and fourth derivatives gives the traces of `g₂` and `g₃`. Every other
representative lies outside the coarse lattice, so all derivatives of translated
Weierstrass functions are taken at genuine non-poles.
-/

open Filter
open scoped Topology

namespace PeriodPair

private theorem representative_not_mem_lattice (L : PeriodPair) (T : Finset ℂ)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ L.lattice → s = t)
    (h0 : 0 ∈ T) {t : ℂ} (ht : t ∈ T.erase 0) : t ∉ L.lattice := by
  intro h
  exact (Finset.mem_erase.mp ht).1
    (hTi t (Finset.mem_erase.mp ht).2 0 h0 (by simpa using h))

private theorem regular_part_finite_coset_sum (L M : PeriodPair) (T : Finset ℂ)
    (hLM : (L.lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ L.lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ L.lattice)
    (h0 : 0 ∈ T) :
    (fun z => M.weierstrassPExcept 0 z - L.weierstrassPExcept 0 z) =
      (fun z => ∑ t ∈ T.erase 0, (L.weierstrassP (z - t) - L.weierstrassP t)) := by
  classical
  funext z
  have heq := weierstrassP_finite_coset_sum L M T hLM hTM hTi hcover z
  rw [← Finset.add_sum_erase T (fun t => L.weierstrassP (z - t)) h0,
    ← Finset.add_sum_erase T L.weierstrassP h0] at heq
  simp only [sub_zero, L.weierstrassP_zero, zero_add] at heq
  have hL := L.weierstrassPExcept_def (0 : L.lattice) z
  have hM := M.weierstrassPExcept_def (0 : M.lattice) z
  simp only [ZeroMemClass.coe_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    div_zero, zero_sub] at hL hM
  rw [hL, hM, Finset.sum_sub_distrib]
  linear_combination heq

private theorem iteratedDeriv_regular_part_finite_coset_sum
    (L M : PeriodPair) (T : Finset ℂ)
    (hLM : (L.lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ L.lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ L.lattice)
    (h0 : 0 ∈ T) (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (M.weierstrassPExcept 0) 0 -
      iteratedDeriv n (L.weierstrassPExcept 0) 0 =
        ∑ t ∈ T.erase 0, iteratedDeriv n L.weierstrassP (-t) := by
  classical
  have ha (t : ℂ) (ht : t ∈ T.erase 0) :
      AnalyticAt ℂ (fun z : ℂ => L.weierstrassP (z - t)) 0 := by
    have ht' := representative_not_mem_lattice L T hTi h0 ht
    have hneg : -t ∉ L.lattice := by simpa using ht'
    simpa only [Function.comp_def] using
      (L.analyticOnNhd_weierstrassP (0 - t) (by simpa using hneg)).comp
        (f := fun z : ℂ => z - t) (analyticAt_id.sub analyticAt_const)
  have heq := congrArg (fun f : ℂ → ℂ => iteratedDeriv n f 0)
    (regular_part_finite_coset_sum L M T hLM hTM hTi hcover h0)
  rw [iteratedDeriv_fun_sub (M.analyticAt_weierstrassPExcept 0).contDiffAt
    (L.analyticAt_weierstrassPExcept 0).contDiffAt,
    iteratedDeriv_fun_sum (f := fun t z => L.weierstrassP (z - t) - L.weierstrassP t)
      (fun t ht => ((ha t ht).fun_sub analyticAt_const).contDiffAt)] at heq
  refine heq.trans (Finset.sum_congr rfl fun t ht => ?_)
  rw [iteratedDeriv_fun_sub (ha t ht).contDiffAt contDiffAt_const,
    iteratedDeriv_comp_sub_const, iteratedDeriv_const]
  simp [hn.ne']

private theorem iteratedDeriv_two_weierstrassP (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) :
    iteratedDeriv 2 L.weierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, L.deriv_weierstrassP] using
    L.deriv_derivWeierstrassP z hz

private theorem iteratedDeriv_three_weierstrassP (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) :
    iteratedDeriv 3 L.weierstrassP z =
      12 * L.weierstrassP z * L.derivWeierstrassP z := by
  have heq : iteratedDeriv 2 L.weierstrassP =ᶠ[𝓝 z]
      (fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact iteratedDeriv_two_weierstrassP L w hw
  have hwp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa only [L.deriv_weierstrassP] using
      (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2)
      (12 * L.weierstrassP z * L.derivWeierstrassP z) z := by
    convert ((hwp.pow 2).const_mul 6).sub_const (L.g₂ / 2) using 1; ring
  rw [show 3 = 2 + 1 by rfl, iteratedDeriv_succ]
  exact (hd.congr_of_eventuallyEq heq).deriv

private theorem iteratedDeriv_four_weierstrassP (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) :
    iteratedDeriv 4 L.weierstrassP z =
      120 * L.weierstrassP z ^ 3 - 18 * L.g₂ * L.weierstrassP z - 12 * L.g₃ := by
  have heq : iteratedDeriv 3 L.weierstrassP =ᶠ[𝓝 z]
      (fun w => 12 * L.weierstrassP w * L.derivWeierstrassP w) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact iteratedDeriv_three_weierstrassP L w hw
  have hwp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa only [L.deriv_weierstrassP] using
      (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hdwp : HasDerivAt L.derivWeierstrassP
      (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z := by
    simpa only [L.deriv_derivWeierstrassP z hz] using
      (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  have hd := (hwp.const_mul 12).mul hdwp
  rw [show 4 = 3 + 1 by rfl, iteratedDeriv_succ,
    (hd.congr_of_eventuallyEq heq).deriv]
  linear_combination 12 * L.derivWeierstrassP_sq z hz

private theorem iteratedDeriv_two_regular_part (L : PeriodPair) :
    iteratedDeriv 2 (L.weierstrassPExcept 0) 0 = L.g₂ / 10 := by
  rw [L.iteratedDeriv_weierstrassPExcept_self]
  norm_num [g₂]
  ring

private theorem iteratedDeriv_four_regular_part (L : PeriodPair) :
    iteratedDeriv 4 (L.weierstrassPExcept 0) 0 = 6 * L.g₃ / 7 := by
  rw [L.iteratedDeriv_weierstrassPExcept_self]
  norm_num [g₃]
  ring

/-- The `g₂` trace formula for a finite lattice inclusion with normalized representatives. -/
theorem g₂_finite_coset_sum (L M : PeriodPair) (T : Finset ℂ)
    (hLM : (L.lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ L.lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ L.lattice)
    (h0 : 0 ∈ T) :
    M.g₂ = L.g₂ +
      ∑ t ∈ T.erase 0, (60 * L.weierstrassP t ^ 2 - 5 * L.g₂) := by
  classical
  have h := iteratedDeriv_regular_part_finite_coset_sum
    L M T hLM hTM hTi hcover h0 2 (by decide)
  simp only [iteratedDeriv_two_regular_part] at h
  have hterms : ∀ t ∈ T.erase 0,
      iteratedDeriv 2 L.weierstrassP (-t) =
        6 * L.weierstrassP t ^ 2 - L.g₂ / 2 := by
    intro t ht
    have ht' := representative_not_mem_lattice L T hTi h0 ht
    simpa only [L.weierstrassP_neg] using
      iteratedDeriv_two_weierstrassP L (-t) (by simpa using ht')
  rw [Finset.sum_congr rfl hterms] at h
  have hscale :
      (∑ t ∈ T.erase 0, (60 * L.weierstrassP t ^ 2 - 5 * L.g₂)) =
        10 * ∑ t ∈ T.erase 0, (6 * L.weierstrassP t ^ 2 - L.g₂ / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hscale]
  linear_combination 10 * h

/-- The `g₃` trace formula for a finite lattice inclusion with normalized representatives. -/
theorem g₃_finite_coset_sum (L M : PeriodPair) (T : Finset ℂ)
    (hLM : (L.lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ L.lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ L.lattice)
    (h0 : 0 ∈ T) :
    M.g₃ = L.g₃ +
      ∑ t ∈ T.erase 0, (140 * L.weierstrassP t ^ 3 -
        21 * L.g₂ * L.weierstrassP t - 14 * L.g₃) := by
  classical
  have h := iteratedDeriv_regular_part_finite_coset_sum
    L M T hLM hTM hTi hcover h0 4 (by decide)
  simp only [iteratedDeriv_four_regular_part] at h
  have hterms : ∀ t ∈ T.erase 0,
      iteratedDeriv 4 L.weierstrassP (-t) =
        120 * L.weierstrassP t ^ 3 -
          18 * L.g₂ * L.weierstrassP t - 12 * L.g₃ := by
    intro t ht
    have ht' := representative_not_mem_lattice L T hTi h0 ht
    simpa only [L.weierstrassP_neg] using
      iteratedDeriv_four_weierstrassP L (-t) (by simpa using ht')
  rw [Finset.sum_congr rfl hterms] at h
  have hscale :
      (∑ t ∈ T.erase 0, (140 * L.weierstrassP t ^ 3 -
        21 * L.g₂ * L.weierstrassP t - 14 * L.g₃)) =
      (7 / 6 : ℂ) * ∑ t ∈ T.erase 0, (120 * L.weierstrassP t ^ 3 -
        18 * L.g₂ * L.weierstrassP t - 12 * L.g₃) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hscale]
  linear_combination (7 / 6 : ℂ) * h

end PeriodPair
