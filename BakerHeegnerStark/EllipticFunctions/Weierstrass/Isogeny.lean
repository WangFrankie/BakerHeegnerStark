/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Ring

/-!
# Finite-coset formula for the actual Weierstrass function

For an inclusion of lattices with a finite complete, non-redundant set of coset
representatives, the fine-lattice Weierstrass function is a sum of translates
of the coarse-lattice function, with its constant term removed. At a pole we
cancel the common principal part before invoking analyticity; the totalized
Weierstrass function itself is not analytic there.
-/

namespace PeriodPair

private theorem weierstrassP_sub_eq_except_zero_sub (L M : PeriodPair) :
    (fun z => L.weierstrassP z - M.weierstrassP z) =
      (fun z => L.weierstrassPExcept 0 z - M.weierstrassPExcept 0 z) := by
  funext z
  have hL := L.weierstrassPExcept_def (0 : L.lattice) z
  have hM := M.weierstrassPExcept_def (0 : M.lattice) z
  simp only [ZeroMemClass.coe_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    div_zero, zero_sub] at hL hM
  rw [hL, hM]
  ring

/-- Cancelling the common principal part makes the difference analytic at zero,
including its actual totalized value there. No relation between the lattices is needed. -/
theorem analyticAt_weierstrassP_sub_zero (L M : PeriodPair) :
    AnalyticAt ℂ (fun z => L.weierstrassP z - M.weierstrassP z) 0 := by
  rw [weierstrassP_sub_eq_except_zero_sub]
  exact (L.analyticAt_weierstrassPExcept 0).fun_sub
    (M.analyticAt_weierstrassPExcept 0)

/-- The actual totalized difference has derivative zero at zero: after cancellation,
both regular parts have zero derivative. Neither individual function is differentiable there. -/
theorem hasDerivAt_weierstrassP_sub_zero (L M : PeriodPair) :
    HasDerivAt (fun z => L.weierstrassP z - M.weierstrassP z) 0 0 := by
  rw [weierstrassP_sub_eq_except_zero_sub]
  have hL := (L.analyticAt_weierstrassPExcept 0).differentiableAt.hasDerivAt
  have hM := (M.analyticAt_weierstrassPExcept 0).differentiableAt.hasDerivAt
  simp only [L.deriv_weierstrassPExcept_same, L.derivWeierstrassPExcept_zero_zero] at hL
  simp only [M.deriv_weierstrassPExcept_same, M.derivWeierstrassPExcept_zero_zero] at hM
  simpa only [sub_self] using hL.fun_sub hM

private theorem weierstrassP_sub_translate_eq (L M : PeriodPair) {a t : ℂ}
    (ha : a ∈ M.lattice) (hat : a - t ∈ L.lattice) :
    (fun z => M.weierstrassP z - L.weierstrassP (z - t)) =
      (fun z => M.weierstrassP (z - a) - L.weierstrassP (z - a)) := by
  funext z
  have hM := M.weierstrassP_sub_coe z ⟨a, ha⟩
  have hL := L.weierstrassP_add_coe (z - a) ⟨a - t, hat⟩
  rw [hM]
  rw [show z - a + (a - t) = z - t by ring] at hL
  rw [hL]

private theorem analyticAt_weierstrassP_sub_coset_sum (L M : PeriodPair)
    (T : Finset ℂ)
    (hLM : (L.lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ L.lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ L.lattice)
    (a : ℂ) :
    AnalyticAt ℂ (fun z => M.weierstrassP z - ∑ t ∈ T, L.weierstrassP (z - t)) a := by
  classical
  by_cases ha : a ∈ M.lattice
  · obtain ⟨t₀, ht₀, hat₀⟩ := hcover a ha
    have hmain : AnalyticAt ℂ
        (fun z => M.weierstrassP z - L.weierstrassP (z - t₀)) a := by
      rw [weierstrassP_sub_translate_eq L M ha hat₀]
      exact (analyticAt_weierstrassP_sub_zero M L).comp_of_eq
        (analyticAt_id.sub analyticAt_const : AnalyticAt ℂ (fun z : ℂ => z - a) a)
        (sub_self a)
    have hrest : AnalyticAt ℂ
        (fun z => ∑ t ∈ T.erase t₀, L.weierstrassP (z - t)) a := by
      refine Finset.analyticAt_fun_sum _ fun t ht => ?_
      obtain ⟨htt₀, htT⟩ := Finset.mem_erase.mp ht
      have hat : a - t ∉ L.lattice := by
        intro hat
        apply htt₀
        apply hTi t htT t₀ ht₀
        convert L.lattice.sub_mem hat₀ hat using 1
        ring
      exact (L.analyticOnNhd_weierstrassP (a - t) hat).comp (f := fun z : ℂ => z - t)
        (analyticAt_id.sub analyticAt_const)
    convert hmain.fun_sub hrest using 1
    funext z
    rw [← Finset.add_sum_erase T (fun t => L.weierstrassP (z - t)) ht₀]
    ring
  · have hterms : ∀ t ∈ T, a - t ∉ L.lattice := by
      intro t ht hat
      apply ha
      exact (by simpa only [sub_add_cancel] using
        M.lattice.add_mem (hLM hat) (hTM t ht))
    exact (M.analyticOnNhd_weierstrassP a ha).sub
      (Finset.analyticAt_fun_sum _ fun t ht =>
        (L.analyticOnNhd_weierstrassP (a - t) (hterms t ht)).comp
          (f := fun z : ℂ => z - t)
          (analyticAt_id.sub analyticAt_const))

/-- The actual finite-index lattice formula, valid also at totalized lattice poles.
The representatives need not contain zero. -/
theorem weierstrassP_finite_coset_sum (L M : PeriodPair) (T : Finset ℂ)
    (hLM : (L.lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ L.lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ L.lattice)
    (z : ℂ) :
    M.weierstrassP z = (∑ t ∈ T, L.weierstrassP (z - t)) -
      ∑ t ∈ T, L.weierstrassP t := by
  classical
  let f : ℂ → ℂ := fun w => M.weierstrassP w - ∑ t ∈ T, L.weierstrassP (w - t)
  have hf : Differentiable ℂ f := fun a =>
    (analyticAt_weierstrassP_sub_coset_sum L M T hLM hTM hTi hcover a).differentiableAt
  have hper : ∀ w l, l ∈ L.lattice → f (w + l) = f w := by
    intro w l hl
    dsimp only [f]
    rw [M.weierstrassP_add_coe w ⟨l, hLM hl⟩]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    simpa only [Subtype.coe_mk, add_sub_right_comm] using
      L.weierstrassP_add_coe (w - t) ⟨l, hl⟩
  have hb := (IsZLattice.isCompact_range_of_periodic L.lattice f hf.continuous hper).isBounded
  have heq := hf.apply_eq_apply_of_bounded hb z 0
  have hf₀ : f 0 = -(∑ t ∈ T, L.weierstrassP t) := by
    simp [f]
  rw [hf₀] at heq
  dsimp only [f] at heq
  exact sub_eq_iff_eq_add.mp heq |>.trans (by ring)

private theorem derivWeierstrassP_finite_coset_sum_of_notMem
    (L M : PeriodPair) (T : Finset ℂ)
    (hLM : (L.lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ L.lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ L.lattice)
    (z : ℂ) (hz : z ∉ M.lattice) :
    M.derivWeierstrassP z = ∑ t ∈ T, L.derivWeierstrassP (z - t) := by
  classical
  have hnot : ∀ t ∈ T, z - t ∉ L.lattice := by
    intro t ht hzt
    exact hz (by simpa only [sub_add_cancel] using M.lattice.add_mem (hLM hzt) (hTM t ht))
  have hderiv : HasDerivAt
      (fun w => (∑ t ∈ T, L.weierstrassP (w - t)) - ∑ t ∈ T, L.weierstrassP t)
      (∑ t ∈ T, L.derivWeierstrassP (z - t)) z := by
    apply HasDerivAt.sub_const
    apply HasDerivAt.fun_sum
    intro t ht
    have hd := (L.analyticOnNhd_weierstrassP (z - t) (hnot t ht)).differentiableAt.hasDerivAt
    rw [L.deriv_weierstrassP] at hd
    simpa only [Function.comp_def, id_eq, mul_one] using
      hd.comp z ((hasDerivAt_id z).sub_const t)
  have heq : M.weierstrassP =
      (fun w => (∑ t ∈ T, L.weierstrassP (w - t)) - ∑ t ∈ T, L.weierstrassP t) :=
    funext (weierstrassP_finite_coset_sum L M T hLM hTM hTi hcover)
  rw [← heq] at hderiv
  simpa only [M.deriv_weierstrassP] using hderiv.deriv

/-- The derivative-scale finite-coset formula holds at every point, including totalized
lattice poles. At a pole the singular summand and the fine-lattice derivative are both
zero; cancellation of their common principal part forces the remaining sum to vanish. -/
theorem derivWeierstrassP_finite_coset_sum (L M : PeriodPair) (T : Finset ℂ)
    (hLM : (L.lattice : Set ℂ) ⊆ M.lattice)
    (hTM : ∀ t ∈ T, t ∈ M.lattice)
    (hTi : ∀ s ∈ T, ∀ t ∈ T, s - t ∈ L.lattice → s = t)
    (hcover : ∀ a ∈ M.lattice, ∃ t ∈ T, a - t ∈ L.lattice)
    (z : ℂ) :
    M.derivWeierstrassP z = ∑ t ∈ T, L.derivWeierstrassP (z - t) := by
  classical
  by_cases hz : z ∈ M.lattice
  · obtain ⟨t₀, ht₀, hzt₀⟩ := hcover z hz
    have hmain : HasDerivAt
        (fun w => M.weierstrassP w - L.weierstrassP (w - t₀)) 0 z := by
      rw [weierstrassP_sub_translate_eq L M hz hzt₀]
      simpa only [Function.comp_def, id_eq, zero_mul] using
        (hasDerivAt_weierstrassP_sub_zero M L).comp_of_eq z
          ((hasDerivAt_id z).sub_const z) (sub_self z).symm
    have hrest : HasDerivAt
        (fun w => ∑ t ∈ T.erase t₀, L.weierstrassP (w - t))
        (∑ t ∈ T.erase t₀, L.derivWeierstrassP (z - t)) z := by
      apply HasDerivAt.fun_sum
      intro t ht
      obtain ⟨htt₀, htT⟩ := Finset.mem_erase.mp ht
      have hzt : z - t ∉ L.lattice := by
        intro hzt
        apply htt₀
        apply hTi t htT t₀ ht₀
        convert L.lattice.sub_mem hzt₀ hzt using 1
        ring
      have hd := (L.analyticOnNhd_weierstrassP (z - t) hzt).differentiableAt.hasDerivAt
      rw [L.deriv_weierstrassP] at hd
      simpa only [Function.comp_def, id_eq, mul_one] using
        hd.comp z ((hasDerivAt_id z).sub_const t)
    have hderiv : HasDerivAt
        (fun w => M.weierstrassP w - ∑ t ∈ T, L.weierstrassP (w - t))
        (-(∑ t ∈ T.erase t₀, L.derivWeierstrassP (z - t))) z := by
      convert hmain.fun_sub hrest using 1
      · funext w
        rw [← Finset.add_sum_erase T (fun t => L.weierstrassP (w - t)) ht₀]
        ring
      · ring
    have heq : (fun w => M.weierstrassP w - ∑ t ∈ T, L.weierstrassP (w - t)) =
        fun _ => -(∑ t ∈ T, L.weierstrassP t) := by
      funext w
      rw [weierstrassP_finite_coset_sum L M T hLM hTM hTi hcover w]
      ring
    rw [heq] at hderiv
    have hsum : ∑ t ∈ T.erase t₀, L.derivWeierstrassP (z - t) = 0 :=
      neg_eq_zero.mp (hderiv.unique (hasDerivAt_const z (-(∑ t ∈ T, L.weierstrassP t))))
    have hMzero : M.derivWeierstrassP z = 0 := M.derivWeierstrassP_coe ⟨z, hz⟩
    have hLzero : L.derivWeierstrassP (z - t₀) = 0 :=
      L.derivWeierstrassP_coe ⟨z - t₀, hzt₀⟩
    rw [hMzero, ← Finset.add_sum_erase T (fun t => L.derivWeierstrassP (z - t)) ht₀,
      hLzero, hsum, add_zero]
  · exact derivWeierstrassP_finite_coset_sum_of_notMem L M T hLM hTM hTi hcover z hz

end PeriodPair
