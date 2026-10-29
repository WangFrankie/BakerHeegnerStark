/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Weierstrass.Invariants
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order

/-!
# Uniqueness from Actual Weierstrass Invariants

Cancelling the common double-pole principal part gives a nonresonant first-order
equation, which determines the analytic germ. The identity principle on the
complement of the remaining poles and their orders recover the actual lattice.
-/

namespace BakerHeegnerStark

open Filter
open scoped Topology

/-- The nonresonant regular-singular equation arising from a Weierstrass
difference has no nonzero analytic germ: its leading order would satisfy
`-4n = 12` for a natural number `n`. -/
theorem analytic_eventuallyEq_zero_of_weierstrass_difference_equation
    (f A B : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hA : AnalyticAt ℂ A 0)
    (hB : AnalyticAt ℂ B 0) (hA₀ : A 0 = -4) (hB₀ : B 0 = 12)
    (hde : ∀ᶠ z in 𝓝 0, z * A z * deriv f z = B z * f z) :
    f =ᶠ[𝓝 0] 0 := by
  apply analyticOrderAt_eq_top.mp
  by_contra hfinite
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  obtain ⟨g, hg, hg₀, hfg'⟩ := hf.analyticOrderAt_eq_natCast.mp hn.symm
  have hfg : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * g z := by
    filter_upwards [hfg'] with z hz
    simpa only [sub_zero, smul_eq_mul] using hz
  have hd : ∀ᶠ z in 𝓝 (0 : ℂ),
      z * deriv f z = z ^ n * ((n : ℂ) * g z + z * deriv g z) := by
    filter_upwards [hfg.deriv, hg.eventually_analyticAt] with z hdz hgz
    have hp := ((hasDerivAt_id z).pow n).mul hgz.differentiableAt.hasDerivAt
    change HasDerivAt (fun w => w ^ n * g w)
      ((n : ℂ) * z ^ (n - 1) * 1 * g z + z ^ n * deriv g z) z at hp
    rw [hdz, hp.deriv]
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.succ_sub_one, pow_succ, mul_one]
      ring
  have heq : (fun z => A z * ((n : ℂ) * g z + z * deriv g z)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => B z * g z) := by
    filter_upwards [hde.filter_mono nhdsWithin_le_nhds,
      hfg.filter_mono nhdsWithin_le_nhds, hd.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hdez hfz hdz hz
    have hz₀ : z ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    apply mul_left_cancel₀ (pow_ne_zero n hz₀)
    calc
      z ^ n * (A z * ((n : ℂ) * g z + z * deriv g z)) =
          A z * (z ^ n * ((n : ℂ) * g z + z * deriv g z)) := by ring
      _ = A z * (z * deriv f z) := by rw [← hdz]
      _ = z * A z * deriv f z := by ring
      _ = B z * f z := hdez
      _ = z ^ n * (B z * g z) := by rw [hfz]; ring
  have hcl : ContinuousAt (fun z => A z * ((n : ℂ) * g z + z * deriv g z)) 0 :=
    hA.continuousAt.mul ((continuousAt_const.mul hg.continuousAt).add
      (continuousAt_id.mul hg.deriv.continuousAt))
  have hcr : ContinuousAt (fun z => B z * g z) 0 := hB.continuousAt.mul hg.continuousAt
  have heq₀ : A 0 * ((n : ℂ) * g 0 + 0 * deriv g 0) = B 0 * g 0 :=
    tendsto_nhds_unique (hcl.mono_left nhdsWithin_le_nhds)
      ((hcr.mono_left nhdsWithin_le_nhds).congr' heq.symm)
  rw [hA₀, hB₀, zero_mul, add_zero] at heq₀
  have hnum : (-4 : ℂ) * (n : ℂ) = 12 :=
    mul_right_cancel₀ hg₀ (by simpa only [mul_assoc] using heq₀)
  have hreal := congrArg Complex.re hnum
  norm_num at hreal
  have hn₀ : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

private theorem weierstrassP_regular_part_relations (L : PeriodPair) (z : ℂ)
    (hz : z ∈ ((L.lattice : Set ℂ) \ {0})ᶜ) :
    L.weierstrassP z = L.weierstrassPExcept 0 z + 1 / z ^ 2 ∧
      L.derivWeierstrassP z = deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 := by
  constructor
  · have h := L.weierstrassPExcept_def (0 : L.lattice) z
    simp only [ZeroMemClass.coe_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
      div_zero, zero_sub] at h
    linear_combination -h
  · have hd := L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz
    have h := L.derivWeierstrassPExcept_def (0 : L.lattice) z
    simp only [ZeroMemClass.coe_zero, sub_zero] at h
    linear_combination -hd - h

/-- The regular parts of actual Weierstrass functions with equal invariants
agree near the common pole, by the nonresonant first-order difference equation. -/
theorem weierstrassPExcept_eventuallyEq_of_invariants (L M : PeriodPair)
    (h₂ : L.g₂ = M.g₂) (h₃ : L.g₃ = M.g₃) :
    L.weierstrassPExcept 0 =ᶠ[𝓝 (0 : ℂ)] M.weierstrassPExcept 0 := by
  let r := L.weierstrassPExcept 0
  let s := M.weierstrassPExcept 0
  let f : ℂ → ℂ := fun z => r z - s z
  let A : ℂ → ℂ := fun z => z ^ 3 * (deriv r z + deriv s z) - 4
  let B : ℂ → ℂ := fun z => 12 + 12 * z ^ 2 * (r z + s z) +
    z ^ 4 * (4 * (r z ^ 2 + r z * s z + s z ^ 2) - L.g₂)
  have hr : AnalyticAt ℂ r 0 := L.analyticAt_weierstrassPExcept 0
  have hs : AnalyticAt ℂ s 0 := M.analyticAt_weierstrassPExcept 0
  have hrd : AnalyticAt ℂ (deriv r) 0 := hr.deriv
  have hsd : AnalyticAt ℂ (deriv s) 0 := hs.deriv
  have hA : AnalyticAt ℂ A 0 := by dsimp only [A]; fun_prop
  have hB : AnalyticAt ℂ B 0 := by dsimp only [B]; fun_prop
  have hde : ∀ᶠ z in 𝓝 (0 : ℂ), z * A z * deriv f z = B z * f z := by
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ),
      M.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ)] with z hzL hzM
    by_cases hz₀ : z = 0
    · subst z
      simp [f, A, B, r, s]
    · have hzL' : z ∉ L.lattice := by simpa [hz₀] using hzL
      have hzM' : z ∉ M.lattice := by simpa [hz₀] using hzM
      obtain ⟨hpL, hdL⟩ := weierstrassP_regular_part_relations L z hzL
      obtain ⟨hpM, hdM⟩ := weierstrassP_regular_part_relations M z hzM
      have hL := L.derivWeierstrassP_sq z hzL'
      have hM := M.derivWeierstrassP_sq z hzM'
      rw [hpL, hdL] at hL
      rw [hpM, hdM, ← h₂, ← h₃] at hM
      have hrz := L.analyticOnNhd_weierstrassPExcept 0 z hzL
      have hsz := M.analyticOnNhd_weierstrassPExcept 0 z hzM
      dsimp only [A, B, f, r, s]
      rw [deriv_fun_sub hrz.differentiableAt hsz.differentiableAt]
      linear_combination (norm := (field_simp [hz₀]; ring)) z ^ 4 * hL - z ^ 4 * hM
  have hzero := analytic_eventuallyEq_zero_of_weierstrass_difference_equation
    f A B (hr.fun_sub hs) hA hB (by simp [A]) (by simp [B]) hde
  filter_upwards [hzero] with z hz
  change r z - s z = 0 at hz
  exact sub_eq_zero.mp hz

/-- Equal actual invariants determine the same local meromorphic Weierstrass
germ, with the common principal part cancelled rather than assumed. -/
theorem weierstrassP_eventuallyEq_of_invariants (L M : PeriodPair)
    (h₂ : L.g₂ = M.g₂) (h₃ : L.g₃ = M.g₃) :
    L.weierstrassP =ᶠ[𝓝 (0 : ℂ)] M.weierstrassP := by
  filter_upwards [weierstrassPExcept_eventuallyEq_of_invariants L M h₂ h₃] with z hz
  have hL := L.weierstrassPExcept_def (0 : L.lattice) z
  have hM := M.weierstrassPExcept_def (0 : M.lattice) z
  simp only [ZeroMemClass.coe_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    div_zero, zero_sub] at hL hM
  linear_combination -hL + hM + hz

/-- The regular parts agree off the countable union of their remaining poles.
Analytic continuation on this connected domain then identifies the pole sets
by their meromorphic orders, hence the actual period lattices. -/
theorem periodPair_lattice_eq_of_invariants (L M : PeriodPair)
    (h₂ : L.g₂ = M.g₂) (h₃ : L.g₃ = M.g₃) :
    L.lattice = M.lattice := by
  let U : Set ℂ := (((L.lattice : Set ℂ) \ {0}) ∪ ((M.lattice : Set ℂ) \ {0}))ᶜ
  have hLcount : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hMcount : (M.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := M.lattice)
  have hconn : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      ((hLcount.mono Set.sdiff_subset).union (hMcount.mono Set.sdiff_subset))).isPreconnected
  have heq : Set.EqOn (L.weierstrassPExcept 0) (M.weierstrassPExcept 0) U := by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      ((L.analyticOnNhd_weierstrassPExcept 0).mono ?_)
      ((M.analyticOnNhd_weierstrassPExcept 0).mono ?_) hconn (by simp [U])
      (weierstrassPExcept_eventuallyEq_of_invariants L M h₂ h₃)
    · intro z hz h
      exact hz (Or.inl h)
    · intro z hz h
      exact hz (Or.inr h)
  have hgerm (x : ℂ) : L.weierstrassP =ᶠ[𝓝[≠] x] M.weierstrassP := by
    filter_upwards [
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (L.compl_lattice_sdiff_singleton_mem_nhds x),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (M.compl_lattice_sdiff_singleton_mem_nhds x),
      (self_mem_nhdsWithin : ({x} : Set ℂ)ᶜ ∈ 𝓝[≠] x)] with z hzL hzM hzx
    have hzL' : z ∉ L.lattice := fun h => hzL ⟨h, by simpa using hzx⟩
    have hzM' : z ∉ M.lattice := fun h => hzM ⟨h, by simpa using hzx⟩
    have hzU : z ∈ U := by
      rintro (h | h)
      · exact hzL' h.1
      · exact hzM' h.1
    have h := heq hzU
    have hL := L.weierstrassPExcept_def (0 : L.lattice) z
    have hM := M.weierstrassPExcept_def (0 : M.lattice) z
    simp only [ZeroMemClass.coe_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
      div_zero, zero_sub] at hL hM
    linear_combination -hL + hM + h
  apply le_antisymm
  · intro x hx
    by_contra hxM
    have horder := (M.analyticOnNhd_weierstrassP x hxM).meromorphicOrderAt_nonneg
    rw [← meromorphicOrderAt_congr (hgerm x), L.order_weierstrassP x hx] at horder
    exact (by decide : ¬ (0 : WithTop ℤ) ≤ -2) horder
  · intro x hx
    by_contra hxL
    have horder := (L.analyticOnNhd_weierstrassP x hxL).meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_congr (hgerm x), M.order_weierstrassP x hx] at horder
    exact (by decide : ¬ (0 : WithTop ℤ) ≤ -2) horder

/-- Equal numerical invariants determine the actual global Weierstrass
function, including its prescribed values at lattice points. -/
theorem weierstrassP_eq_of_invariants (L M : PeriodPair)
    (h₂ : L.g₂ = M.g₂) (h₃ : L.g₃ = M.g₃) :
    L.weierstrassP = M.weierstrassP :=
  (weierstrassP_eq_iff_lattice_eq L M).mpr (periodPair_lattice_eq_of_invariants L M h₂ h₃)

end BakerHeegnerStark
