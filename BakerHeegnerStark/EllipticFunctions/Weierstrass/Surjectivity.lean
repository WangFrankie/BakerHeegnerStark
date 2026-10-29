/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Surjectivity of the actual Weierstrass function off its lattice

The reciprocal of `wp-c` has a genuine analytic extension with value zero
at every lattice pole. The local formula uses the actual analytic regular
part and `(z-l)² / (1+(z-l)²*regular(z))`; it does not treat the totalized
pole value of `wp` as an affine value.

If a complex value were omitted off the lattice, this regularized reciprocal
would be entire and lattice-periodic. Compactness of its range and Liouville
make it constant zero, contradicting its nonzero value at a half-period.
Consequently every complex value is attained at a point outside the lattice.
-/

open Filter
open scoped Topology
namespace PeriodPair

/-- The reciprocal of `wp-c`, with its analytic-extension value zero at the lattice poles. -/
noncomputable def weierstrassPReciprocal (L : PeriodPair) (c z : ℂ) : ℂ := by
  classical
  exact if z ∈ L.lattice then 0 else (L.weierstrassP z - c)⁻¹

/-- The actual double-pole principal part makes the regularized reciprocal analytic at each lattice point. -/
theorem analyticAt_weierstrassPReciprocal_of_mem (L : PeriodPair) (c l : ℂ)
    (hl : l ∈ L.lattice) : AnalyticAt ℂ (L.weierstrassPReciprocal c) l := by
  classical
  let g : ℂ → ℂ := fun z => L.weierstrassPExcept l z - 1 / l ^ 2 - c
  let q : ℂ → ℂ := fun z => (z - l) ^ 2
  let h : ℂ → ℂ := fun z => q z / (1 + q z * g z)
  have hg : AnalyticAt ℂ g l :=
    ((L.analyticAt_weierstrassPExcept l).sub analyticAt_const).sub analyticAt_const
  have hq : AnalyticAt ℂ q l := (analyticAt_id.sub analyticAt_const).pow 2
  have hh : AnalyticAt ℂ h l :=
    hq.div (analyticAt_const.add (hq.mul hg)) (by simp [q])
  apply hh.congr
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds l] with z hz
  by_cases hzl : z = l
  · subst z
    simp [weierstrassPReciprocal, hl, h, q]
  · have hzn : z ∉ L.lattice := fun hm => hz ⟨hm, hzl⟩
    rw [weierstrassPReciprocal, ite_eq_right hzn]
    change q z / (1 + q z * g z) = (L.weierstrassP z - c)⁻¹
    have hwp : L.weierstrassP z - c = g z + (q z)⁻¹ := by
      rw [← L.weierstrassPExcept_add ⟨l, hl⟩ z]
      dsimp [g, q]
      simp only [one_div]
      ring
    rw [hwp, ← inv_div]
    congr 1
    have hqz : q z ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hzl)
    field_simp [hqz]
    ring

/-- Off the lattice, the reciprocal is analytic where its denominator is nonzero. -/
theorem analyticAt_weierstrassPReciprocal_of_not_mem (L : PeriodPair) (c z : ℂ)
    (hz : z ∉ L.lattice) (hc : L.weierstrassP z ≠ c) :
    AnalyticAt ℂ (L.weierstrassPReciprocal c) z := by
  classical
  have h : AnalyticAt ℂ (fun w => (L.weierstrassP w - c)⁻¹) z :=
    ((L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const).inv (sub_ne_zero.mpr hc)
  apply h.congr
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
  change w ∉ L.lattice at hw
  simp only [weierstrassPReciprocal, ite_eq_right hw]

/-- The regularized reciprocal respects every actual lattice period. -/
theorem periodic_weierstrassPReciprocal (L : PeriodPair) (c : ℂ) (l : L.lattice) :
    Function.Periodic (L.weierstrassPReciprocal c) (l : ℂ) := by
  classical
  intro z
  simp only [weierstrassPReciprocal, L.weierstrassP_add_coe z l]
  congr 1
  simpa using (L.lattice.toAddSubgroup.add_mem_cancel_right (y := z) l.property)

/-- An omitted affine value would give an entire regularized reciprocal. -/
theorem differentiable_weierstrassPReciprocal_of_omits (L : PeriodPair) (c : ℂ)
    (hc : ∀ z, z ∉ L.lattice → L.weierstrassP z ≠ c) :
    Differentiable ℂ (L.weierstrassPReciprocal c) := by
  intro z
  by_cases hz : z ∈ L.lattice
  · exact (L.analyticAt_weierstrassPReciprocal_of_mem c z hz).differentiableAt
  · exact (L.analyticAt_weierstrassPReciprocal_of_not_mem c z hz (hc z hz)).differentiableAt

/-- Every complex value is attained off the actual lattice, not merely at a totalized pole. -/
theorem exists_not_mem_lattice_weierstrassP_eq (L : PeriodPair) (c : ℂ) :
    ∃ z : ℂ, z ∉ L.lattice ∧ L.weierstrassP z = c := by
  classical
  by_contra h
  have hmiss : ∀ z, z ∉ L.lattice → L.weierstrassP z ≠ c := by
    intro z hz heq
    exact h ⟨z, hz, heq⟩
  have hf := L.differentiable_weierstrassPReciprocal_of_omits c hmiss
  have hb := (IsZLattice.isCompact_range_of_periodic L.lattice _ hf.continuous
    (fun z w hw => L.periodic_weierstrassPReciprocal c ⟨w, hw⟩ z)).isBounded
  have heq := hf.apply_eq_apply_of_bounded hb (L.ω₁ / 2) 0
  have hz := L.ω₁_div_two_notMem_lattice
  have hc : L.weierstrassPReciprocal c (L.ω₁ / 2) ≠ 0 := by
    simp only [weierstrassPReciprocal, ite_eq_right hz, ne_eq, inv_eq_zero]
    exact sub_ne_zero.mpr (hmiss _ hz)
  apply hc
  exact heq.trans (by simp [weierstrassPReciprocal])

end PeriodPair
