/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Weierstrass.Translation

/-!
# Analytic Weierstrass translation at the origin

Cancelling the double pole in the rational translation x-coordinate gives an
analytic germ with value `wp z` and derivative `wp' z`. The lattice filling
agrees with this germ, without any restriction on the fixed argument `z`.
-/

namespace PeriodPair

open Filter
open scoped Topology

private theorem weierstrassTranslateX_local_extension (L : PeriodPair) (z : ℂ) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧
      HasDerivAt Q (L.derivWeierstrassP z) 0 ∧
      Q =ᶠ[𝓝 (0 : ℂ)] L.weierstrassTranslateX z := by
  let h := L.weierstrassPExcept 0
  let a := L.weierstrassP z
  let b := L.derivWeierstrassP z
  let D : ℂ → ℂ := fun u => 1 + (h u - a) * u ^ 2
  let N : ℂ → ℂ := fun u =>
    2 * (a - h u) + (b - deriv h u) * u - (h u - a) ^ 2 * u ^ 2 +
      ((deriv h u - b) ^ 2 / 4) * u ^ 4
  let Q : ℂ → ℂ := fun u => N u / D u ^ 2 - (a + h u)
  have hh : AnalyticAt ℂ h 0 := L.analyticAt_weierstrassPExcept 0
  have hh₀ : h 0 = 0 := by simp [h]
  have hdh₀ : deriv h 0 = 0 := by simp [h]
  have hhd : HasDerivAt h 0 0 := by
    simpa only [hdh₀] using hh.differentiableAt.hasDerivAt
  have hhdd := hh.deriv.differentiableAt.hasDerivAt
  have hD : AnalyticAt ℂ D 0 := by dsimp only [D]; fun_prop
  have hN : AnalyticAt ℂ N 0 := by dsimp only [N]; fun_prop
  have hD₀ : D 0 = 1 := by simp [D]
  have hQ : AnalyticAt ℂ Q 0 :=
    (hN.div (hD.pow 2) (by simp [hD₀])).sub (analyticAt_const.add hh)
  have hdD : HasDerivAt D 0 0 := by
    convert! (hasDerivAt_const 0 (1 : ℂ)).add
        ((hhd.sub_const a).mul ((hasDerivAt_id (0 : ℂ)).pow 2)) using 1
    simp
  have hdN : HasDerivAt N b 0 := by
    convert! (((hhd.const_sub a).const_mul 2).add
        (((hasDerivAt_const 0 b).sub hhdd).mul (hasDerivAt_id (0 : ℂ)))).sub
          (((hhd.sub_const a).pow 2).mul ((hasDerivAt_id (0 : ℂ)).pow 2)) |>.add
            (((hhdd.sub_const b).pow 2).div_const 4 |>.mul
              ((hasDerivAt_id (0 : ℂ)).pow 4)) using 1
    simp [hh₀, hdh₀]
  have hdQ : HasDerivAt Q b 0 := by
    convert! (hdN.div (hdD.pow 2) (by simp [hD₀])).sub (hhd.const_add a) using 1
    simp [hD₀]
  refine ⟨Q, hQ, hdQ, ?_⟩
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ),
    hD.continuousAt.eventually_ne (by simp [hD₀] : D 0 ≠ 0)] with u hu hDu
  by_cases hu₀ : u = 0
  · subst u
    simp [Q, N, D, hh₀, weierstrassTranslateX, a]
    ring
  · have huL : u ∉ L.lattice := by simpa [hu₀] using hu
    have hp : L.weierstrassP u = h u + 1 / u ^ 2 := by
      have hp := L.weierstrassPExcept_add (0 : L.lattice) u
      simpa only [ZeroMemClass.coe_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
        div_zero, sub_zero] using hp.symm
    have hd : L.derivWeierstrassP u = deriv h u - 2 / u ^ 3 := by
      have hd := L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hu
      have he := L.derivWeierstrassPExcept_def (0 : L.lattice) u
      simp only [ZeroMemClass.coe_zero, sub_zero] at he
      change deriv h u = _ at hd
      linear_combination -hd - he
    have hden : h u + 1 / u ^ 2 - a = D u / u ^ 2 := by
      dsimp only [D]
      field_simp [hu₀]
      ring
    simp only [weierstrassTranslateX, ite_eq_right huL, hp, hd]
    change Q u = ((deriv h u - 2 / u ^ 3 - b) /
      (2 * (h u + 1 / u ^ 2 - a))) ^ 2 - (h u + 1 / u ^ 2) - a
    rw [hden]
    dsimp only [Q, N]
    generalize hddef : D u = d at hDu ⊢
    field_simp [hu₀, hDu]
    rw [← hddef]
    dsimp only [D]
    ring

/-- The pole-filled rational translation x-coordinate is analytic at the origin,
for every fixed first argument, including lattice arguments. -/
theorem analyticAt_weierstrassTranslateX_zero (L : PeriodPair) (z : ℂ) :
    AnalyticAt ℂ (L.weierstrassTranslateX z) 0 := by
  obtain ⟨Q, hQ, _, heq⟩ := weierstrassTranslateX_local_extension L z
  exact hQ.congr heq

/-- At the origin the translation x-coordinate has the actual Weierstrass
first derivative at the fixed argument. -/
theorem hasDerivAt_weierstrassTranslateX_zero (L : PeriodPair) (z : ℂ) :
    HasDerivAt (L.weierstrassTranslateX z) (L.derivWeierstrassP z) 0 := by
  obtain ⟨Q, _, hdQ, heq⟩ := weierstrassTranslateX_local_extension L z
  exact hdQ.congr_of_eventuallyEq heq.symm

end PeriodPair
