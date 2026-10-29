/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# The Weierstrass local parameter at infinity

For the coordinates `(wp z, wp' z / 2)`, the parameter `-x/y` extends
analytically across the lattice origin, with derivative one. Its local analytic
inverse is supplied by the inverse function theorem. No assertion is made about
the totalized quotient at other zeros of `wp'`, or about global injectivity.
-/

namespace PeriodPair

open Filter
open scoped Topology

/-- The origin-filled quotient parameter for prescribed double/triple principal parts.
Only its germ at zero is used; under the hypotheses below this is the genuine analytic extension. -/
noncomputable def weierstrassPoleParameter (L : PeriodPair) (a b : ℂ)
    (A B : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else -2 * (a * L.weierstrassP z + A z) / (b * L.derivWeierstrassP z + B z)

/-- The chosen origin value is zero; analyticity is proved under the hypotheses below. -/
@[simp] theorem weierstrassPoleParameter_zero (L : PeriodPair) (a b : ℂ) (A B : ℂ → ℂ) :
    L.weierstrassPoleParameter a b A B 0 = 0 := by simp [weierstrassPoleParameter]

/-- Cancellation of the actual double/triple poles gives this local rational identity.
The identity itself does not require analytic remainder terms or a nonzero leading coefficient. -/
theorem weierstrassPoleParameter_eventuallyEq (L : PeriodPair) (a b : ℂ)
    (A B : ℂ → ℂ) :
    L.weierstrassPoleParameter a b A B =ᶠ[𝓝 (0 : ℂ)]
      (fun z => z * (a * (1 + L.weierstrassPExcept 0 z * z ^ 2) + A z * z ^ 2) /
        (b * (1 - deriv (L.weierstrassPExcept 0) z * z ^ 3 / 2) - B z * z ^ 3 / 2)) := by
  let h := L.weierstrassPExcept 0
  let D : ℂ → ℂ := fun z => b * (1 - deriv h z * z ^ 3 / 2) - B z * z ^ 3 / 2
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ)] with z hz
  by_cases hz0 : z = 0
  · subst z
    simp
  · have hp : L.weierstrassP z = h z + 1 / z ^ 2 := by
      have hp := L.weierstrassPExcept_add (0 : L.lattice) z
      simpa only [ZeroMemClass.coe_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
        div_zero, sub_zero] using hp.symm
    have hd : L.derivWeierstrassP z = deriv h z - 2 / z ^ 3 := by
      have hd := L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz
      have he := L.derivWeierstrassPExcept_def (0 : L.lattice) z
      simp only [ZeroMemClass.coe_zero, sub_zero] at he
      change deriv h z = _ at hd
      linear_combination -hd - he
    have hden : b * (deriv h z - 2 / z ^ 3) + B z = -2 * D z / z ^ 3 := by
      dsimp only [D]
      field_simp [hz0]
      ring
    simp only [weierstrassPoleParameter, ite_eq_right hz0]
    change -2 * (a * L.weierstrassP z + A z) / (b * L.derivWeierstrassP z + B z) =
      z * (a * (1 + h z * z ^ 2) + A z * z ^ 2) / D z
    rw [hp, hd, hden]
    by_cases hDz : D z = 0
    · simp [hDz]
    · field_simp [hz0, hDz]
      ring

/-- Analytic remainder terms and a nonzero triple-pole coefficient make the parameter analytic. -/
theorem analyticAt_weierstrassPoleParameter_zero (L : PeriodPair) (a b : ℂ)
    (A B : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hb : b ≠ 0) :
    AnalyticAt ℂ (L.weierstrassPoleParameter a b A B) 0 := by
  have hh := L.analyticAt_weierstrassPExcept (0 : ℂ)
  have h : AnalyticAt ℂ
      (fun z => z * (a * (1 + L.weierstrassPExcept 0 z * z ^ 2) + A z * z ^ 2) /
        (b * (1 - deriv (L.weierstrassPExcept 0) z * z ^ 3 / 2) - B z * z ^ 3 / 2)) 0 := by
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · simpa using hb
  exact h.congr (L.weierstrassPoleParameter_eventuallyEq a b A B).symm

/-- The differential of the filled pole quotient is the ratio of its leading coefficients. -/
theorem hasDerivAt_weierstrassPoleParameter_zero (L : PeriodPair) (a b : ℂ)
    (A B : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hb : b ≠ 0) :
    HasDerivAt (L.weierstrassPoleParameter a b A B) (a / b) 0 := by
  let h := L.weierstrassPExcept 0
  have hh : AnalyticAt ℂ h 0 := L.analyticAt_weierstrassPExcept 0
  have hhd := hh.differentiableAt.hasDerivAt
  have hhdd := hh.deriv.differentiableAt.hasDerivAt
  have hAd := hA.differentiableAt.hasDerivAt
  have hBd := hB.differentiableAt.hasDerivAt
  have hN : HasDerivAt
      (fun z => z * (a * (1 + h z * z ^ 2) + A z * z ^ 2)) a 0 := by
    convert! (hasDerivAt_id (0 : ℂ)).mul
      ((((hhd.mul ((hasDerivAt_id (0 : ℂ)).pow 2)).const_add 1).const_mul a).add
        (hAd.mul ((hasDerivAt_id (0 : ℂ)).pow 2))) using 1
    simp
  have hD : HasDerivAt
      (fun z => b * (1 - deriv h z * z ^ 3 / 2) - B z * z ^ 3 / 2) 0 0 := by
    convert! (((hasDerivAt_const 0 (1 : ℂ)).sub
      ((hhdd.mul ((hasDerivAt_id (0 : ℂ)).pow 3)).div_const 2)).const_mul b).sub
        ((hBd.mul ((hasDerivAt_id (0 : ℂ)).pow 3)).div_const 2) using 1
    simp
  have hT : HasDerivAt
      (fun z => z * (a * (1 + h z * z ^ 2) + A z * z ^ 2) /
        (b * (1 - deriv h z * z ^ 3 / 2) - B z * z ^ 3 / 2)) (a / b) 0 := by
    convert! hN.div hD (by simpa using hb) using 1
    simp
    field_simp [hb]
  exact hT.congr_of_eventuallyEq (L.weierstrassPoleParameter_eventuallyEq a b A B)


/-- The parameter `-x/y` for the Weierstrass coordinates `(wp z, wp' z / 2)`.
The quotient is totalized; only its germ at zero is used as a local parameter. -/
noncomputable def weierstrassParameter (L : PeriodPair) (z : ℂ) : ℂ :=
  -2 * L.weierstrassP z / L.derivWeierstrassP z

@[simp]
theorem weierstrassParameter_zero (L : PeriodPair) : L.weierstrassParameter 0 = 0 := by
  simp [weierstrassParameter]

private theorem weierstrassParameter_eq_poleParameter (L : PeriodPair) :
    L.weierstrassParameter = L.weierstrassPoleParameter 1 1 (fun _ => 0) (fun _ => 0) := by
  funext z
  by_cases hz : z = 0
  · subst z
    simp
  · simp [weierstrassParameter, weierstrassPoleParameter, hz]

/-- Cancellation of the poles gives the actual analytic expression for the
parameter near zero, including its totalized value at zero. -/
theorem weierstrassParameter_eventuallyEq (L : PeriodPair) :
    L.weierstrassParameter =ᶠ[𝓝 (0 : ℂ)]
      (fun u => u * (1 + L.weierstrassPExcept 0 u * u ^ 2) /
        (1 - deriv (L.weierstrassPExcept 0) u * u ^ 3 / 2)) := by
  simpa only [← weierstrassParameter_eq_poleParameter, one_mul, zero_mul, add_zero,
    zero_div, sub_zero] using L.weierstrassPoleParameter_eventuallyEq 1 1 (fun _ => 0) (fun _ => 0)

/-- The totalized parameter is analytic at the lattice origin. -/
theorem analyticAt_weierstrassParameter_zero (L : PeriodPair) :
    AnalyticAt ℂ L.weierstrassParameter 0 := by
  simpa only [← weierstrassParameter_eq_poleParameter] using
    L.analyticAt_weierstrassPoleParameter_zero 1 1 (fun _ => 0) (fun _ => 0)
      analyticAt_const analyticAt_const one_ne_zero

/-- The parameter at infinity is normalized to have derivative one. -/
theorem hasDerivAt_weierstrassParameter_zero (L : PeriodPair) :
    HasDerivAt L.weierstrassParameter 1 0 := by
  simpa only [← weierstrassParameter_eq_poleParameter, div_one] using
    L.hasDerivAt_weierstrassPoleParameter_zero 1 1 (fun _ => 0) (fun _ => 0)
      analyticAt_const analyticAt_const one_ne_zero

/-- The actual Weierstrass parameter admits a normalized analytic local inverse
at zero. Both inverse identities hold on full neighborhoods of zero. -/
theorem exists_weierstrassParameter_inverse (L : PeriodPair) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ HasDerivAt g 1 0 ∧
      (fun z => g (L.weierstrassParameter z)) =ᶠ[𝓝 (0 : ℂ)] id ∧
      (fun z => L.weierstrassParameter (g z)) =ᶠ[𝓝 (0 : ℂ)] id := by
  have ha := L.analyticAt_weierstrassParameter_zero
  have hd := L.hasDerivAt_weierstrassParameter_zero
  have hne : deriv L.weierstrassParameter 0 ≠ 0 := by rw [hd.deriv]; exact one_ne_zero
  let g := ha.hasStrictDerivAt.localInverse _ _ _ hne
  have hg : AnalyticAt ℂ g 0 := by
    simpa only [weierstrassParameter_zero] using ha.analyticAt_localInverse hne
  have hg₀ : g 0 = 0 := by
    simpa only [weierstrassParameter_zero] using
      (ha.hasStrictDerivAt.hasStrictFDerivAt_equiv hne).localInverse_apply_image
  have hgd : HasDerivAt g 1 0 := by
    simpa only [weierstrassParameter_zero, hd.deriv, inv_one] using
      (ha.hasStrictDerivAt.to_localInverse hne).hasDerivAt
  refine ⟨g, hg, hg₀, hgd, ?_, ?_⟩
  · exact ha.hasStrictDerivAt.eventually_left_inverse hne
  · have hright := ha.hasStrictDerivAt.eventually_right_inverse hne
    rw [weierstrassParameter_zero] at hright
    exact hright

end PeriodPair
