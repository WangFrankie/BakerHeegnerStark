/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Weierstrass.Parameter
import BakerHeegnerStark.EllipticCurves.JInvariant.Coordinates

/-!
# Recovering the actual infinity branch from pole coordinates

Prescribed double and triple principal parts force an analytic lift through the
actual Weierstrass uniformization. The proof retains the finite/infinite point
branch and separates the root tending to one in the rescaled cubic equation;
neither the totalized projections nor the quotient parameter is globally injective.
-/

namespace BakerHeegnerStark

open Filter
open scoped Topology

private theorem periodCurve_equation_of_X_ne_zero (τ : UpperHalfPlane)
    (P : (periodCurve (standardPeriodPair τ)).toAffine.Point)
    (hx : periodCurveX τ P ≠ 0) :
    (periodCurveY τ P) ^ 2 = (periodCurveX τ P) ^ 3 +
      (periodCurve (standardPeriodPair τ)).a₄ * periodCurveX τ P +
      (periodCurve (standardPeriodPair τ)).a₆ := by
  cases P with
  | zero => exact (hx rfl).elim
  | some x y h =>
    have he := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at he
    change y ^ 2 = x ^ 3 + (periodCurve (standardPeriodPair τ)).a₄ * x +
      (periodCurve (standardPeriodPair τ)).a₆
    simpa only [periodCurve, zero_mul, zero_add, add_zero] using he

private theorem periodCurve_eq_of_coordinates_of_X_ne_zero (τ : UpperHalfPlane)
    (P Q : (periodCurve (standardPeriodPair τ)).toAffine.Point)
    (hne : periodCurveX τ P ≠ 0)
    (hx : periodCurveX τ P = periodCurveX τ Q)
    (hy : periodCurveY τ P = periodCurveY τ Q) : P = Q := by
  cases P with
  | zero => exact (hne rfl).elim
  | some x y h =>
    cases Q with
    | zero => exact (hne hx).elim
    | some x' y' h' =>
      change x = x' at hx
      change y = y' at hy
      cases hx
      cases hy
      rfl

private theorem infinity_branch_coordinates (t x₁ y₁ x₂ y₂ c d : ℂ)
    (ht : t ≠ 0) (h₁ : y₁ ^ 2 = x₁ ^ 3 + c * x₁ + d)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 + c * x₂ + d)
    (ht₁ : t * y₁ = -x₁) (ht₂ : t * y₂ = -x₂)
    (hbranch : t ^ 2 * x₁ + t ^ 2 * x₂ - (t ^ 2 * x₁) ^ 2 -
      (t ^ 2 * x₁) * (t ^ 2 * x₂) - (t ^ 2 * x₂) ^ 2 - c * t ^ 4 ≠ 0) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hu₁ : (t ^ 2 * x₁) ^ 2 = (t ^ 2 * x₁) ^ 3 +
      c * (t ^ 2 * x₁) * t ^ 4 + d * t ^ 6 := by
    linear_combination -t ^ 4 * congrArg (fun z : ℂ => z ^ 2) ht₁ + t ^ 6 * h₁
  have hu₂ : (t ^ 2 * x₂) ^ 2 = (t ^ 2 * x₂) ^ 3 +
      c * (t ^ 2 * x₂) * t ^ 4 + d * t ^ 6 := by
    linear_combination -t ^ 4 * congrArg (fun z : ℂ => z ^ 2) ht₂ + t ^ 6 * h₂
  have hmul : (t ^ 2 * x₁ - t ^ 2 * x₂) *
      (t ^ 2 * x₁ + t ^ 2 * x₂ - (t ^ 2 * x₁) ^ 2 -
        (t ^ 2 * x₁) * (t ^ 2 * x₂) - (t ^ 2 * x₂) ^ 2 - c * t ^ 4) = 0 := by
    linear_combination hu₁ - hu₂
  have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 ht)
    (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hbranch))
  refine ⟨hx, mul_left_cancel₀ ht ?_⟩
  rw [ht₁, ht₂, hx]

private theorem weierstrass_regular_coordinates (L : PeriodPair) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      L.weierstrassP z = (1 + L.weierstrassPExcept 0 z * z ^ 2) / z ^ 2 ∧
      L.derivWeierstrassP z / 2 =
        -(1 - deriv (L.weierstrassPExcept 0) z * z ^ 3 / 2) / z ^ 3 := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ)), self_mem_nhdsWithin] with z hz hz0
  have hne : z ≠ 0 := hz0
  have hp := L.weierstrassPExcept_add (0 : L.lattice) z
  simp only [ZeroMemClass.coe_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    div_zero, sub_zero] at hp
  have hd := L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz
  have he := L.derivWeierstrassPExcept_def (0 : L.lattice) z
  simp only [ZeroMemClass.coe_zero, sub_zero] at he
  constructor
  · rw [← hp]
    field_simp [hne]
    ring
  · rw [← hd] at he
    have he' : L.derivWeierstrassP z = deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 := by
      linear_combination -he
    rw [he']
    field_simp [hne]
    ring

/-- Actual point-valued pole coordinates, without any continuity assumption on
`F`, determine an analytic local lift through the actual uniformization. -/
theorem exists_analytic_lift_of_pole_coordinates [DecidableEq ℂ]
    (τ : UpperHalfPlane)
    (F : ℂ → (periodCurve (standardPeriodPair τ)).toAffine.Point)
    (hF₀ : F 0 = 0) (a b : ℂ) (hb : b ≠ 0) (hab : a ^ 3 = b ^ 2)
    (A B : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0)
    (hX : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      periodCurveX τ (F z) = a * (standardPeriodPair τ).weierstrassP z + A z)
    (hY : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      periodCurveY τ (F z) = b * (standardPeriodPair τ).derivWeierstrassP z / 2 + B z) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ HasDerivAt g (a / b) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), F z = standardPeriodPoint τ (g z) := by
  let L := standardPeriodPair τ
  let h := L.weierstrassPExcept 0
  let p : ℂ → ℂ := fun z => 1 + h z * z ^ 2
  let q : ℂ → ℂ := fun z => 1 - deriv h z * z ^ 3 / 2
  let N : ℂ → ℂ := fun z => a * p z + A z * z ^ 2
  let D : ℂ → ℂ := fun z => b * q z - B z * z ^ 3
  let t := L.weierstrassPoleParameter a b A (fun z => 2 * B z)
  have ha : a ≠ 0 := by
    intro ha
    have : b ^ 2 = 0 := by simpa [ha] using hab.symm
    exact (pow_ne_zero 2 hb) this
  have hh : AnalyticAt ℂ h 0 := L.analyticAt_weierstrassPExcept 0
  have hp : AnalyticAt ℂ p 0 := by fun_prop
  have hq : AnalyticAt ℂ q 0 := by fun_prop
  have hN : AnalyticAt ℂ N 0 := by fun_prop
  have hD : AnalyticAt ℂ D 0 := by fun_prop
  have hp₀ : p 0 = 1 := by simp [p]
  have hq₀ : q 0 = 1 := by simp [q]
  have hN₀ : N 0 = a := by simp [N, hp₀]
  have hD₀ : D 0 = b := by simp [D, hq₀]
  have ht : AnalyticAt ℂ t 0 := L.analyticAt_weierstrassPoleParameter_zero a b A
    (fun z => 2 * B z) hA (by fun_prop) hb
  have ht₀ : t 0 = 0 := by simp [t]
  have htd : HasDerivAt t (a / b) 0 := L.hasDerivAt_weierstrassPoleParameter_zero a b A
    (fun z => 2 * B z) hA (by fun_prop) hb
  have htform : t =ᶠ[𝓝 (0 : ℂ)] (fun z => z * N z / D z) := by
    convert L.weierstrassPoleParameter_eventuallyEq a b A (fun z => 2 * B z) using 1
    ext z
    dsimp [N, D, p, q, h]
    congr 1
    ring
  obtain ⟨v, hv, hv₀, hvd, -, hright⟩ := L.exists_weierstrassParameter_inverse
  let g : ℂ → ℂ := fun z => v (t z)
  have hg : AnalyticAt ℂ g 0 :=
    (show AnalyticAt ℂ v (t 0) by simpa [ht₀] using hv).comp ht
  have hg₀ : g 0 = 0 := by simp [g, ht₀, hv₀]
  have hgd : HasDerivAt g (a / b) 0 := by
    convert! (show HasDerivAt v 1 (t 0) by simpa [ht₀] using hvd).comp 0 htd using 1
    simp
  have hgt : Tendsto g (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa [hg₀] using hg.continuousAt.tendsto
  have hTg : ∀ᶠ z in 𝓝 (0 : ℂ), L.weierstrassParameter (g z) = t z := by
    exact hright.comp_tendsto (by simpa [ht₀] using ht.continuousAt.tendsto)
  let U₁ : ℂ → ℂ := fun z => (p (g z)) ^ 3 / (q (g z)) ^ 2
  let U₂ : ℂ → ℂ := fun z => (N z) ^ 3 / (D z) ^ 2
  have hU₁ : ContinuousAt U₁ 0 := by
    apply ContinuousAt.div
    · exact ((show ContinuousAt p (g 0) by simpa [hg₀] using hp.continuousAt).comp
        hg.continuousAt).pow 3
    · exact ((show ContinuousAt q (g 0) by simpa [hg₀] using hq.continuousAt).comp
        hg.continuousAt).pow 2
    · simp [hg₀, hq₀]
  have hU₂ : ContinuousAt U₂ 0 :=
    (hN.continuousAt.pow 3).div (hD.continuousAt.pow 2) (by simpa [hD₀] using pow_ne_zero 2 hb)
  have hU₁₀ : U₁ 0 = 1 := by simp [U₁, hg₀, hp₀, hq₀]
  have hU₂₀ : U₂ 0 = 1 := by simp [U₂, hN₀, hD₀, hab, hb]
  let C : ℂ → ℂ := fun z => U₁ z + U₂ z - (U₁ z) ^ 2 - U₁ z * U₂ z -
    (U₂ z) ^ 2 - (periodCurve L).a₄ * (t z) ^ 4
  have hC : ContinuousAt C 0 := by fun_prop
  have hC₀ : C 0 = -1 := by simp [C, hU₁₀, hU₂₀, ht₀]
  have hNne : ∀ᶠ z in 𝓝 (0 : ℂ), N z ≠ 0 :=
    hN.continuousAt.eventually_ne (by simpa [hN₀] using ha)
  have hDne : ∀ᶠ z in 𝓝 (0 : ℂ), D z ≠ 0 :=
    hD.continuousAt.eventually_ne (by simpa [hD₀] using hb)
  have hpgne : ∀ᶠ z in 𝓝 (0 : ℂ), p (g z) ≠ 0 :=
    hgt.eventually (hp.continuousAt.eventually_ne (by rw [hp₀]; exact one_ne_zero))
  have hqgne : ∀ᶠ z in 𝓝 (0 : ℂ), q (g z) ≠ 0 :=
    hgt.eventually (hq.continuousAt.eventually_ne (by rw [hq₀]; exact one_ne_zero))
  have hCne : ∀ᶠ z in 𝓝 (0 : ℂ), C z ≠ 0 :=
    hC.eventually_ne (by rw [hC₀]; norm_num)
  have htne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), t z ≠ 0 := by
    filter_upwards [htform.filter_mono nhdsWithin_le_nhds,
      hNne.filter_mono nhdsWithin_le_nhds, hDne.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hNz hDz hz0
    rw [hz]
    exact div_ne_zero (mul_ne_zero hz0 hNz) hDz
  have hgne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z ≠ 0 := by
    filter_upwards [htne, hTg.filter_mono nhdsWithin_le_nhds] with z htz hTgz hgz
    exact htz (by rw [← hTgz, hgz, L.weierstrassParameter_zero])
  have hgp : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hgt.mono_left nhdsWithin_le_nhds, hgne⟩
  have hcoord : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = standardPeriodPoint τ (g z) := by
    filter_upwards [hX, hY, weierstrass_regular_coordinates L,
      hgp.eventually (weierstrass_regular_coordinates L),
      htform.filter_mono nhdsWithin_le_nhds, hTg.filter_mono nhdsWithin_le_nhds,
      hNne.filter_mono nhdsWithin_le_nhds, hDne.filter_mono nhdsWithin_le_nhds,
      hpgne.filter_mono nhdsWithin_le_nhds, hqgne.filter_mono nhdsWithin_le_nhds,
      hCne.filter_mono nhdsWithin_le_nhds, htne, hgne, self_mem_nhdsWithin]
        with z hXz hYz hreg hgreg htz hTgz hNz hDz hpz hqz hCz htnz hgnz hz0
    change z ≠ 0 at hz0
    have hx₂ : periodCurveX τ (F z) = N z / z ^ 2 := by
      rw [hXz, hreg.1]
      dsimp [N, p, h]
      field_simp [hz0]
    have hy₂ : periodCurveY τ (F z) = -D z / z ^ 3 := by
      rw [hYz]
      have he := hreg.2
      change L.derivWeierstrassP z / 2 = -q z / z ^ 3 at he
      rw [show b * L.derivWeierstrassP z / 2 = b * (L.derivWeierstrassP z / 2) by ring, he]
      dsimp [D]
      field_simp [hz0]
      ring
    have hx₂ne : periodCurveX τ (F z) ≠ 0 := by
      rw [hx₂]
      exact div_ne_zero hNz (pow_ne_zero 2 hz0)
    have hTformula : t z = g z * p (g z) / q (g z) := by
      rw [← hTgz]
      dsimp [PeriodPair.weierstrassParameter]
      have he := hgreg.2
      change L.derivWeierstrassP (g z) / 2 = -q (g z) / (g z) ^ 3 at he
      have he' : L.derivWeierstrassP (g z) = -2 * q (g z) / (g z) ^ 3 := by
        linear_combination 2 * he
      rw [hgreg.1, he']
      change -2 * (p (g z) / (g z) ^ 2) / (-2 * q (g z) / (g z) ^ 3) = _
      field_simp [hgnz, hqz]
    have hu₁ : (t z) ^ 2 * periodCurveX τ (standardPeriodPoint τ (g z)) = U₁ z := by
      rw [periodCurveX_standardPeriodPoint, hgreg.1, hTformula]
      change (g z * p (g z) / q (g z)) ^ 2 * (p (g z) / (g z) ^ 2) = _
      dsimp [U₁]
      field_simp [hgnz, hqz]
    have hu₂ : (t z) ^ 2 * periodCurveX τ (F z) = U₂ z := by
      rw [hx₂, htz]
      dsimp [U₂]
      field_simp [hz0, hDz]
    have ht₂ : t z * periodCurveY τ (F z) = -periodCurveX τ (F z) := by
      rw [hx₂, hy₂, htz]
      field_simp [hz0, hDz]
    have ht₁ : t z * periodCurveY τ (standardPeriodPoint τ (g z)) =
        -periodCurveX τ (standardPeriodPoint τ (g z)) := by
      rw [periodCurveX_standardPeriodPoint, periodCurveY_standardPeriodPoint,
        hgreg.1, hgreg.2, hTformula]
      change (g z * p (g z) / q (g z)) * (-q (g z) / (g z) ^ 3) =
        -(p (g z) / (g z) ^ 2)
      field_simp [hgnz, hqz]
    have hx₁ne : periodCurveX τ (standardPeriodPoint τ (g z)) ≠ 0 := by
      rw [periodCurveX_standardPeriodPoint, hgreg.1]
      exact div_ne_zero hpz (pow_ne_zero 2 hgnz)
    have he₁ := periodCurve_equation_of_X_ne_zero τ (standardPeriodPoint τ (g z)) hx₁ne
    have he₂ := periodCurve_equation_of_X_ne_zero τ (F z) hx₂ne
    have hbranch : (t z) ^ 2 * periodCurveX τ (standardPeriodPoint τ (g z)) +
        (t z) ^ 2 * periodCurveX τ (F z) -
        ((t z) ^ 2 * periodCurveX τ (standardPeriodPoint τ (g z))) ^ 2 -
        ((t z) ^ 2 * periodCurveX τ (standardPeriodPoint τ (g z))) *
          ((t z) ^ 2 * periodCurveX τ (F z)) -
        ((t z) ^ 2 * periodCurveX τ (F z)) ^ 2 - (periodCurve L).a₄ * (t z) ^ 4 ≠ 0 := by
      rw [hu₁, hu₂]
      exact hCz
    obtain ⟨hxeq, hyeq⟩ := infinity_branch_coordinates (t z)
      (periodCurveX τ (standardPeriodPoint τ (g z)))
      (periodCurveY τ (standardPeriodPoint τ (g z)))
      (periodCurveX τ (F z)) (periodCurveY τ (F z))
      (periodCurve L).a₄ (periodCurve L).a₆ htnz he₁ he₂ ht₁ ht₂ hbranch
    exact periodCurve_eq_of_coordinates_of_X_ne_zero τ _ _ hx₂ne hxeq.symm hyeq.symm
  refine ⟨g, hg, hg₀, hgd, ?_⟩
  rw [eventually_nhdsWithin_iff] at hcoord
  filter_upwards [hcoord] with z hz
  by_cases hz0 : z = 0
  · subst z
    rw [hF₀, hg₀, standardPeriodPoint_of_mem τ (zero_mem _)]
  · exact hz hz0

end BakerHeegnerStark
