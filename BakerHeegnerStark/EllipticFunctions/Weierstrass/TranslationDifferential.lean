/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Weierstrass.Translation
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Differential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Differential equations for rational Weierstrass translation

Away from the lattice and from equal x-coordinates, the rational chord expressions
are analytic and satisfy `X' = Y` and `Y' = 6 * X² - g₂ / 2` in the derivative-scale
y-coordinate convention. The algebra uses the actual cubic equations at both
endpoints, together with the actual second derivative of the Weierstrass function.

The filled-in values at lattice poles are not used for differentiation: all local
identifications with the rational formulas take place on the open lattice complement.
-/

open Filter
open scoped Topology

namespace PeriodPair

/-- Differentiating the chord slope uses both endpoint cubic equations. -/
private theorem translateSlope_derivative (a b X Y g₂ g₃ : ℂ)
    (ha : b ^ 2 = 4 * a ^ 3 - g₂ * a - g₃)
    (hX : Y ^ 2 = 4 * X ^ 3 - g₂ * X - g₃)
    (hne : X - a ≠ 0) :
    ((6 * X ^ 2 - g₂ / 2) * (2 * (X - a)) - (Y - b) * (2 * Y)) /
      (2 * (X - a)) ^ 2 =
        X - (((Y - b) / (2 * (X - a))) ^ 2 - X - a) := by
  field_simp
  linear_combination ha - hX

/-- The difference of the endpoint cubics is the slope identity needed for the y-derivative. -/
private theorem translateSlope_cubic (a b X Y g₂ g₃ : ℂ)
    (ha : b ^ 2 = 4 * a ^ 3 - g₂ * a - g₃)
    (hX : Y ^ 2 = 4 * X ^ 3 - g₂ * X - g₃)
    (hne : X - a ≠ 0) :
    4 * ((Y - b) / (2 * (X - a))) * Y -
      4 * ((Y - b) / (2 * (X - a))) ^ 2 * (X - a) =
        4 * (X ^ 2 + X * a + a ^ 2) - g₂ := by
  field_simp
  linear_combination 4 * hX - 4 * ha

private theorem translateY_derivative (a b X Y g₂ g₃ : ℂ)
    (ha : b ^ 2 = 4 * a ^ 3 - g₂ * a - g₃)
    (hX : Y ^ 2 = 4 * X ^ 3 - g₂ * X - g₃)
    (hne : X - a ≠ 0) :
    let s := (Y - b) / (2 * (X - a));
    let r := s ^ 2 - X - a;
    -(6 * X ^ 2 - g₂ / 2) + 2 * (X - r) ^ 2 +
      2 * s * (Y - (-Y + 2 * s * (X - r))) = 6 * r ^ 2 - g₂ / 2 := by
  dsimp only
  linear_combination translateSlope_cubic a b X Y g₂ g₃ ha hX hne

private theorem div_eq_twice_half_div (n d : ℂ) : n / d = 2 * (n / (2 * d)) := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem eventually_weierstrassTranslateX_eq (L : PeriodPair) (z : ℂ) {u : ℂ}
    (hu : u ∉ L.lattice) :
    L.weierstrassTranslateX z =ᶠ[𝓝 u]
      (fun w => ((L.derivWeierstrassP w - L.derivWeierstrassP z) /
        (2 * (L.weierstrassP w - L.weierstrassP z))) ^ 2 -
          L.weierstrassP w - L.weierstrassP z) := by
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hu] with w hw
  change w ∉ L.lattice at hw
  simp only [weierstrassTranslateX, ite_eq_right hw]

private theorem eventually_weierstrassTranslateY_eq (L : PeriodPair) (z : ℂ) {u : ℂ}
    (hu : u ∉ L.lattice) :
    L.weierstrassTranslateY z =ᶠ[𝓝 u]
      (fun w => -L.derivWeierstrassP w +
        (L.derivWeierstrassP w - L.derivWeierstrassP z) /
          (L.weierstrassP w - L.weierstrassP z) *
            (L.weierstrassP w - L.weierstrassTranslateX z w)) := by
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hu] with w hw
  change w ∉ L.lattice at hw
  simp only [weierstrassTranslateY, ite_eq_right hw]

/-- The rational translation x-coordinate is analytic away from its denominator and the lattice. -/
theorem analyticAt_weierstrassTranslateX_of_not_mem (L : PeriodPair) (z : ℂ) {u : ℂ}
    (hu : u ∉ L.lattice) (hxu : L.weierstrassP u ≠ L.weierstrassP z) :
    AnalyticAt ℂ (L.weierstrassTranslateX z) u := by
  have hx := L.analyticOnNhd_weierstrassP u hu
  have hy := L.analyticOnNhd_derivWeierstrassP u hu
  have hden : 2 * (L.weierstrassP u - L.weierstrassP z) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hxu)
  exact (((((hy.sub analyticAt_const).div
    (analyticAt_const.mul (hx.sub analyticAt_const)) hden).pow 2).sub hx).sub
      analyticAt_const).congr (eventually_weierstrassTranslateX_eq L z hu).symm

/-- The rational derivative-scale y-coordinate is analytic under the same local conditions. -/
theorem analyticAt_weierstrassTranslateY_of_not_mem (L : PeriodPair) (z : ℂ) {u : ℂ}
    (hu : u ∉ L.lattice) (hxu : L.weierstrassP u ≠ L.weierstrassP z) :
    AnalyticAt ℂ (L.weierstrassTranslateY z) u := by
  have hx := L.analyticOnNhd_weierstrassP u hu
  have hy := L.analyticOnNhd_derivWeierstrassP u hu
  exact (hy.neg.add (((hy.sub analyticAt_const).div (hx.sub analyticAt_const)
    (sub_ne_zero.mpr hxu)).mul
      (hx.sub (L.analyticAt_weierstrassTranslateX_of_not_mem z hu hxu)))).congr
        (eventually_weierstrassTranslateY_eq L z hu).symm

private theorem hasDerivAt_translateSlope (L : PeriodPair) (z : ℂ) {u : ℂ}
    (hz : z ∉ L.lattice) (hu : u ∉ L.lattice)
    (hxu : L.weierstrassP u ≠ L.weierstrassP z) :
    HasDerivAt (fun w => (L.derivWeierstrassP w - L.derivWeierstrassP z) /
      (2 * (L.weierstrassP w - L.weierstrassP z)))
      (L.weierstrassP u - L.weierstrassTranslateX z u) u := by
  have hx : HasDerivAt L.weierstrassP (L.derivWeierstrassP u) u := by
    simpa only [L.deriv_weierstrassP] using
      (L.analyticOnNhd_weierstrassP u hu).differentiableAt.hasDerivAt
  have hy : HasDerivAt L.derivWeierstrassP
      (6 * L.weierstrassP u ^ 2 - L.g₂ / 2) u := by
    simpa only [L.deriv_derivWeierstrassP u hu] using
      (L.analyticOnNhd_derivWeierstrassP u hu).differentiableAt.hasDerivAt
  have hden : 2 * (L.weierstrassP u - L.weierstrassP z) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hxu)
  convert (hy.sub_const (L.derivWeierstrassP z)).div
    ((hx.sub_const (L.weierstrassP z)).const_mul 2) hden using 1
  simp only [weierstrassTranslateX, ite_eq_right hu]
  exact (translateSlope_derivative _ _ _ _ _ _
    (L.derivWeierstrassP_sq z hz) (L.derivWeierstrassP_sq u hu)
      (sub_ne_zero.mpr hxu)).symm

/-- The rational x-coordinate has the derivative-scale y-coordinate as derivative. -/
theorem hasDerivAt_weierstrassTranslateX_of_not_mem (L : PeriodPair) (z : ℂ) {u : ℂ}
    (hz : z ∉ L.lattice) (hu : u ∉ L.lattice)
    (hxu : L.weierstrassP u ≠ L.weierstrassP z) :
    HasDerivAt (L.weierstrassTranslateX z) (L.weierstrassTranslateY z u) u := by
  have hx : HasDerivAt L.weierstrassP (L.derivWeierstrassP u) u := by
    simpa only [L.deriv_weierstrassP] using
      (L.analyticOnNhd_weierstrassP u hu).differentiableAt.hasDerivAt
  have hs := hasDerivAt_translateSlope L z hz hu hxu
  have hne := sub_ne_zero.mpr hxu
  have hr : HasDerivAt
      (fun w => ((L.derivWeierstrassP w - L.derivWeierstrassP z) /
        (2 * (L.weierstrassP w - L.weierstrassP z))) ^ 2 -
          L.weierstrassP w - L.weierstrassP z)
      (L.weierstrassTranslateY z u) u := by
    convert ((hs.pow 2).sub hx).sub_const (L.weierstrassP z) using 1
    simp only [weierstrassTranslateY, ite_eq_right hu]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hne]
    ring
  exact hr.congr_of_eventuallyEq (eventually_weierstrassTranslateX_eq L z hu)

/-- The rational y-coordinate satisfies the same actual second-order Weierstrass equation. -/
theorem hasDerivAt_weierstrassTranslateY_of_not_mem (L : PeriodPair) (z : ℂ) {u : ℂ}
    (hz : z ∉ L.lattice) (hu : u ∉ L.lattice)
    (hxu : L.weierstrassP u ≠ L.weierstrassP z) :
    HasDerivAt (L.weierstrassTranslateY z)
      (6 * (L.weierstrassTranslateX z u) ^ 2 - L.g₂ / 2) u := by
  have hx : HasDerivAt L.weierstrassP (L.derivWeierstrassP u) u := by
    simpa only [L.deriv_weierstrassP] using
      (L.analyticOnNhd_weierstrassP u hu).differentiableAt.hasDerivAt
  have hy : HasDerivAt L.derivWeierstrassP
      (6 * L.weierstrassP u ^ 2 - L.g₂ / 2) u := by
    simpa only [L.deriv_derivWeierstrassP u hu] using
      (L.analyticOnNhd_derivWeierstrassP u hu).differentiableAt.hasDerivAt
  have hs := hasDerivAt_translateSlope L z hz hu hxu
  have hr := L.hasDerivAt_weierstrassTranslateX_of_not_mem z hz hu hxu
  have hv : HasDerivAt
      (fun w => -L.derivWeierstrassP w +
        2 * ((L.derivWeierstrassP w - L.derivWeierstrassP z) /
          (2 * (L.weierstrassP w - L.weierstrassP z))) *
            (L.weierstrassP w - L.weierstrassTranslateX z w))
      (-(6 * L.weierstrassP u ^ 2 - L.g₂ / 2) +
        2 * (L.weierstrassP u - L.weierstrassTranslateX z u) ^ 2 +
        2 * ((L.derivWeierstrassP u - L.derivWeierstrassP z) /
          (2 * (L.weierstrassP u - L.weierstrassP z))) *
            (L.derivWeierstrassP u - L.weierstrassTranslateY z u)) u := by
    convert hy.neg.add ((hs.const_mul 2).mul (hx.sub hr)) using 1
    simp only [Pi.sub_apply]
    ring
  have hvalue : L.weierstrassTranslateY z u = -L.derivWeierstrassP u +
      2 * ((L.derivWeierstrassP u - L.derivWeierstrassP z) /
        (2 * (L.weierstrassP u - L.weierstrassP z))) *
          (L.weierstrassP u - L.weierstrassTranslateX z u) := by
    rw [weierstrassTranslateY, ite_eq_right hu,
      div_eq_twice_half_div (L.derivWeierstrassP u - L.derivWeierstrassP z)
        (L.weierstrassP u - L.weierstrassP z)]
  have halg := translateY_derivative _ _ _ _ _ _
    (L.derivWeierstrassP_sq z hz) (L.derivWeierstrassP_sq u hu)
      (sub_ne_zero.mpr hxu)
  dsimp only at halg
  have hderiv : -(6 * L.weierstrassP u ^ 2 - L.g₂ / 2) +
        2 * (L.weierstrassP u - L.weierstrassTranslateX z u) ^ 2 +
        2 * ((L.derivWeierstrassP u - L.derivWeierstrassP z) /
          (2 * (L.weierstrassP u - L.weierstrassP z))) *
            (L.derivWeierstrassP u - L.weierstrassTranslateY z u) =
      6 * (L.weierstrassTranslateX z u) ^ 2 - L.g₂ / 2 := by
    rw [hvalue]
    simpa only [weierstrassTranslateX, ite_eq_right hu] using halg
  rw [hderiv] at hv
  apply hv.congr_of_eventuallyEq
  filter_upwards [eventually_weierstrassTranslateY_eq L z hu] with w hw
  rw [hw, div_eq_twice_half_div (L.derivWeierstrassP w - L.derivWeierstrassP z)
    (L.weierstrassP w - L.weierstrassP z)]

end PeriodPair
