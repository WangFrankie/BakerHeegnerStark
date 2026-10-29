/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Uniformization.Curve
import BakerHeegnerStark.EllipticFunctions.PeriodTorus.Torsion
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Surjectivity
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Fibres
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Addition

/-!
# Actual points of the standard period curve

The actual Weierstrass functions define a point of the nonsingular period
curve away from the lattice. Lattice points are sent to the point at infinity,
not to the totalized zero values of `wp` and `wp'` at their poles.

The resulting map respects every lattice translation and therefore descends
to the actual period quotient `PeriodTorus`. Its zero fibre is exactly the
zero class, it respects negation, and half-periods give actual two-torsion
points of the curve.

The actual Weierstrass function attains every complex value off the lattice.
Matching the derivative coordinate by choosing `z` or `-z` proves surjectivity.
Uniqueness for the second-order differential equation and comparison of
translated poles show that equal affine coordinates differ by a period.
The resulting period-quotient map is bijective, including infinity.

The actual chord formula and group associativity prove compatibility with
the existing affine point addition, including tangent, inverse, and pole
cases. `standardPeriodTorusEquiv` is therefore an additive uniformization.

An algebraic field of definition for the CM endomorphism is not asserted.
-/

namespace BakerHeegnerStark

/-- The actual standard period-pair lattice is the previously specified integer period module. -/
theorem standardPeriodPair_lattice_eq_periodModule (τ : UpperHalfPlane) :
    (standardPeriodPair τ).lattice = periodModule (τ : ℂ) := rfl

/-- Away from the period lattice, the actual Weierstrass coordinates satisfy the actual curve equation. -/
theorem standardPeriodCurve_equation_of_not_mem (τ : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ periodModule (τ : ℂ)) :
    (periodCurve (standardPeriodPair τ)).toAffine.Equation
      ((standardPeriodPair τ).weierstrassP z)
      ((standardPeriodPair τ).derivWeierstrassP z / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simpa only [periodCurve, zero_mul, zero_add, add_zero] using
    periodCurve_equation (standardPeriodPair τ) z hz

/-- The actual Weierstrass point, with lattice poles mapped to the point at infinity. -/
noncomputable def standardPeriodPoint (τ : UpperHalfPlane) (z : ℂ) :
    (periodCurve (standardPeriodPair τ)).toAffine.Point := by
  classical
  exact if hz : z ∈ periodModule (τ : ℂ) then 0 else
    WeierstrassCurve.Affine.Point.mk (standardPeriodCurve_equation_of_not_mem τ z hz)

/-- Every actual lattice point maps to infinity. -/
theorem standardPeriodPoint_of_mem (τ : UpperHalfPlane) {z : ℂ}
    (hz : z ∈ periodModule (τ : ℂ)) : standardPeriodPoint τ z = 0 := by
  classical
  simp only [standardPeriodPoint, dite_eq_left hz]

/-- Off the lattice, the map has the actual `wp,wp'/2` affine coordinates. -/
theorem standardPeriodPoint_of_not_mem (τ : UpperHalfPlane) {z : ℂ}
    (hz : z ∉ periodModule (τ : ℂ)) :
    standardPeriodPoint τ z =
      WeierstrassCurve.Affine.Point.mk (standardPeriodCurve_equation_of_not_mem τ z hz) := by
  classical
  simp only [standardPeriodPoint, dite_eq_right hz]

/-- Only lattice points map to infinity. -/
theorem standardPeriodPoint_eq_zero_iff (τ : UpperHalfPlane) (z : ℂ) :
    standardPeriodPoint τ z = 0 ↔ z ∈ periodModule (τ : ℂ) := by
  classical
  by_cases hz : z ∈ periodModule (τ : ℂ)
  · simp only [standardPeriodPoint_of_mem τ hz, hz]
  · rw [standardPeriodPoint_of_not_mem τ hz]
    constructor
    · intro h
      cases h
    · intro h
      exact (hz h).elim

/-- The actual point-valued map respects every period-lattice translation. -/
theorem standardPeriodPoint_add_coe (τ : UpperHalfPlane) (z : ℂ)
    (l : periodModule (τ : ℂ)) : standardPeriodPoint τ (z + l) = standardPeriodPoint τ z := by
  classical
  by_cases hz : z ∈ periodModule (τ : ℂ)
  · have hz' := (periodModule (τ : ℂ)).add_mem hz l.property
    rw [standardPeriodPoint_of_mem τ hz', standardPeriodPoint_of_mem τ hz]
  · have hz' : z + (l : ℂ) ∉ periodModule (τ : ℂ) := by
      intro h
      exact hz (((periodModule (τ : ℂ)).toAddSubgroup.add_mem_cancel_right l.property).mp h)
    rw [standardPeriodPoint_of_not_mem τ hz', standardPeriodPoint_of_not_mem τ hz]
    simp only [(standardPeriodPair τ).weierstrassP_add_coe z l,
      (standardPeriodPair τ).derivWeierstrassP_add_coe z l]

/-- Representatives of the same actual period class determine the same curve point. -/
theorem standardPeriodPoint_eq_of_sub_mem (τ : UpperHalfPlane) {z w : ℂ}
    (h : z - w ∈ periodModule (τ : ℂ)) : standardPeriodPoint τ z = standardPeriodPoint τ w := by
  simpa only [add_sub_cancel] using standardPeriodPoint_add_coe τ w ⟨z - w, h⟩

/-- The actual point-valued Weierstrass map on the actual period quotient. -/
noncomputable def standardPeriodTorusPoint (τ : UpperHalfPlane) :
    PeriodTorus (τ : ℂ) → (periodCurve (standardPeriodPair τ)).toAffine.Point :=
  Quotient.lift (standardPeriodPoint τ) (by
    intro z w h
    exact standardPeriodPoint_eq_of_sub_mem τ ((Submodule.quotientRel_def _).mp h))

/-- The quotient map retains the actual Weierstrass-point formula on representatives. -/
theorem standardPeriodTorusPoint_mk (τ : UpperHalfPlane) (z : ℂ) :
    standardPeriodTorusPoint τ ((periodModule (τ : ℂ)).mkQ z) = standardPeriodPoint τ z := rfl

/-- The zero fibre of the quotient map is exactly the zero period class. -/
theorem standardPeriodTorusPoint_eq_zero_iff (τ : UpperHalfPlane) (p : PeriodTorus (τ : ℂ)) :
    standardPeriodTorusPoint τ p = 0 ↔ p = 0 := by
  refine Submodule.Quotient.induction_on (periodModule (τ : ℂ)) p fun z => ?_
  change standardPeriodPoint τ z = 0 ↔ (Submodule.Quotient.mk z : PeriodTorus (τ : ℂ)) = 0
  rw [standardPeriodPoint_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

/-- Negating the actual argument negates the actual curve point. -/
theorem standardPeriodPoint_neg (τ : UpperHalfPlane) (z : ℂ) :
    standardPeriodPoint τ (-z) = -standardPeriodPoint τ z := by
  classical
  change standardPeriodPoint τ (-z) = (standardPeriodPoint τ z).neg
  by_cases hz : z ∈ periodModule (τ : ℂ)
  · rw [standardPeriodPoint_of_mem τ ((periodModule (τ : ℂ)).neg_mem hz),
      standardPeriodPoint_of_mem τ hz]
    rfl
  · have hz' : -z ∉ periodModule (τ : ℂ) := by simpa only [neg_mem_iff] using hz
    rw [standardPeriodPoint_of_not_mem τ hz', standardPeriodPoint_of_not_mem τ hz]
    simp [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.neg,
      WeierstrassCurve.Affine.negY, periodCurve,
      PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg]
    ring

/-- The actual quotient map respects negation. -/
theorem standardPeriodTorusPoint_neg (τ : UpperHalfPlane) (p : PeriodTorus (τ : ℂ)) :
    standardPeriodTorusPoint τ (-p) = -standardPeriodTorusPoint τ p := by
  refine Submodule.Quotient.induction_on (periodModule (τ : ℂ)) p fun z => ?_
  exact standardPeriodPoint_neg τ z

/-- A half-period maps to actual algebraic two-torsion. -/
theorem standardPeriodPoint_two_nsmul_eq_zero [DecidableEq ℂ] (τ : UpperHalfPlane) (z : ℂ)
    (hz : (2 : ℂ) * z ∈ periodModule (τ : ℂ)) :
    (2 : ℕ) • standardPeriodPoint τ z = 0 := by
  have h : standardPeriodPoint τ z = standardPeriodPoint τ (-z) := by
    apply standardPeriodPoint_eq_of_sub_mem τ
    simpa only [sub_neg_eq_add, two_mul] using hz
  rw [standardPeriodPoint_neg] at h
  rw [two_smul]
  exact add_eq_zero_iff_eq_neg.mpr h

/-- Every actual affine point has the prescribed Weierstrass coordinates off the period lattice. -/
theorem exists_standardPeriod_weierstrass_coordinates (τ : UpperHalfPlane) (x y : ℂ)
    (h : (periodCurve (standardPeriodPair τ)).toAffine.Equation x y) :
    ∃ z : ℂ, z ∉ periodModule (τ : ℂ) ∧
      (standardPeriodPair τ).weierstrassP z = x ∧
      (standardPeriodPair τ).derivWeierstrassP z / 2 = y := by
  obtain ⟨z, hz, hx⟩ := (standardPeriodPair τ).exists_not_mem_lattice_weierstrassP_eq x
  have hz' : z ∉ periodModule (τ : ℂ) := hz
  have hy := h
  rw [WeierstrassCurve.Affine.equation_iff] at hy
  simp only [periodCurve, zero_mul, add_zero] at hy
  have hw := periodCurve_equation (standardPeriodPair τ) z hz
  rw [hx] at hw
  have hs : ((standardPeriodPair τ).derivWeierstrassP z / 2) ^ 2 = y ^ 2 :=
    hw.trans hy.symm
  have hprod : ((standardPeriodPair τ).derivWeierstrassP z / 2 - y) *
      ((standardPeriodPair τ).derivWeierstrassP z / 2 + y) = 0 := by
    linear_combination hs
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · exact ⟨z, hz', hx, sub_eq_zero.mp hminus⟩
  · refine ⟨-z, ?_, ?_, ?_⟩
    · simpa only [neg_mem_iff] using hz'
    · rw [(standardPeriodPair τ).weierstrassP_neg]
      exact hx
    · have hd := add_eq_zero_iff_eq_neg.mp hplus
      rw [(standardPeriodPair τ).derivWeierstrassP_neg]
      calc
        -(standardPeriodPair τ).derivWeierstrassP z / 2 =
            -((standardPeriodPair τ).derivWeierstrassP z / 2) := by ring
        _ = y := by rw [hd, neg_neg]

/-- The actual point-valued Weierstrass map covers every point of the period curve. -/
theorem standardPeriodPoint_surjective (τ : UpperHalfPlane) :
    Function.Surjective (standardPeriodPoint τ) := by
  intro P
  cases P with
  | zero => exact ⟨0, standardPeriodPoint_of_mem τ (periodModule (τ : ℂ)).zero_mem⟩
  | some x y hp =>
    obtain ⟨z, hz, hx, hy⟩ := exists_standardPeriod_weierstrass_coordinates τ x y hp.1
    refine ⟨z, ?_⟩
    rw [standardPeriodPoint_of_not_mem τ hz]
    simp only [WeierstrassCurve.Affine.Point.mk, hx, hy]

/-- The actual period-quotient map covers every point of the actual period curve. -/
theorem standardPeriodTorusPoint_surjective (τ : UpperHalfPlane) :
    Function.Surjective (standardPeriodTorusPoint τ) := by
  intro P
  obtain ⟨z, hz⟩ := standardPeriodPoint_surjective τ P
  exact ⟨(periodModule (τ : ℂ)).mkQ z, hz⟩

/-- Two actual Weierstrass points coincide exactly when their arguments differ by a period. -/
theorem standardPeriodPoint_eq_iff_sub_mem (τ : UpperHalfPlane) (z w : ℂ) :
    standardPeriodPoint τ z = standardPeriodPoint τ w ↔
      z - w ∈ periodModule (τ : ℂ) := by
  classical
  constructor
  · intro h
    by_cases hz : z ∈ periodModule (τ : ℂ)
    · have hw : w ∈ periodModule (τ : ℂ) :=
        (standardPeriodPoint_eq_zero_iff τ w).mp (h.symm.trans (standardPeriodPoint_of_mem τ hz))
      exact (periodModule (τ : ℂ)).sub_mem hz hw
    · have hw : w ∉ periodModule (τ : ℂ) := by
        intro hw
        exact hz ((standardPeriodPoint_eq_zero_iff τ z).mp
          (h.trans (standardPeriodPoint_of_mem τ hw)))
      rw [standardPeriodPoint_of_not_mem τ hz, standardPeriodPoint_of_not_mem τ hw] at h
      have hxy := WeierstrassCurve.Affine.Point.some.inj h
      apply (standardPeriodPair τ).sub_mem_lattice_of_weierstrassP_deriv_eq z w hz hw hxy.1
      linear_combination 2 * hxy.2
  · exact standardPeriodPoint_eq_of_sub_mem τ

/-- The actual period-quotient map is injective, including its point at infinity. -/
theorem standardPeriodTorusPoint_injective (τ : UpperHalfPlane) :
    Function.Injective (standardPeriodTorusPoint τ) := by
  intro p q
  refine Submodule.Quotient.induction_on (periodModule (τ : ℂ)) p fun z => ?_
  refine Submodule.Quotient.induction_on (periodModule (τ : ℂ)) q fun w => ?_
  intro h
  exact Quotient.sound ((Submodule.quotientRel_def _).mpr
    ((standardPeriodPoint_eq_iff_sub_mem τ z w).mp h))

/-- The actual period quotient and actual nonsingular period-curve points are in bijection. -/
theorem standardPeriodTorusPoint_bijective (τ : UpperHalfPlane) :
    Function.Bijective (standardPeriodTorusPoint τ) :=
  ⟨standardPeriodTorusPoint_injective τ, standardPeriodTorusPoint_surjective τ⟩

/-- Actual curve addition agrees with argument addition at unequal x-coordinates. -/
theorem standardPeriodPoint_add_of_weierstrassP_ne [DecidableEq ℂ]
    (τ : UpperHalfPlane) (z u : ℂ)
    (hz : z ∉ periodModule (τ : ℂ)) (hu : u ∉ periodModule (τ : ℂ))
    (hxu : (standardPeriodPair τ).weierstrassP u ≠ (standardPeriodPair τ).weierstrassP z) :
    standardPeriodPoint τ (z + u) = standardPeriodPoint τ z + standardPeriodPoint τ u := by
  let L := standardPeriodPair τ
  have hzu : z + u ∉ periodModule (τ : ℂ) := by
    intro h
    apply hxu
    apply (L.weierstrassP_eq_iff_sub_mem_or_add_mem_lattice u z hu hz).mpr
    right
    simpa only [L, standardPeriodPair_lattice_eq_periodModule, add_comm] using h
  have hne : L.weierstrassP u - L.weierstrassP z ≠ 0 := sub_ne_zero.mpr hxu
  have hslope : (periodCurve L).toAffine.slope
      (L.weierstrassP u) (L.weierstrassP z)
      (L.derivWeierstrassP u / 2) (L.derivWeierstrassP z / 2) =
      (L.derivWeierstrassP u - L.derivWeierstrassP z) /
        (2 * (L.weierstrassP u - L.weierstrassP z)) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxu]
    field_simp [hne]
    rfl
  have hx : L.weierstrassP (z + u) = (periodCurve L).toAffine.addX
      (L.weierstrassP u) (L.weierstrassP z)
      ((periodCurve L).toAffine.slope (L.weierstrassP u) (L.weierstrassP z)
        (L.derivWeierstrassP u / 2) (L.derivWeierstrassP z / 2)) := by
    rw [hslope]
    simpa only [WeierstrassCurve.Affine.addX, periodCurve, zero_mul, add_zero, sub_zero]
      using L.weierstrassP_add z u hz hu hxu
  have hy : L.derivWeierstrassP (z + u) / 2 = (periodCurve L).toAffine.addY
      (L.weierstrassP u) (L.weierstrassP z) (L.derivWeierstrassP u / 2)
      ((periodCurve L).toAffine.slope (L.weierstrassP u) (L.weierstrassP z)
        (L.derivWeierstrassP u / 2) (L.derivWeierstrassP z / 2)) := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, ← hx, hslope,
      L.derivWeierstrassP_add z u hz hu hxu]
    simp only [periodCurve, zero_mul, sub_zero]
    field_simp [hne]
    ring
  rw [add_comm (standardPeriodPoint τ z) (standardPeriodPoint τ u),
    standardPeriodPoint_of_not_mem τ hzu, standardPeriodPoint_of_not_mem τ hu,
    standardPeriodPoint_of_not_mem τ hz]
  simp only [WeierstrassCurve.Affine.Point.mk]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxu]
  simpa only [WeierstrassCurve.Affine.Point.some.injEq] using And.intro hx hy

private theorem exists_standardPeriod_addition_auxiliary (τ : UpperHalfPlane) (z : ℂ) :
    ∃ u : ℂ, u ∉ periodModule (τ : ℂ) ∧ z + u ∉ periodModule (τ : ℂ) ∧
      z - u ∉ periodModule (τ : ℂ) ∧ 2 * u ∉ periodModule (τ : ℂ) := by
  have hcL : ((standardPeriodPair τ).lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := (standardPeriodPair τ).lattice)
  have hc : (periodModule (τ : ℂ) : Set ℂ).Countable := by
    simpa only [standardPeriodPair_lattice_eq_periodModule] using hcL
  have hc₁ : ((fun u : ℂ => z + u) ⁻¹' (periodModule (τ : ℂ) : Set ℂ)).Countable :=
    hc.preimage (by intro a b h; exact add_left_cancel h)
  have hc₂ : ((fun u : ℂ => -z + u) ⁻¹' (periodModule (τ : ℂ) : Set ℂ)).Countable :=
    hc.preimage (by intro a b h; exact add_left_cancel h)
  have hc₃ : ((fun u : ℂ => 2 * u) ⁻¹' (periodModule (τ : ℂ) : Set ℂ)).Countable :=
    hc.preimage (by intro a b h; linear_combination (1 / 2 : ℂ) * h)
  let B : Set ℂ := (periodModule (τ : ℂ) : Set ℂ) ∪
    ((fun u : ℂ => z + u) ⁻¹' (periodModule (τ : ℂ) : Set ℂ)) ∪
    ((fun u : ℂ => -z + u) ⁻¹' (periodModule (τ : ℂ) : Set ℂ)) ∪
    ((fun u : ℂ => 2 * u) ⁻¹' (periodModule (τ : ℂ) : Set ℂ))
  have hcB : B.Countable := ((hc.union hc₁).union hc₂).union hc₃
  obtain ⟨u, hu⟩ := (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hcB).nonempty
  have hs : u ∉ periodModule (τ : ℂ) ∧ z + u ∉ periodModule (τ : ℂ) ∧
      -z + u ∉ periodModule (τ : ℂ) ∧ 2 * u ∉ periodModule (τ : ℂ) := by
    simpa only [B, Set.mem_compl_iff, Set.mem_union, Set.mem_preimage, SetLike.mem_coe,
      not_or, and_assoc] using hu
  refine ⟨u, hs.1, hs.2.1, ?_, hs.2.2.2⟩
  intro hm
  apply hs.2.2.1
  convert (periodModule (τ : ℂ)).neg_mem hm using 1; ring

/-- Doubling agrees with the existing curve group law, also at half-periods. -/
theorem standardPeriodPoint_add_self [DecidableEq ℂ] (τ : UpperHalfPlane) (z : ℂ) :
    standardPeriodPoint τ (z + z) = standardPeriodPoint τ z + standardPeriodPoint τ z := by
  by_cases hz : z ∈ periodModule (τ : ℂ)
  · rw [standardPeriodPoint_of_mem τ ((periodModule (τ : ℂ)).add_mem hz hz),
      standardPeriodPoint_of_mem τ hz, zero_add]
  by_cases h₂ : (2 : ℂ) * z ∈ periodModule (τ : ℂ)
  · have hs : z + z ∈ periodModule (τ : ℂ) := by simpa only [two_mul] using h₂
    rw [standardPeriodPoint_of_mem τ hs]
    simpa only [two_smul] using (standardPeriodPoint_two_nsmul_eq_zero τ z h₂).symm
  obtain ⟨u, hu, hzu, hzmu, h₂u⟩ := exists_standardPeriod_addition_auxiliary τ z
  have hxu : (standardPeriodPair τ).weierstrassP u ≠
      (standardPeriodPair τ).weierstrassP z := by
    intro h
    have hcoords := ((standardPeriodPair τ).weierstrassP_eq_iff_sub_mem_or_add_mem_lattice
      u z hu hz).mp h
    simp only [standardPeriodPair_lattice_eq_periodModule] at hcoords
    rcases hcoords with hm | hp
    · apply hzmu
      convert (periodModule (τ : ℂ)).neg_mem hm using 1; ring
    · apply hzu
      convert hp using 1; ring
  have hxpm : (standardPeriodPair τ).weierstrassP (z - u) ≠
      (standardPeriodPair τ).weierstrassP (z + u) := by
    intro h
    have hcoords := ((standardPeriodPair τ).weierstrassP_eq_iff_sub_mem_or_add_mem_lattice
      (z - u) (z + u) hzmu hzu).mp h
    simp only [standardPeriodPair_lattice_eq_periodModule] at hcoords
    rcases hcoords with hm | hp
    · apply h₂u
      convert (periodModule (τ : ℂ)).neg_mem hm using 1; ring
    · apply h₂
      convert hp using 1; ring
  have hnu : -u ∉ periodModule (τ : ℂ) := by simpa only [neg_mem_iff] using hu
  have hxnu : (standardPeriodPair τ).weierstrassP (-u) ≠
      (standardPeriodPair τ).weierstrassP z := by
    rw [(standardPeriodPair τ).weierstrassP_neg]
    exact hxu
  calc
    standardPeriodPoint τ (z + z) = standardPeriodPoint τ ((z + u) + (z - u)) := by
      congr 1
      ring
    _ = standardPeriodPoint τ (z + u) + standardPeriodPoint τ (z - u) :=
      standardPeriodPoint_add_of_weierstrassP_ne τ (z + u) (z - u) hzu hzmu hxpm
    _ = (standardPeriodPoint τ z + standardPeriodPoint τ u) +
        (standardPeriodPoint τ z + standardPeriodPoint τ (-u)) := by
      rw [standardPeriodPoint_add_of_weierstrassP_ne τ z u hz hu hxu,
        sub_eq_add_neg, standardPeriodPoint_add_of_weierstrassP_ne τ z (-u) hz hnu hxnu]
    _ = standardPeriodPoint τ z + standardPeriodPoint τ z := by
      rw [standardPeriodPoint_neg]
      abel

/-- The actual Weierstrass point map preserves the existing affine point addition in every case. -/
theorem standardPeriodPoint_add [DecidableEq ℂ] (τ : UpperHalfPlane) (z u : ℂ) :
    standardPeriodPoint τ (z + u) = standardPeriodPoint τ z + standardPeriodPoint τ u := by
  by_cases hz : z ∈ periodModule (τ : ℂ)
  · rw [standardPeriodPoint_of_mem τ hz, zero_add]
    simpa only [add_comm] using standardPeriodPoint_add_coe τ u ⟨z, hz⟩
  by_cases hu : u ∈ periodModule (τ : ℂ)
  · rw [standardPeriodPoint_of_mem τ hu, add_zero]
    exact standardPeriodPoint_add_coe τ z ⟨u, hu⟩
  by_cases hx : (standardPeriodPair τ).weierstrassP u = (standardPeriodPair τ).weierstrassP z
  · have hcoords := ((standardPeriodPair τ).weierstrassP_eq_iff_sub_mem_or_add_mem_lattice
      u z hu hz).mp hx
    simp only [standardPeriodPair_lattice_eq_periodModule] at hcoords
    rcases hcoords with hm | hp
    · have hpoint : standardPeriodPoint τ u = standardPeriodPoint τ z :=
        standardPeriodPoint_eq_of_sub_mem τ hm
      have hsum : (z + u) - (z + z) ∈ periodModule (τ : ℂ) := by
        convert hm using 1; ring
      rw [standardPeriodPoint_eq_of_sub_mem τ hsum, standardPeriodPoint_add_self, hpoint]
    · have hsum : z + u ∈ periodModule (τ : ℂ) := by
        convert hp using 1; ring
      have hdiff : u - -z ∈ periodModule (τ : ℂ) := by
        simpa only [sub_neg_eq_add] using hp
      rw [standardPeriodPoint_of_mem τ hsum, standardPeriodPoint_eq_of_sub_mem τ hdiff,
        standardPeriodPoint_neg, add_neg_cancel]
  · exact standardPeriodPoint_add_of_weierstrassP_ne τ z u hz hu hx

/-- Addition on the actual period quotient agrees with the actual curve group law. -/
theorem standardPeriodTorusPoint_add [DecidableEq ℂ] (τ : UpperHalfPlane)
    (p q : PeriodTorus (τ : ℂ)) :
    standardPeriodTorusPoint τ (p + q) =
      standardPeriodTorusPoint τ p + standardPeriodTorusPoint τ q := by
  refine Submodule.Quotient.induction_on (periodModule (τ : ℂ)) p fun z => ?_
  refine Submodule.Quotient.induction_on (periodModule (τ : ℂ)) q fun u => ?_
  exact standardPeriodPoint_add τ z u

/-- The actual Weierstrass point map as an additive homomorphism. -/
noncomputable def standardPeriodTorusPointHom [DecidableEq ℂ] (τ : UpperHalfPlane) :
    PeriodTorus (τ : ℂ) →+ (periodCurve (standardPeriodPair τ)).toAffine.Point where
  toFun := standardPeriodTorusPoint τ
  map_zero' := (standardPeriodTorusPoint_eq_zero_iff τ 0).mpr rfl
  map_add' := standardPeriodTorusPoint_add τ

/-- Uniformization of the actual period curve by the specified actual period quotient. -/
noncomputable def standardPeriodTorusEquiv [DecidableEq ℂ] (τ : UpperHalfPlane) :
    PeriodTorus (τ : ℂ) ≃+ (periodCurve (standardPeriodPair τ)).toAffine.Point :=
  AddEquiv.ofBijective (standardPeriodTorusPointHom τ) (standardPeriodTorusPoint_bijective τ)

@[simp]
theorem standardPeriodTorusEquiv_apply [DecidableEq ℂ] (τ : UpperHalfPlane)
    (p : PeriodTorus (τ : ℂ)) : standardPeriodTorusEquiv τ p = standardPeriodTorusPoint τ p := rfl

end BakerHeegnerStark
