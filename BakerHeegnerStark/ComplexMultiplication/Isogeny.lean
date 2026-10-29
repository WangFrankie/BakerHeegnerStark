/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.DivisionLattice
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Isogeny

/-!
# Finite coordinate formulas for quadratic-period CM

The divided-period lattice is the actual inverse-period homothety of the
original lattice when `τ² = -m`. Combining that equality with the proved
finite-coset formula gives the finite kernel sums for the coordinates of
multiplication by `τ`, with factors `τ⁻²` and `τ⁻³`.

The resulting finite coordinates give the actual period-curve CM point
away from its kernel. The kernel branch is precisely the finer lattice
and maps to infinity, not to the totalized affine coordinates `(0,0)`.
No arithmetic field of definition or Galois compatibility is assumed or
asserted by these analytic coordinate identities.
-/

namespace BakerHeegnerStark

/-- The actual finite-coset formula for the specified divided-period lattice, including poles. -/
theorem weierstrassP_dividedPeriod (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) (z : ℂ) :
    (standardPeriodPair (dividedPeriod τ N hN)).weierstrassP z =
      (∑ t ∈ divisionPeriodRepresentatives τ N, (standardPeriodPair τ).weierstrassP (z - t)) -
        ∑ t ∈ divisionPeriodRepresentatives τ N, (standardPeriodPair τ).weierstrassP t :=
  PeriodPair.weierstrassP_finite_coset_sum (standardPeriodPair τ)
    (standardPeriodPair (dividedPeriod τ N hN)) (divisionPeriodRepresentatives τ N)
    (periodModule_le_divided τ N hN)
    (fun _ ht => divisionPeriodRepresentatives_mem _ _ ht)
    (fun _ hs _ ht hst => divisionPeriodRepresentatives_separated τ N hN hs ht hst)
    (fun _ ha => divisionPeriodRepresentatives_cover τ N hN ha) z

/-- The derivative formula on the specified finer lattice, including its totalized poles. -/
theorem derivWeierstrassP_dividedPeriod (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N)
    (z : ℂ) :
    (standardPeriodPair (dividedPeriod τ N hN)).derivWeierstrassP z =
      ∑ t ∈ divisionPeriodRepresentatives τ N, (standardPeriodPair τ).derivWeierstrassP (z - t) :=
  PeriodPair.derivWeierstrassP_finite_coset_sum (standardPeriodPair τ)
    (standardPeriodPair (dividedPeriod τ N hN)) (divisionPeriodRepresentatives τ N)
    (periodModule_le_divided τ N hN)
    (fun _ ht => divisionPeriodRepresentatives_mem _ _ ht)
    (fun _ hs _ ht hst => divisionPeriodRepresentatives_separated τ N hN hs ht hst)
    (fun _ ha => divisionPeriodRepresentatives_cover τ N hN ha) z

/-- The quadratic relation identifies the finer lattice with the inverse-period homothety. -/
private theorem weierstrassP_quadraticPeriod_homothety
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (z : ℂ) :
    (standardPeriodPair (dividedPeriod τ m hm)).weierstrassP z =
      (τ : ℂ) ^ 2 * (standardPeriodPair τ).weierstrassP ((τ : ℂ) * z) := by
  have hτ0 : (τ : ℂ) ≠ 0 := by
    intro h
    exact (ne_of_gt τ.im_pos) (by simpa using congrArg Complex.im h)
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  have hinv : (τ : ℂ)⁻¹ = -(τ : ℂ) / (m : ℂ) := by
    field_simp [hτ0, hmC]
    linear_combination hτ
  let c : ℂˣ := Units.mk0 (τ : ℂ)⁻¹ (inv_ne_zero hτ0)
  have hlat : (scalePeriodPair (standardPeriodPair τ) c).lattice =
      (standardPeriodPair (dividedPeriod τ m hm)).lattice := by
    ext w
    rw [PeriodPair.mem_lattice, PeriodPair.mem_lattice]
    change (∃ a b : ℤ, (a : ℂ) * ((τ : ℂ)⁻¹ * 1) +
      (b : ℂ) * ((τ : ℂ)⁻¹ * (τ : ℂ)) = w) ↔
      ∃ a b : ℤ, (a : ℂ) * 1 + (b : ℂ) * ((τ : ℂ) / (m : ℂ)) = w
    simp only [mul_one, inv_mul_cancel₀ hτ0]
    constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨b, -a, ?_⟩
      push_cast
      rw [hinv] at hab
      linear_combination hab
    · rintro ⟨a, b, hab⟩
      refine ⟨-b, a, ?_⟩
      push_cast
      rw [hinv]
      linear_combination hab
  have hw := (weierstrassP_eq_iff_lattice_eq _ _).mpr hlat
  have h := scalePeriodPair_weierstrassP (standardPeriodPair τ) c ((τ : ℂ) * z)
  rw [hw] at h
  simpa [c, mul_assoc, hτ0] using h

/-- The quadratic-period CM x-coordinate is the actual finite kernel sum with scale `τ⁻²`. -/
theorem weierstrassP_CM_finite_sum
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (z : ℂ) :
    (standardPeriodPair τ).weierstrassP ((τ : ℂ) * z) = ((τ : ℂ) ^ 2)⁻¹ *
      ((∑ t ∈ divisionPeriodRepresentatives τ m, (standardPeriodPair τ).weierstrassP (z - t)) -
        ∑ t ∈ divisionPeriodRepresentatives τ m, (standardPeriodPair τ).weierstrassP t) := by
  have hτ0 : (τ : ℂ) ≠ 0 := by
    intro h
    exact (ne_of_gt τ.im_pos) (by simpa using congrArg Complex.im h)
  rw [← weierstrassP_dividedPeriod τ m hm z, weierstrassP_quadraticPeriod_homothety τ m hm hτ z]
  simp [hτ0]


/-- At every totalized argument, the actual derivative coordinate has finite-sum scale `τ⁻³`. -/
theorem derivWeierstrassP_CM_finite_sum
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (z : ℂ) :
    (standardPeriodPair τ).derivWeierstrassP ((τ : ℂ) * z) = ((τ : ℂ) ^ 3)⁻¹ *
      ∑ t ∈ divisionPeriodRepresentatives τ m, (standardPeriodPair τ).derivWeierstrassP (z - t) := by
  by_cases hz : (τ : ℂ) * z ∈ (standardPeriodPair τ).lattice
  · have hzM : z ∈ (standardPeriodPair (dividedPeriod τ m hm)).lattice := by
      rw [standardPeriodPair_lattice_eq_periodModule, coe_dividedPeriod]
      exact (mul_mem_periodModule_iff_mem_divided τ m hm hτ z).mp hz
    rw [← derivWeierstrassP_dividedPeriod τ m hm z,
      (standardPeriodPair τ).derivWeierstrassP_coe ⟨(τ : ℂ) * z, hz⟩,
      (standardPeriodPair (dividedPeriod τ m hm)).derivWeierstrassP_coe ⟨z, hzM⟩]
    simp
  · have hτ0 : (τ : ℂ) ≠ 0 := by
      intro h
      exact (ne_of_gt τ.im_pos) (by simpa using congrArg Complex.im h)
    have hd := ((standardPeriodPair τ).analyticOnNhd_weierstrassP _ hz).differentiableAt.hasDerivAt
    rw [PeriodPair.deriv_weierstrassP] at hd
    have hdR : HasDerivAt
        (fun w : ℂ => (τ : ℂ) ^ 2 * (standardPeriodPair τ).weierstrassP ((τ : ℂ) * w))
        ((τ : ℂ) ^ 3 * (standardPeriodPair τ).derivWeierstrassP ((τ : ℂ) * z)) z := by
      convert! (hd.comp z ((hasDerivAt_id z).const_mul (τ : ℂ))).const_mul ((τ : ℂ) ^ 2)
        using 1; ring
    have heq : (standardPeriodPair (dividedPeriod τ m hm)).weierstrassP =
        (fun w : ℂ => (τ : ℂ) ^ 2 * (standardPeriodPair τ).weierstrassP ((τ : ℂ) * w)) :=
      funext (weierstrassP_quadraticPeriod_homothety τ m hm hτ)
    rw [← heq] at hdR
    have hscale : (standardPeriodPair (dividedPeriod τ m hm)).derivWeierstrassP z =
        (τ : ℂ) ^ 3 * (standardPeriodPair τ).derivWeierstrassP ((τ : ℂ) * z) := by
      simpa only [PeriodPair.deriv_weierstrassP] using hdR.deriv
    rw [← derivWeierstrassP_dividedPeriod τ m hm z, hscale]
    simp [hτ0]

/-- The finite kernel x-expression; at kernel arguments it is not an affine point coordinate. -/
noncomputable def cmIsogenyX (τ : UpperHalfPlane) (m : ℕ) (z : ℂ) : ℂ :=
  ((τ : ℂ) ^ 2)⁻¹ *
    ((∑ t ∈ divisionPeriodRepresentatives τ m, (standardPeriodPair τ).weierstrassP (z - t)) -
      ∑ t ∈ divisionPeriodRepresentatives τ m, (standardPeriodPair τ).weierstrassP t)

/-- The finite kernel y-expression in the actual `wp'/2` normalization. -/
noncomputable def cmIsogenyY (τ : UpperHalfPlane) (m : ℕ) (z : ℂ) : ℂ :=
  (((τ : ℂ) ^ 3)⁻¹ *
    ∑ t ∈ divisionPeriodRepresentatives τ m, (standardPeriodPair τ).derivWeierstrassP (z - t)) / 2

/-- Away from the kernel, the finite expressions satisfy the actual nonsingular curve equation. -/
theorem cmIsogeny_equation
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (z : ℂ) (hz : (τ : ℂ) * z ∉ (standardPeriodPair τ).lattice) :
    (periodCurve (standardPeriodPair τ)).toAffine.Equation (cmIsogenyX τ m z) (cmIsogenyY τ m z) := by
  have h := standardPeriodCurve_equation_of_not_mem τ ((τ : ℂ) * z)
    (by simpa only [standardPeriodPair_lattice_eq_periodModule] using hz)
  simpa only [cmIsogenyX, cmIsogenyY, weierstrassP_CM_finite_sum τ m hm hτ z,
    derivWeierstrassP_CM_finite_sum τ m hm hτ z] using h

/-- The actual point-group CM endomorphism has these finite affine coordinates off its kernel. -/
theorem periodCurveCMEnd_standardPeriodPoint_finite [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ))
    (z : ℂ) (hz : (τ : ℂ) * z ∉ (standardPeriodPair τ).lattice) :
    periodCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ) (standardPeriodPoint τ z) =
      WeierstrassCurve.Affine.Point.mk (cmIsogeny_equation τ m hm hτ z hz) := by
  rw [periodCurveCMEnd_standardPeriodPoint, standardPeriodPoint_of_not_mem τ
    (by simpa only [standardPeriodPair_lattice_eq_periodModule] using hz)]
  simp only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨weierstrassP_CM_finite_sum τ m hm hτ z,
    congrArg (fun w : ℂ => w / 2) (derivWeierstrassP_CM_finite_sum τ m hm hτ z)⟩

/-- The omitted affine branch is exactly the actual finer lattice and maps to infinity. -/
theorem periodCurveCMEnd_standardPeriodPoint_eq_zero_iff_divided [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m) (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (z : ℂ) :
    periodCurveCMEnd τ m (by simpa only [Int.cast_natCast] using hτ) (standardPeriodPoint τ z) = 0 ↔
      z ∈ periodModule ((τ : ℂ) / (m : ℂ)) := by
  rw [periodCurveCMEnd_standardPeriodPoint, standardPeriodPoint_eq_zero_iff,
    mul_mem_periodModule_iff_mem_divided τ m hm hτ]

end BakerHeegnerStark
