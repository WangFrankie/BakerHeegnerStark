/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Weierstrass.Invariants
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Weierstrass Curve of an Actual Period Lattice

The coefficients use mathlib's actual lattice sums `g₂,g₃`. Their analytic
normalization proves nonsingularity for the standard upper-half-plane lattice
and identifies the algebraic curve invariant with the analytic modular `j`.
The Weierstrass functions satisfy this actual short equation away from poles.
Mathlib's classification of curves by algebraic `j` gives a scaling of actual
lattices with equal invariants, including at `j = 0` and `j = 1728`.
No uniformization, CM endomorphism, integrality, or class-field assertion is made.
-/

namespace BakerHeegnerStark

/-- The short equation `y² = x³ - (g₂/4)x - g₃/4` from the actual lattice invariants. -/
noncomputable def periodCurve (L : PeriodPair) : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩

/-- The first algebraic curve invariant has the classical lattice normalization. -/
theorem periodCurve_c₄ (L : PeriodPair) : (periodCurve L).c₄ = 12 * L.g₂ := by
  dsimp [periodCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

/-- The second algebraic curve invariant has the classical lattice normalization. -/
theorem periodCurve_c₆ (L : PeriodPair) : (periodCurve L).c₆ = 216 * L.g₃ := by
  dsimp [periodCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ring

/-- The actual short curve's discriminant is the lattice discriminant. -/
theorem periodCurve_discriminant (L : PeriodPair) :
    (periodCurve L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  dsimp [periodCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Nonsingularity follows from the actual modular discriminant, not a CM hypothesis. -/
instance standardPeriodCurve_isElliptic (τ : UpperHalfPlane) :
    (periodCurve (standardPeriodPair τ)).IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr (by
    rw [periodCurve_discriminant]
    exact standardPeriodPair_discriminant_ne_zero τ)

/-- Algebraic `j` for the actual lattice equation, whenever it is nonsingular. -/
theorem periodCurve_j (L : PeriodPair) [(periodCurve L).IsElliptic] :
    (periodCurve L).j = 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [WeierstrassCurve.j_eq, periodCurve_discriminant, periodCurve_c₄]
  ring

/-- The algebraic invariant of the actual standard period curve is the analytic modular `j`. -/
theorem standardPeriodCurve_j (τ : UpperHalfPlane) :
    (periodCurve (standardPeriodPair τ)).j = ModularForm.jInvariant τ :=
  (periodCurve_j (standardPeriodPair τ)).trans (standardPeriodPair_j τ)

/-- The actual Weierstrass functions lie on the short period equation away
from the lattice; the prescribed pole values are not claimed to be affine points. -/
theorem periodCurve_equation (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    (L.derivWeierstrassP z / 2) ^ 2 = (L.weierstrassP z) ^ 3 +
      (periodCurve L).a₄ * L.weierstrassP z + (periodCurve L).a₆ := by
  dsimp only [periodCurve]
  have h := L.derivWeierstrassP_sq z hz
  linear_combination (1 / 4 : ℂ) * h

/-- Equality of algebraic `j` gives a complex scaling with the same actual
numerical lattice invariants. This uses the curve classification uniformly,
including `j = 0` and `j = 1728`; no nonvanishing of `g₂` or `g₃` is assumed. -/
theorem periodCurve_exists_scale_of_j_eq (L M : PeriodPair)
    [(periodCurve L).IsElliptic] [(periodCurve M).IsElliptic]
    (hj : (periodCurve L).j = (periodCurve M).j) :
    ∃ c : ℂˣ, (scalePeriodPair L c).g₂ = M.g₂ ∧ (scalePeriodPair L c).g₃ = M.g₃ := by
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
    (periodCurve L) (periodCurve M) hj
  refine ⟨C.u, ?_, ?_⟩
  · have h := congrArg WeierstrassCurve.c₄ hC
    rw [WeierstrassCurve.variableChange_c₄, periodCurve_c₄, periodCurve_c₄] at h
    simp only [Units.val_inv_eq_inv_val, inv_pow] at h
    rw [scalePeriodPair_g₂]
    linear_combination h / 12
  · have h := congrArg WeierstrassCurve.c₆ hC
    rw [WeierstrassCurve.variableChange_c₆, periodCurve_c₆, periodCurve_c₆] at h
    simp only [Units.val_inv_eq_inv_val, inv_pow] at h
    rw [scalePeriodPair_g₃]
    linear_combination h / 216

/-- Analytic `j` equality yields matching actual invariants after one nonzero
complex scaling of the standard periods. Recovery of the lattice is separate. -/
theorem standardPeriodPair_exists_scale_of_jInvariant_eq (τ σ : UpperHalfPlane)
    (hj : ModularForm.jInvariant τ = ModularForm.jInvariant σ) :
    ∃ c : ℂˣ, (scalePeriodPair (standardPeriodPair τ) c).g₂ = (standardPeriodPair σ).g₂ ∧
      (scalePeriodPair (standardPeriodPair τ) c).g₃ = (standardPeriodPair σ).g₃ := by
  apply periodCurve_exists_scale_of_j_eq
  simpa only [standardPeriodCurve_j] using hj

end BakerHeegnerStark
