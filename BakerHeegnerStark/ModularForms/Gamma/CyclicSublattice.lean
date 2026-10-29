/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.Modularity
import BakerHeegnerStark.ModularForms.CyclicSublattice.Basic

/-!
# Twisted Gamma Values of Cyclic Sublattices

The actual cyclic-sublattice gamma value includes the cubic phase prescribed
by the upper-triangular triple. Its cube is the product of the two j-values.
Positive triples give holomorphic functions with polynomial j-growth at the
cusp. No modular-invariance assertion or q-expansion of gamma is used here.
-/

open UpperHalfPlane ModularForm Filter Asymptotics
open scoped Topology Manifold

noncomputable section

namespace BakerHeegnerStark

/-- The actual twisted gamma value attached to an upper-triangular triple. -/
def cyclicSublatticeGammaRoot (t : ℕ × ℕ × ℕ) (τ : UpperHalfPlane) : ℂ :=
  gammaPhaseThree ^ (t.1 * t.2.1) * gamma₂ τ * gamma₂ (cyclicSublatticePoint t τ)

/-- Cubing removes the phase, for every triple, including the arbitrary
extension of `cyclicSublatticePoint` outside the positive triples. -/
theorem cyclicSublatticeGammaRoot_cube (t : ℕ × ℕ × ℕ) (τ : UpperHalfPlane) :
    cyclicSublatticeGammaRoot t τ ^ 3 =
      jInvariant τ * jInvariant (cyclicSublatticePoint t τ) := by
  have hphase : (gammaPhaseThree ^ (t.1 * t.2.1)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm (t.1 * t.2.1) 3, pow_mul,
      gammaPhaseThree_cube, one_pow]
  simp only [cyclicSublatticeGammaRoot, mul_pow, hphase, gamma₂_cube, one_mul]

/-- Every actual twisted gamma value for a positive triple is holomorphic. -/
theorem mdifferentiable_cyclicSublatticeGammaRoot {t : ℕ × ℕ × ℕ}
    (ha : 0 < t.1) (hd : 0 < t.2.2) : MDiff (cyclicSublatticeGammaRoot t) := by
  unfold cyclicSublatticeGammaRoot
  exact (mdifferentiable_const.mul mdifferentiable_gamma₂).mul
    (mdifferentiable_gamma₂.comp (mdifferentiable_cyclicSublatticePoint ha hd))

/-- The cube identity bounds gamma by j at the cusp, without using a gamma
q-expansion or choosing any branch of a cube root. -/
theorem isBigO_gamma₂_jInvariant :
    gamma₂ =O[atImInfty] jInvariant := by
  apply IsBigO.of_pow (n := 3) (by decide)
  apply IsBigO.of_bound 1
  filter_upwards [eventually_one_le_norm_jInvariant] with τ hτ
  simpa only [Pi.pow_apply, gamma₂_cube, norm_pow, one_mul, pow_one] using
    pow_le_pow_right₀ hτ (show 1 ≤ (3 : ℕ) by decide)

/-- A level-N twisted gamma value has polynomial growth bounded by `j^(N+1)`. -/
theorem isBigO_cyclicSublatticeGammaRoot_of_mem
    {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) :
    cyclicSublatticeGammaRoot t =O[atImInfty]
      (fun τ : UpperHalfPlane => jInvariant τ ^ (N + 1)) := by
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  have hpos : 0 < t.1 * t.2.2 := by omega
  have ha : 0 < t.1 := by
    by_contra h
    have hz : t.1 = 0 := by omega
    simp [hz] at hpos
  have hd : 0 < t.2.2 := by
    by_contra h
    have hz : t.2.2 = 0 := by omega
    simp [hz] at hpos
  have hgamma : (fun τ : UpperHalfPlane => gamma₂ (cyclicSublatticePoint t τ))
      =O[atImInfty] (fun τ : UpperHalfPlane => jInvariant τ ^ N) :=
    (isBigO_gamma₂_jInvariant.comp_tendsto
      (tendsto_cyclicSublatticePoint_atImInfty ha hd)).trans
      (isBigO_jInvariant_of_mem_cyclicSublatticeTriples hN ht)
  unfold cyclicSublatticeGammaRoot
  simpa only [mul_assoc, pow_succ'] using
    (isBigO_gamma₂_jInvariant.mul hgamma).const_mul_left
      (gammaPhaseThree ^ (t.1 * t.2.1))

end BakerHeegnerStark
