/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.CoefficientQExpansion
import BakerHeegnerStark.ModularForms.QExpansion.CyclotomicPowerSeries

/-!
# Formal Cyclotomic Expansions of the Twisted Gamma Root Product

The two complete integer gamma numerator series define the common-width root
expansions over any field. Coefficient maps commute with these expansions and
their finite product. Coprime powers of the common root of unity reindex the
actual cyclic-sublattice factors, using the existing residue permutation and
phase identity. Specialization at the actual complex phase recovers the full
gamma q-expansions. These formal identities require only a positive level.
-/

open ModularForm Polynomial

noncomputable section

namespace BakerHeegnerStark

variable {K L : Type*} [Field K] [Field L]

/-- The full regularized common-width gamma root series over an arbitrary field,
with formal translation phase `θ ^ (a * b)`. -/
def cyclotomicGammaRootQExpansion {N : ℕ} (hN : 0 < N) (θ : K)
    (t : ℕ × ℕ × ℕ) (ha : 0 < t.1) : PowerSeries K :=
  PowerSeries.C (((θ ^ (t.1 * t.2.1)) ^ ((N + 1) / 3))⁻¹) *
    (PowerSeries.expand N (Nat.ne_of_gt hN)
      (PowerSeries.map (Int.castRingHom K) gammaIntegralNumerator) *
    PowerSeries.expand (t.1 * t.1)
      (Nat.mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt ha))
      (PowerSeries.rescale (θ ^ (t.1 * t.2.1))
        (PowerSeries.map (Int.castRingHom K) gammaIntegralNumerator)))

/-- Changing the coefficient field only changes the formal common phase. -/
@[simp]
theorem map_cyclotomicGammaRootQExpansion {N : ℕ} (hN : 0 < N)
    (f : K →+* L) (θ : K) (t : ℕ × ℕ × ℕ) (ha : 0 < t.1) :
    PowerSeries.map f (cyclotomicGammaRootQExpansion hN θ t ha) =
      cyclotomicGammaRootQExpansion hN (f θ) t ha := by
  have hG : PowerSeries.map f
      (PowerSeries.map (Int.castRingHom K) gammaIntegralNumerator) =
      PowerSeries.map (Int.castRingHom L) gammaIntegralNumerator := by
    ext m
    simp
  simp only [cyclotomicGammaRootQExpansion, map_mul, PowerSeries.map_C,
    map_inv₀, map_pow, PowerSeries.map_expand, ← PowerSeries.rescale_map, hG]

/-- The finite product of regularized gamma factors, with the actual gamma pole
orders and a common phase in an arbitrary field. -/
def cyclotomicGammaQPolynomial {N : ℕ} (hN : 0 < N) (θ : K) :
    (PowerSeries K)[X] :=
  ∏ t ∈ (cyclicSublatticeTriples N).attach,
    (C ((PowerSeries.X : PowerSeries K) ^ cyclicSublatticeGammaPoleOrder N t.1) * X -
      C (cyclotomicGammaRootQExpansion hN θ t.1 (cyclicSublatticeTriple_pos hN t).1))

/-- Coefficientwise field maps commute with the full finite gamma root product. -/
@[simp]
theorem map_cyclotomicGammaQPolynomial {N : ℕ} (hN : 0 < N)
    (f : K →+* L) (θ : K) :
    Polynomial.map (PowerSeries.map f) (cyclotomicGammaQPolynomial hN θ) =
      cyclotomicGammaQPolynomial hN (f θ) := by
  classical
  unfold cyclotomicGammaQPolynomial
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro t ht
  simp

/-- The existing residue permutation implements the power action on each full
formal gamma root series, including its inverse residual phase. -/
theorem cyclotomicGammaRootQExpansion_residuePerm {N : ℕ} (hN : 0 < N)
    (θ : K) (hθ : θ ^ N = 1) (u : ℕ) (hu : Nat.Coprime u N)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    cyclotomicGammaRootQExpansion hN θ (cyclicSublatticeResiduePerm hN u hu t).val
        (cyclicSublatticeTriple_pos hN (cyclicSublatticeResiduePerm hN u hu t)).1 =
      cyclotomicGammaRootQExpansion hN (θ ^ u) t.val
        (cyclicSublatticeTriple_pos hN t).1 := by
  simp only [cyclotomicGammaRootQExpansion, cyclicSublatticeResiduePerm_apply_val]
  rw [cyclotomicPhase_mul_mod hN θ hθ t.property u]

/-- Coprime powers of an `N`-th root of unity fix the complete formal gamma
q-polynomial by reindexing its actual cyclic-sublattice factors. -/
theorem cyclotomicGammaQPolynomial_pow {N : ℕ} (hN : 0 < N) (θ : K)
    (hθ : θ ^ N = 1) (u : ℕ) (hu : Nat.Coprime u N) :
    cyclotomicGammaQPolynomial hN (θ ^ u) = cyclotomicGammaQPolynomial hN θ := by
  classical
  unfold cyclotomicGammaQPolynomial
  refine Finset.prod_equiv (cyclicSublatticeResiduePerm hN u hu)
    (fun t => by simp) ?_
  intro t ht
  rw [cyclotomicGammaRootQExpansion_residuePerm hN θ hθ u hu t]
  simp only [cyclicSublatticeResiduePerm_apply_val, cyclicSublatticeGammaPoleOrder]

/-- A field endomorphism acting on the common root by a coprime power fixes the
full gamma q-polynomial coefficientwise. -/
theorem map_cyclotomicGammaQPolynomial_eq_self {N : ℕ} (hN : 0 < N)
    (θ : K) (hθ : θ ^ N = 1) (σ : K →+* K) (u : ℕ)
    (hu : Nat.Coprime u N) (hσ : σ θ = θ ^ u) :
    Polynomial.map (PowerSeries.map σ) (cyclotomicGammaQPolynomial hN θ) =
      cyclotomicGammaQPolynomial hN θ := by
  rw [map_cyclotomicGammaQPolynomial, hσ,
    cyclotomicGammaQPolynomial_pow hN θ hθ u hu]

/-- At the actual common complex phase, the formal gamma root series is exactly
the previously defined full common-width expansion. -/
theorem cyclotomicGammaRootQExpansion_complex {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (ha : 0 < t.1) :
    cyclotomicGammaRootQExpansion hN (cyclicSublatticePhase 1 N) t ha =
      cyclicSublatticeGammaRootQExpansion hN t ha := by
  simp only [cyclotomicGammaRootQExpansion, cyclicSublatticeGammaRootQExpansion,
    cyclicSublatticeGammaPhase, cyclicSublatticePhase_commonRoot hN ht]

/-- Specialization at the actual common complex phase recovers the actual full
gamma q-polynomial, with exactly the same pole orders and root expansions. -/
theorem cyclotomicGammaQPolynomial_complex {N : ℕ} (hN : 0 < N) :
    cyclotomicGammaQPolynomial hN (cyclicSublatticePhase 1 N) =
      cyclicSublatticeGammaQPolynomial hN := by
  classical
  unfold cyclotomicGammaQPolynomial cyclicSublatticeGammaQPolynomial
  apply Finset.prod_congr rfl
  intro t ht
  rw [cyclotomicGammaRootQExpansion_complex hN t.property]

end BakerHeegnerStark
