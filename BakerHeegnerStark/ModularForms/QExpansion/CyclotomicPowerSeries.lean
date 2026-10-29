/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.CoefficientQExpansion
import BakerHeegnerStark.ModularForms.CyclicSublattice.Residues

/-!
# Formal Cyclotomic Expansions of the Actual Root Product

The common-width root expansions and their finite symmetric product are defined
algebraically over any field. Coefficient maps commute with these constructions,
and coprime powers of the common root of unity permute their actual factors.
Specialization at the complex translation phase recovers the previously defined
q-expansions. No continuity or coefficient descent is assumed here.
-/

open ModularForm Polynomial

noncomputable section

namespace BakerHeegnerStark

private theorem cyclotomicTriple_pos {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) : 0 < t.1 := by
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  by_contra h
  have hz : t.1 = 0 := by omega
  simp [hz] at had
  omega

variable {K L : Type*} [Field K] [Field L]

/-- The regularized common-width root expansion with formal phase
`θ ^ (a * b)`, constructed over an arbitrary field. -/
def cyclotomicRootQExpansion (θ : K) (t : ℕ × ℕ × ℕ) (ha : 0 < t.1) :
    PowerSeries K :=
  PowerSeries.C (θ ^ (t.1 * t.2.1))⁻¹ *
    PowerSeries.expand (t.1 * t.1)
      (Nat.mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt ha))
      (PowerSeries.rescale (θ ^ (t.1 * t.2.1))
        (PowerSeries.map (Int.castRingHom K) jInvariantIntegralNumerator))

/-- Changing the coefficient field only changes the formal common phase. -/
@[simp]
theorem map_cyclotomicRootQExpansion (f : K →+* L) (θ : K)
    (t : ℕ × ℕ × ℕ) (ha : 0 < t.1) :
    PowerSeries.map f (cyclotomicRootQExpansion θ t ha) =
      cyclotomicRootQExpansion (f θ) t ha := by
  have hJ : PowerSeries.map f
      (PowerSeries.map (Int.castRingHom K) jInvariantIntegralNumerator) =
      PowerSeries.map (Int.castRingHom L) jInvariantIntegralNumerator := by
    ext m
    simp
  simp only [cyclotomicRootQExpansion, map_mul, PowerSeries.map_C,
    map_inv₀, map_pow, PowerSeries.map_expand, ← PowerSeries.rescale_map, hJ]

/-- The same finite regularized product as the actual complex q-polynomial,
with its common phase allowed to lie in any field. -/
def cyclotomicQPolynomial {N : ℕ} (hN : 0 < N) (θ : K) : (PowerSeries K)[X] :=
  ∏ t ∈ (cyclicSublatticeTriples N).attach,
    (C ((PowerSeries.X : PowerSeries K) ^ (t.1.1 * t.1.1)) * X -
      C (cyclotomicRootQExpansion θ t.1 (cyclotomicTriple_pos hN t.2)))

/-- Coefficientwise field maps commute with the finite formal root product. -/
@[simp]
theorem map_cyclotomicQPolynomial {N : ℕ} (hN : 0 < N)
    (f : K →+* L) (θ : K) :
    Polynomial.map (PowerSeries.map f) (cyclotomicQPolynomial hN θ) =
      cyclotomicQPolynomial hN (f θ) := by
  classical
  unfold cyclotomicQPolynomial
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro t ht
  simp

/-- The residue reduction changes the phase exponent by exactly a multiple of
`N`; this identity does not require coprimality of `u`. -/
theorem cyclotomicPhase_exponent_decomposition {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (u : ℕ) :
    t.1 * ((u * t.2.1) % t.2.2) + N * ((u * t.2.1) / t.2.2) =
      u * (t.1 * t.2.1) := by
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  calc
    _ = t.1 * ((u * t.2.1) % t.2.2 + t.2.2 * ((u * t.2.1) / t.2.2)) := by
      rw [← had]
      ring
    _ = t.1 * (u * t.2.1) := by rw [Nat.mod_add_div]
    _ = _ := by ring

/-- The exact phase identity induced by multiplying and reducing a residue. -/
theorem cyclotomicPhase_mul_mod {N : ℕ} (hN : 0 < N) (θ : K)
    (hθ : θ ^ N = 1) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (u : ℕ) :
    θ ^ (t.1 * ((u * t.2.1) % t.2.2)) = (θ ^ u) ^ (t.1 * t.2.1) := by
  calc
    _ = θ ^ (t.1 * ((u * t.2.1) % t.2.2)) *
        (θ ^ N) ^ ((u * t.2.1) / t.2.2) := by rw [hθ, one_pow, mul_one]
    _ = θ ^ (t.1 * ((u * t.2.1) % t.2.2) +
        N * ((u * t.2.1) / t.2.2)) := by simp only [pow_add, pow_mul]
    _ = _ := by rw [cyclotomicPhase_exponent_decomposition hN ht, pow_mul]

/-- The actual residue permutation preserves the sparse exponent shift and
implements the power action on every formal root series. -/
theorem cyclotomicRootQExpansion_residuePerm {N : ℕ} (hN : 0 < N)
    (θ : K) (hθ : θ ^ N = 1) (u : ℕ) (hu : Nat.Coprime u N)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    cyclotomicRootQExpansion θ (cyclicSublatticeResiduePerm hN u hu t).val
        (cyclotomicTriple_pos hN (cyclicSublatticeResiduePerm hN u hu t).property) =
      cyclotomicRootQExpansion (θ ^ u) t.val (cyclotomicTriple_pos hN t.property) := by
  simp only [cyclotomicRootQExpansion, cyclicSublatticeResiduePerm_apply_val]
  rw [cyclotomicPhase_mul_mod hN θ hθ t.property u]

/-- Coprime powers of an `N`-th root of unity leave the finite symmetric product
unchanged, by reindexing its actual cyclic-sublattice factors. -/
theorem cyclotomicQPolynomial_pow {N : ℕ} (hN : 0 < N) (θ : K)
    (hθ : θ ^ N = 1) (u : ℕ) (hu : Nat.Coprime u N) :
    cyclotomicQPolynomial hN (θ ^ u) = cyclotomicQPolynomial hN θ := by
  classical
  unfold cyclotomicQPolynomial
  refine Finset.prod_equiv (cyclicSublatticeResiduePerm hN u hu)
    (fun t => by simp) ?_
  intro t ht
  rw [cyclotomicRootQExpansion_residuePerm hN θ hθ u hu t]
  simp only [cyclicSublatticeResiduePerm_apply_val]

/-- An endomorphism acting on the common root by a coprime power fixes the
q-polynomial coefficientwise. This is a purely formal statement. -/
theorem map_cyclotomicQPolynomial_eq_self {N : ℕ} (hN : 0 < N)
    (θ : K) (hθ : θ ^ N = 1) (σ : K →+* K) (u : ℕ)
    (hu : Nat.Coprime u N) (hσ : σ θ = θ ^ u) :
    Polynomial.map (PowerSeries.map σ) (cyclotomicQPolynomial hN θ) =
      cyclotomicQPolynomial hN θ := by
  rw [map_cyclotomicQPolynomial, hσ, cyclotomicQPolynomial_pow hN θ hθ u hu]

/-- At the actual complex common phase, the formal individual root expansion
is precisely the previously defined analytic root expansion. -/
theorem cyclotomicRootQExpansion_complex {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (ha : 0 < t.1) :
    cyclotomicRootQExpansion (cyclicSublatticePhase 1 N) t ha =
      cyclicSublatticeRootQExpansion t ha := by
  simp only [cyclotomicRootQExpansion, cyclicSublatticeRootQExpansion,
    cyclicSublatticePhase_commonRoot hN ht]

/-- Specialization of the formal finite product recovers the actual complex
q-polynomial, not merely a polynomial with matching formal properties. -/
theorem cyclotomicQPolynomial_complex {N : ℕ} (hN : 0 < N) :
    cyclotomicQPolynomial hN (cyclicSublatticePhase 1 N) =
      cyclicSublatticeQPolynomial hN := by
  classical
  unfold cyclotomicQPolynomial cyclicSublatticeQPolynomial
  apply Finset.prod_congr rfl
  intro t ht
  rw [cyclotomicRootQExpansion_complex hN t.property]

end BakerHeegnerStark
