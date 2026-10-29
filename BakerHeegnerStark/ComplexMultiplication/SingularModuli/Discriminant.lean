/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.SingularModuli.Conjugates
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.NormDiscriminant
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.NormSpectrum
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.PrimitiveRelation

/-!
# Recognition of the Original CM Discriminant

Primitive integer fixed matrices recover the primitive quadratic norm spectrum
of an actual quadratic parameter. Canonical normalization and the small-value
recognition theorems identify its discriminant from the positive-level modular
root data of the original maximal-order point. Unit cases are included.
-/

open ModularForm Polynomial

namespace BakerHeegnerStark

/-- An actual primitive quadratic point with the same positive-level diagonal
root multiplicities as `cmPoint m` has discriminant exactly `-m`.
No class-number bound or CM reciprocity theorem is assumed. -/
theorem discriminant_eq_of_cmPoint_rootMultiplicity {m : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) (τ : UpperHalfPlane)
    (a b c : ℤ) (ha : 0 < a)
    (hprim : Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0)
    (hmult : ∀ N : ℕ, 0 < N →
      rootMultiplicity (jInvariant (cmPoint m)) (cyclicSublatticePolynomial N (cmPoint m)) =
        rootMultiplicity (jInvariant τ) (cyclicSublatticePolynomial N τ)) :
    b ^ 2 - 4 * a * c = -(m : ℤ) := by
  let c₀ : ℤ := ((m + 1) / 4 : ℕ)
  let d : ℤ := quadraticNormConstant b (a * c)
  have hc₀ : 1 ≤ c₀ := by dsimp [c₀]; omega
  have hD : b ^ 2 - 4 * (a * c) < 0 := by
    simpa only [mul_assoc] using
      quadratic_discriminant_neg_of_upperHalfPlane_root τ (ne_of_gt ha) hτ
  have hdpos : 0 < d := quadraticNormConstant_pos hD
  have hd : 1 ≤ d := by omega
  have hnorm (n : ℤ) (hn : 1 < n) : PrimitiveOddNormValue c₀ n ↔
      ∃ x k : ℤ, Nat.Coprime x.natAbs k.natAbs ∧
        x ^ 2 + b * x * k + (a * c) * k ^ 2 = n := by
    have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
    have hN : 0 < n.toNat := by omega
    have hsource := rootMultiplicity_cmPoint_pos_iff_primitiveOddNormValue hm hm4 hN
    have htarget := rootMultiplicity_cyclicSublatticePolynomial_pos_iff_primitiveQuadraticNorm
      hN τ a b c (ne_of_gt ha) hprim hτ
    rw [hncast] at hsource htarget
    rw [hmult _ hN] at hsource
    exact hsource.symm.trans htarget
  have hpar : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases hpar with hpar | hpar
  · exfalso
    apply primitiveOddEvenNormValue_spectra_ne hc₀ hd
    intro n hn
    exact (hnorm n hn).trans (primitiveQuadraticNorm_iff_even hpar n)
  · have hcd : c₀ = d := primitiveOddNormValue_spectrum_injective hc₀ hd
      (fun n hn => (hnorm n hn).trans (primitiveQuadraticNorm_iff_odd hpar n))
    have hdisc := quadraticNormConstant_discriminant b (a * c)
    rw [hpar] at hdisc
    have hmc : 4 * c₀ = (m : ℤ) + 1 := by dsimp [c₀]; omega
    change b ^ 2 - 4 * a * c = -(m : ℤ)
    change c₀ = quadraticNormConstant b (a * c) at hcd
    nlinarith [hdisc]

/-- Every algebraic conjugate of the actual singular modulus is represented by
an actual primitive imaginary quadratic relation of the original discriminant.
All positive-level diagonal root multiplicities are retained. -/
theorem exists_cmPoint_conjugate_primitive_discriminant {m : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) {x : ℂ}
    (hx : aeval x (minpoly ℚ (jInvariant (cmPoint m))) = 0) :
    ∃ τ : UpperHalfPlane, jInvariant τ = x ∧
      (∀ N : ℕ, 0 < N →
        rootMultiplicity (jInvariant (cmPoint m)) (cyclicSublatticePolynomial N (cmPoint m)) =
          rootMultiplicity (jInvariant τ) (cyclicSublatticePolynomial N τ)) ∧
      ∃ a b c : ℤ, 0 < a ∧
        Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1 ∧
        b ^ 2 - 4 * a * c = -(m : ℤ) ∧
        (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0 := by
  obtain ⟨τ, hτ, hmult, a, b, c, ha, _, hquad⟩ :=
    exists_integer_quadratic_cmPoint_conjugate hm hm4 hx
  obtain ⟨a', b', c', ha', hprim, _, hquad'⟩ :=
    exists_primitive_integer_quadratic τ a b c ha hquad
  exact ⟨τ, hτ, hmult, a', b', c', ha', hprim,
    discriminant_eq_of_cmPoint_rootMultiplicity hm hm4 τ a' b' c' ha' hprim hquad' hmult,
    hquad'⟩

end BakerHeegnerStark
