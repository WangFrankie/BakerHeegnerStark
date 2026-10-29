/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.SingularModuli.Basic
import BakerHeegnerStark.ModularForms.ModularPolynomial.Conjugates
import BakerHeegnerStark.ModularForms.ModularPolynomial.FixedPoints
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.NormMinimum

/-!
# Actual Imaginary Quadratic Representatives of CM Conjugates

The maximal-order point has a primitive norm representation at the nontrivial
level `(m+1)/4+2`, including `m=3`. Its algebraic conjugates preserve the actual
diagonal root multiplicities, so their upper-half-plane representatives also
have nontrivial primitive fixed matrices. These yield actual integral quadratic
relations of negative discriminant. Equality of CM orders or primitive
discriminants is not asserted.
-/

open ModularForm Polynomial

namespace BakerHeegnerStark

/-- The maximal-order point has exactly the primitive odd norm spectrum with
constant `(m+1)/4`, at every positive modular level. -/
theorem rootMultiplicity_cmPoint_pos_iff_primitiveOddNormValue {m N : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) (hN : 0 < N) :
    (0 < rootMultiplicity (jInvariant (cmPoint m)) (cyclicSublatticePolynomial N (cmPoint m))) ↔
      PrimitiveOddNormValue (((m + 1) / 4 : ℕ) : ℤ) (N : ℤ) := by
  have hquad : (cmPoint m : ℂ) ^ 2 + ((-1 : ℤ) : ℂ) * (cmPoint m : ℂ) +
      (((m + 1) / 4 : ℕ) : ℂ) = 0 := by
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, one_mul, sub_eq_add_neg] using
      cmPoint_quadratic hm hm4
  have h := rootMultiplicity_cyclicSublatticePolynomial_pos_iff_quadraticNorm
    hN (cmPoint m) (-1) (((m + 1) / 4 : ℕ) : ℤ) hquad
  simpa only [PrimitiveOddNormValue, oddQuadraticNorm, neg_one_mul, neg_mul,
    one_mul, sub_eq_add_neg] using h

/-- A uniform nontrivial self-root level for every positive `m ≡ 3 (mod 4)`.
The norm coordinates `x=-1, k=1` are primitive, even in the exceptional case `m=3`. -/
theorem rootMultiplicity_cmPoint_nontrivial_level_pos {m : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) :
    0 < rootMultiplicity (jInvariant (cmPoint m))
      (cyclicSublatticePolynomial ((m + 1) / 4 + 2) (cmPoint m)) := by
  apply (rootMultiplicity_cmPoint_pos_iff_primitiveOddNormValue hm hm4 (by omega)).mpr
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    primitiveOddNormValue_c_add_two (((m + 1) / 4 : ℕ) : ℤ)

/-- Every conjugate of the maximal-order singular modulus is an actual j-value
of an imaginary quadratic point and retains all diagonal modular root
multiplicities. The exhibited quadratic is not yet identified with the original
CM order or normalized to its primitive discriminant. -/
theorem exists_integer_quadratic_cmPoint_conjugate {m : ℕ}
    (hm : 0 < m) (hm4 : m % 4 = 3) {x : ℂ}
    (hx : aeval x (minpoly ℚ (jInvariant (cmPoint m))) = 0) :
    ∃ τ : UpperHalfPlane, jInvariant τ = x ∧
      (∀ N : ℕ, 0 < N →
        rootMultiplicity (jInvariant (cmPoint m)) (cyclicSublatticePolynomial N (cmPoint m)) =
          rootMultiplicity (jInvariant τ) (cyclicSublatticePolynomial N τ)) ∧
      ∃ a b c : ℤ, 0 < a ∧ b ^ 2 - 4 * a * c < 0 ∧
        (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0 := by
  obtain ⟨τ, hτ, hmult⟩ := exists_jInvariant_minpoly_root_preserving_rootMultiplicity
    (cmPoint m) ((singularModulusIntegrality m hm hm4).tower_top (A := ℚ)) hx
  refine ⟨τ, hτ, hmult, ?_⟩
  apply exists_integer_quadratic_of_cyclicSublattice_rootMultiplicity_pos
    (N := (m + 1) / 4 + 2) (by omega) τ
  rw [← hmult _ (by omega)]
  exact rootMultiplicity_cmPoint_nontrivial_level_pos hm hm4

end BakerHeegnerStark
