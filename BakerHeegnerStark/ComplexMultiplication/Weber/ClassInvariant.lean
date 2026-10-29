/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Weber.JointSpecialization

/-!
# The actual Weber class invariant

For every positive `m ≡ 3 (mod 8)` prime to three, the actual Weber square at
`√-m` belongs to `ℚ(j(√-m))`. Primality, squarefreeness, and class number one
are unnecessary for this descent.

`ComplexMultiplication/Weber/JointSpecialization.lean` proves this membership from the rational
joint modular relation, the actual cyclic-neighbour Galois action, and CM
centralization. Reality descent removes `√-m` from the compositum.
The theorem below specializes that proved result to the inert prime case.

## References

The classical Weber statement and its role in Heegner's proof follow Weber,
*Lehrbuch der Algebra* III; B. J. Birch, *Weber's class invariants* (1969);
H. M. Stark (1969); and D. A. Cox, *Primes of the form x² + ny²*, §12.B–C.
The finite-level descent and its relation to classical reciprocity are
documented in `ComplexMultiplication/Weber/JointSpecialization.lean`.
-/

namespace BakerHeegnerStark
open ModularForm

/-- Weber's class invariant in the inert class-number-one case (Weber; Birch 1969; Cox §12),
proved from the actual rational joint relation and CM torsion action. -/
theorem weberClassInvariant : WeberClassInvariant := by
  intro p _ _ hp hp8 hp3 _
  have hnot3 : ¬ 3 ∣ p := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  exact weberF_sq_sqrtPoint_mem_adjoin hp.pos hp8 hnot3

end BakerHeegnerStark
