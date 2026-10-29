/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ClassNumberOne.KnownCases

/-!
# The Imaginary Quadratic Class-Number-One Classification

`ClassNumberOneClassification` states the Baker-Heegner-Stark theorem.
It is proved by `BakerHeegnerStark.classNumberOneClassification` in
`ClassNumberOne/Classification.lean`. The nine individual class-number-one results
are proved in `ClassNumberOne/KnownCases.lean`.
-/

open QuadraticNumberFields
open scoped NumberField

namespace BakerHeegnerStark

/-- A negative squarefree integer defines a quadratic field of class number one
exactly when it is one of `-1, -2, -3, -7, -11, -19, -43, -67, -163`.
The proof is `BakerHeegnerStark.classNumberOneClassification`. -/
def ClassNumberOneClassification : Prop :=
  ∀ (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)], d < 0 →
    (NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 ↔ d ∈ heegnerSet)

end BakerHeegnerStark
