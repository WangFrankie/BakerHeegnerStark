/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import ImaginaryClassNumberOne.ClassNumberOne

/-!
# The Imaginary Quadratic Class-Number-One Classification

The target proposition states the unconditional Baker-Heegner-Stark theorem.
Defining this proposition does not prove it. The nine individual class-number-one
results are supplied by QuadraticNumberFields.
-/

open QuadraticNumberFields QuadraticNumberFields.Heegner
open scoped NumberField

namespace BakerHeegnerStark

/-- A negative squarefree integer defines a quadratic field of class number one
exactly when it is one of `-1, -2, -3, -7, -11, -19, -43, -67, -163`.
This is the theorem to be proved in this project. -/
def ClassNumberOneClassification : Prop :=
  ∀ (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)], d < 0 →
    (NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 ↔ d ∈ heegnerSet)

end BakerHeegnerStark
