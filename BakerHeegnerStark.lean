/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ClassNumberOne.InertPrimes
import BakerHeegnerStark.ClassNumberOne.Heegner.IntegralPoints
import BakerHeegnerStark.ModularForms.Eta.Positivity
import BakerHeegnerStark.ModularForms.ModularPolynomial.LevelTwo

/-!
# The Baker-Heegner-Stark Theorem

An independent development over QuadraticNumberFields. The complete
classification is the proposition `BakerHeegnerStark.ClassNumberOneClassification`.
The nine known cases, ideal-theoretic reductions, Heegner integral-point
classification, and general Weber/modular-polynomial identities are proved
here. Quadratic-field and binary-quadratic-form theory remains in
QuadraticNumberFields. This import exposes the extracted core; subsequent
analytic and arithmetic modules build on it.
-/
