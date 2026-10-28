/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import BakerHeegnerStark

/-!
# Axiom Audit

Run `lake env lean scripts/check_axioms.lean` after `lake build`.
Audit the proved reduction and the arithmetic and analytic results it reuses.
The target classification is a proposition, not an audited proof of the theorem.
-/

open Lean in
run_cmd do
  let declarations : Array Name := #[
    ``BakerHeegnerStark.mem_heegnerSet_or_inert_prime,
    ``BakerHeegnerStark.classNumberOneClassification_iff_inertPrimeClassification,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_of_mem_heegnerSet,
    ``QuadraticNumberFields.Heegner.heegner_xy_solutions,
    ``ModularForm.weber_cubic_factorization,
    ``ModularForm.modularPolynomialTwo_jInvariant]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in declarations do
    let axioms ← collectAxioms declaration
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{declaration} depends on unexpected axioms: {unexpected.toList}"
  logInfo m!"Axiom audit passed for {declarations.size} declarations."
