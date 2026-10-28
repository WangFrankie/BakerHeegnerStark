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
Audit the extracted arithmetic and modular-function proofs and the reduction.
The target classification is a proposition, not an audited proof of the theorem.
-/

open Lean in
run_cmd do
  let declarations : Array Name := #[
    ``BakerHeegnerStark.mem_heegnerSet_or_inert_prime,
    ``BakerHeegnerStark.classNumberOneClassification_iff_inertPrimeClassification,
    ``BakerHeegnerStark.classNumber_eq_one_neg1,
    ``BakerHeegnerStark.classNumber_eq_one_neg2,
    ``BakerHeegnerStark.classNumber_eq_one_neg3,
    ``BakerHeegnerStark.classNumber_eq_one_neg7,
    ``BakerHeegnerStark.classNumber_eq_one_neg11,
    ``BakerHeegnerStark.classNumber_eq_one_neg19,
    ``BakerHeegnerStark.classNumber_eq_one_neg43,
    ``BakerHeegnerStark.classNumber_eq_one_neg67,
    ``BakerHeegnerStark.classNumber_eq_one_neg163,
    ``BakerHeegnerStark.classNumber_eq_one_of_mem_heegnerSet,
    ``BakerHeegnerStark.eq_neg_one_or_eq_neg_two_of_exists_absNorm_eq_two,
    ``BakerHeegnerStark.eq_neg_seven_of_exists_absNorm_eq_two_of_mod_eight_eq_one,
    ``BakerHeegnerStark.exists_algebraNorm_natAbs_eq_two_of_classNumber_eq_one_of_mod_four_ne_one,
    ``BakerHeegnerStark.exists_algebraNorm_natAbs_eq_two_of_classNumber_eq_one_of_mod_eight_eq_one,
    ``BakerHeegnerStark.exists_algebraNorm_natAbs_eq_prime_of_classNumber_eq_one_of_dvd,
    ``BakerHeegnerStark.eq_neg_one_or_eq_neg_two_of_classNumber_eq_one_of_mod_four_ne_one,
    ``BakerHeegnerStark.eq_neg_seven_of_classNumber_eq_one_of_mod_eight_eq_one,
    ``BakerHeegnerStark.classNumber_eq_one_imp_exists_prime_of_mod_four_eq_one,
    ``BakerHeegnerStark.classNumber_eq_one_imp_mem_heegnerSet_of_mod_four_ne_one,
    ``BakerHeegnerStark.classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_one,
    ``BakerHeegnerStark.heegner_xy_solutions,
    ``BakerHeegnerStark.heegnerXYEquation_of_mem_heegnerXYSolutionSet,
    ``BakerHeegnerStark.heegnerGammaImageSet_eq_heegnerGammaSet,
    ``BakerHeegnerStark.gamma_mem_heegnerGammaSet_of_xy_solution,
    ``ModularForm.qExpansion_E₄,
    ``ModularForm.qExpansion_E₆,
    ``ModularForm.discriminant_qExpansion_coeff_two,
    ``ModularForm.discriminant_qExpansion_coeff_three,
    ``ModularForm.eta_mul_I_eq,
    ``ModularForm.eta_mul_I_im,
    ``ModularForm.eta_mul_I_re_pos,
    ``ModularForm.eta_add_one,
    ``ModularForm.eta_neg_inv,
    ``ModularForm.weberF_add_one,
    ``ModularForm.weberF₁_add_one,
    ``ModularForm.weberF₂_add_one,
    ``ModularForm.weberF_neg_inv,
    ``ModularForm.weberF₁_neg_inv,
    ``ModularForm.weberF₂_neg_inv,
    ``ModularForm.weberF_mul_weberF₁_mul_weberF₂,
    ``ModularForm.heckeTwoSum_eq,
    ``ModularForm.weberF_pow_24_sub_weberF₁_pow_24_sub_weberF₂_pow_24,
    ``ModularForm.heckeTwoSum₂_eq,
    ``ModularForm.gamma₂_cube,
    ``ModularForm.jInvariant_smul,
    ``ModularForm.mdifferentiable_jInvariant,
    ``ModularForm.weber_second_symmetric,
    ``ModularForm.weber_product_pow_24,
    ``ModularForm.jInvariant_eq_weberF,
    ``ModularForm.jInvariant_eq_weberF₁,
    ``ModularForm.jInvariant_eq_weberF₂,
    ``ModularForm.jInvariant_two_mul_eq_weberF₂,
    ``ModularForm.modularPolynomialTwo_swap,
    ``ModularForm.modularPolynomialTwo_monic,
    ``ModularForm.modularPolynomialTwo_natDegree,
    ``ModularForm.modularPolynomialTwo_param,
    ``ModularForm.modularPolynomialTwo_jInvariant_half,
    ``ModularForm.modularPolynomialTwo_jInvariant_half_add_one,
    ``ModularForm.weber_cubic_factorization,
    ``ModularForm.modularPolynomialTwo_jInvariant]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in declarations do
    let axioms ← collectAxioms declaration
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{declaration} depends on unexpected axioms: {unexpected.toList}"
  logInfo m!"Axiom audit passed for {declarations.size} declarations."
