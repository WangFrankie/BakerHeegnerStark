/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Orders.Quadratic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Period Lattices

For a nonreal complex parameter, `1` and the parameter form a real basis.
Their integer span is therefore a discrete, full-rank lattice in the complex
plane. This supplies the topological lattice structure for the period modules
whose scalar multipliers are computed in `ComplexMultiplication/Orders/Quadratic.lean`.
-/

open Module

namespace BakerHeegnerStark

/-- The real basis of the complex plane given by `1` and a nonreal parameter. -/
noncomputable def periodBasis (τ : ℂ) (hτ : τ.im ≠ 0) : Basis (Fin 2) ℝ ℂ := by
  refine Basis.mk (v := ![1, τ]) ?_ ?_
  · rw [linearIndependent_fin2]
    change τ ≠ 0 ∧ ∀ a : ℝ, a • τ ≠ 1
    constructor
    · intro hz
      apply hτ
      rw [hz]
      rfl
    · intro a ha
      have hi := congrArg Complex.im ha
      simp only [Complex.smul_im, smul_eq_mul, Complex.one_im] at hi
      have ha0 : a = 0 := (mul_eq_zero.mp hi).resolve_right hτ
      simp [ha0] at ha
  · rw [Matrix.range_cons_cons_empty]
    intro z _
    apply Submodule.mem_span_pair.mpr
    refine ⟨z.re - z.im / τ.im * τ.re, z.im / τ.im, ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]
      ring
    · simp only [Complex.add_im, Complex.smul_im, Complex.one_im, smul_eq_mul, mul_zero,
        zero_add]
      exact div_mul_cancel₀ _ hτ

/-- The basis vectors are precisely the two period generators. -/
theorem periodBasis_range (τ : ℂ) (hτ : τ.im ≠ 0) :
    Set.range (periodBasis τ hτ) = ({1, τ} : Set ℂ) := by
  simp only [periodBasis, Basis.coe_mk, Matrix.range_cons_cons_empty]

/-- A nonreal period module has the discrete subspace topology. -/
instance periodModule_discreteTopology (τ : ℂ) [Fact (τ.im ≠ 0)] :
    DiscreteTopology (periodModule τ) := by
  have hr : Submodule.span ℤ (Set.range (periodBasis τ Fact.out)) = periodModule τ := by
    rw [periodBasis_range]
    rfl
  rw [← hr]
  infer_instance

/-- The nonreal period module is a full-rank real lattice. -/
instance periodModule_isZLattice (τ : ℂ) [Fact (τ.im ≠ 0)] :
    IsZLattice ℝ (periodModule τ) := by
  have hr : Submodule.span ℤ (Set.range (periodBasis τ Fact.out)) = periodModule τ := by
    rw [periodBasis_range]
    rfl
  constructor
  rw [← hr]
  exact ZSpan.span_top (periodBasis τ Fact.out)

/-- The integer rank of a nonreal period module is two. -/
theorem periodModule_finrank (τ : ℂ) [Fact (τ.im ≠ 0)] :
    Module.finrank ℤ (periodModule τ) = 2 := by
  rw [ZLattice.rank ℝ, Module.finrank_eq_card_basis (periodBasis τ Fact.out),
    Fintype.card_fin]

/-- The integer basis of a period lattice, with the same two generators. -/
noncomputable def periodIntegralBasis (τ : ℂ) (hτ : τ.im ≠ 0) :
    Basis (Fin 2) ℤ (periodModule τ) :=
  (Basis.span ((periodBasis τ hτ).linearIndependent.restrict_scalars' ℤ)).map
    (LinearEquiv.ofEq _ _ (by rw [periodBasis_range]; rfl))

/-- Integer basis vectors, viewed in the ambient complex plane. -/
theorem coe_periodIntegralBasis (τ : ℂ) (hτ : τ.im ≠ 0) :
    (fun i => (periodIntegralBasis τ hτ i : ℂ)) = ![1, τ] := by
  funext i
  simp only [periodIntegralBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.coe_span_apply]
  exact Basis.mk_apply _ _ _

/-- An integral affine change of the second generator gives a period submodule. -/
theorem periodModule_affine_le (τ : ℂ) (m n : ℤ) :
    periodModule ((m : ℂ) + (n : ℂ) * τ) ≤ periodModule τ := by
  intro z hz
  obtain ⟨a, b, rfl⟩ := (mem_periodModule_iff _ _).mp hz
  apply (mem_periodModule_iff _ _).mpr
  refine ⟨a + b * m, b * n, ?_⟩
  push_cast
  ring

/-- The index of an integral affine period sublattice is the absolute value
of the coefficient of the original nonreal period. -/
theorem periodModule_affine_relIndex (τ : ℂ) (hτ : τ.im ≠ 0) (m n : ℤ)
    (hn : n ≠ 0) :
    (periodModule ((m : ℂ) + (n : ℂ) * τ)).toAddSubgroup.relIndex
      (periodModule τ).toAddSubgroup = n.natAbs := by
  have him : ((m : ℂ) + (n : ℂ) * τ).im ≠ 0 := by
    simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
      zero_mul, zero_add, add_zero]
    exact mul_ne_zero (by exact_mod_cast hn) hτ
  let b := periodIntegralBasis τ hτ
  let b' := periodIntegralBasis ((m : ℂ) + (n : ℂ) * τ) him
  let hle := periodModule_affine_le τ m n
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ hle b' b]
  change (b.det (fun i => (⟨b' i, hle (SetLike.coe_mem _)⟩ : periodModule τ))).natAbs =
    n.natAbs
  have hb : ∀ i, (b i : ℂ) = (![1, τ] : Fin 2 → ℂ) i :=
    congrFun (coe_periodIntegralBasis τ hτ)
  have hb' : ∀ i, (b' i : ℂ) =
      (![1, (m : ℂ) + (n : ℂ) * τ] : Fin 2 → ℂ) i :=
    congrFun (coe_periodIntegralBasis _ him)
  have hvec : (fun i => (⟨b' i, hle (SetLike.coe_mem _)⟩ : periodModule τ)) =
      ![b 0, m • b 0 + n • b 1] := by
    funext i
    apply Subtype.ext
    fin_cases i
    · exact (hb' 0).trans (hb 0).symm
    · change (b' 1 : ℂ) = (↑(m • b 0 + n • b 1) : ℂ)
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul, hb', hb]
      change (m : ℂ) + (n : ℂ) * τ = (m : ℂ) * 1 + (n : ℂ) * τ
      ring
  rw [hvec]
  simp [Basis.det_apply, Basis.toMatrix_apply, Matrix.det_fin_two]

/-- Halving the second period gives an overlattice. -/
theorem periodModule_le_half (τ : ℂ) :
    periodModule τ ≤ periodModule (τ / 2) := by
  have heq : 2 * (τ / 2) = τ := by ring
  simpa [heq] using periodModule_affine_le (τ / 2) 0 2

/-- The shifted half-period also gives an overlattice. -/
theorem periodModule_le_shifted_half (τ : ℂ) :
    periodModule τ ≤ periodModule ((τ + 1) / 2) := by
  have hτ : (-1 : ℂ) + 2 * ((τ + 1) / 2) = τ := by ring
  simpa only [Int.cast_neg, Int.cast_one, Int.cast_ofNat, hτ] using
    periodModule_affine_le ((τ + 1) / 2) (-1) 2

/-- The three period parameters in the level-two modular polynomial give one
index-two sublattice and two index-two overlattices. This does not assert
that their homothety classes are distinct or exhaustive. -/
theorem periodModule_two_neighbors_relIndex (τ : ℂ) (hτ : τ.im ≠ 0) :
    (periodModule (2 * τ)).toAddSubgroup.relIndex (periodModule τ).toAddSubgroup = 2 ∧
    (periodModule τ).toAddSubgroup.relIndex (periodModule (τ / 2)).toAddSubgroup = 2 ∧
    (periodModule τ).toAddSubgroup.relIndex
      (periodModule ((τ + 1) / 2)).toAddSubgroup = 2 := by
  constructor
  · simpa using periodModule_affine_relIndex τ hτ 0 2 (by norm_num)
  constructor
  · have him : (τ / 2).im ≠ 0 := by simpa using div_ne_zero hτ (by norm_num : (2 : ℝ) ≠ 0)
    have heq : 2 * (τ / 2) = τ := by ring
    simpa [heq] using periodModule_affine_relIndex (τ / 2) him 0 2 (by norm_num)
  · have him : ((τ + 1) / 2).im ≠ 0 := by
      simpa using div_ne_zero hτ (by norm_num : (2 : ℝ) ≠ 0)
    have heq : (-1 : ℂ) + 2 * ((τ + 1) / 2) = τ := by ring
    simpa [heq] using
      periodModule_affine_relIndex ((τ + 1) / 2) him (-1) 2 (by norm_num)

end BakerHeegnerStark
