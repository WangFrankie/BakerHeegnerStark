/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.Algebra.QuadraticAlgebra.Matrix
import Mathlib.Data.ZMod.Basic

/-!
# Recovering the level-twenty-four CM commutant

The actual CRT maps to levels three and eight detect equality of residues,
hence the two coordinate equations for the quadratic-generator commutant.
Projective agreement with CM-compatible local matrices therefore recovers
global CM commutation. The unit group modulo twenty-four has exponent two.

These finite residue statements do not assert modular-function evaluation
compatibility with a Galois automorphism.
-/

namespace BakerHeegnerStark

/-- Every unit modulo twenty-four is an involution. -/
theorem zmod_twenty_four_unit_sq (u : (ZMod 24)ˣ) : (u : ZMod 24) ^ 2 = 1 := by
  have h : ∀ x y : ZMod 24, x * y = 1 → x ^ 2 = 1 := by decide +kernel
  exact h u u.inv u.val_inv

/-- Equality modulo twenty-four is detected by the two genuine CRT reductions. -/
theorem zmod_twenty_four_eq_iff_reductions (a b : ZMod 24) :
    a = b ↔
      ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3) a =
        ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3) b ∧
      ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8) a =
        ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8) b := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h₃, h₈⟩
    apply (ZMod.chineseRemainder (by decide : Nat.Coprime 3 8)).injective
    exact Prod.ext h₃ h₈

/-- The CM companion matrix is centralized modulo twenty-four exactly when
it is centralized at both the three- and eight-primary levels. -/
theorem commute_CM_mod_twenty_four_iff_mod_three_eight
    (m : ZMod 24) (A : Matrix (Fin 2) (Fin 2) (ZMod 24)) :
    Commute A !![0, -m; 1, 0] ↔
      Commute (A.map (ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3)))
        !![0, -ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3) m; 1, 0] ∧
      Commute (A.map (ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)))
        !![0, -ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8) m; 1, 0] := by
  have hgen (N : ℕ) (n : ZMod N) :
      Algebra.leftMulMatrix (QuadraticAlgebra.basis (-n) 0) QuadraticAlgebra.omega =
        !![0, -n; 1, 0] := by
    simp [QuadraticAlgebra.leftMulMatrix_eq]
  simp only [← hgen 24 m,
    ← hgen 3 (ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3) m),
    ← hgen 8 (ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8) m),
    QuadraticAlgebra.commute_leftMulMatrix_omega_iff, Matrix.map_apply, zero_mul, add_zero]
  constructor
  · rintro ⟨h₀₁, h₁₁⟩
    constructor <;> constructor <;> simp only [h₀₁, h₁₁, map_mul, map_neg]
  · rintro ⟨⟨h₃₀₁, h₃₁₁⟩, ⟨h₈₀₁, h₈₁₁⟩⟩
    constructor
    · apply (zmod_twenty_four_eq_iff_reductions _ _).mpr
      constructor
      · simpa only [map_mul, map_neg] using h₃₀₁
      · simpa only [map_mul, map_neg] using h₈₀₁
    · exact (zmod_twenty_four_eq_iff_reductions _ _).mpr ⟨h₃₁₁, h₈₁₁⟩

/-- Projectively matching CM-compatible actions at levels three and eight
suffices for the actual level-twenty-four matrix to centralize CM.
Even nonunit scalar multiples preserve commutation, so no extra unit
hypothesis on the two displayed scalars is needed. -/
theorem commute_CM_mod_twenty_four_of_projective_reductions
    (m : ZMod 24) (A : Matrix (Fin 2) (Fin 2) (ZMod 24))
    (B₃ : Matrix (Fin 2) (Fin 2) (ZMod 3)) (B₈ : Matrix (Fin 2) (Fin 2) (ZMod 8))
    (c₃ : ZMod 3) (c₈ : ZMod 8)
    (h₃ : Commute B₃ !![0, -ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3) m; 1, 0])
    (h₈ : Commute B₈ !![0, -ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8) m; 1, 0])
    (hA₃ : A.map (ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3)) = c₃ • B₃)
    (hA₈ : A.map (ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)) = c₈ • B₈) :
    Commute A !![0, -m; 1, 0] := by
  apply (commute_CM_mod_twenty_four_iff_mod_three_eight m A).mpr
  constructor
  · rw [hA₃]
    exact h₃.smul_left c₃
  · rw [hA₈]
    exact h₈.smul_left c₈

end BakerHeegnerStark
