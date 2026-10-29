/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.Modularity

/-!
# The actual modular orbit of the three Weber squares

The existing normalized S and T laws act by a branch permutation and an
integral power of `zeta48²`. Generation of the integral modular group extends
this monomial law to every matrix, including inverses. Reduction of the phase
to a genuine residue representative gives a finite phase-branch description
valid on the entire upper half-plane, not just at a chosen CM point.

These are analytic transformation statements. They do not identify an
arithmetic Galois conjugate of a Weber value.
-/

open Complex UpperHalfPlane
open scoped MatrixGroups

namespace ModularForm

/-- The three actual Weber-square branches, in the order `f², f₁², f₂²`. -/
noncomputable def weberSquareBranch (i : Fin 3) (τ : UpperHalfPlane) : ℂ :=
  ![weberF (τ : ℂ) ^ 2, weberF₁ (τ : ℂ) ^ 2, weberF₂ (τ : ℂ) ^ 2] i

/-- Modular inversion fixes the first branch and exchanges the other two. -/
theorem weberSquareBranch_S (i : Fin 3) (τ : UpperHalfPlane) :
    weberSquareBranch i (ModularGroup.S • τ) =
      weberSquareBranch (Equiv.swap 1 2 i) τ := by
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ)
    simp only [inv_neg, neg_div, one_div]
  simp only [weberSquareBranch, hS]
  fin_cases i <;>
    simp [Equiv.swap_apply_def, weberF_neg_inv τ.im_pos,
      weberF₁_neg_inv τ.im_pos, weberF₂_neg_inv τ.im_pos]

/-- Translation exchanges the first two branches with inverse twenty-fourth-root
phase, and multiplies the third by the square of that root. -/
theorem weberSquareBranch_T (i : Fin 3) (τ : UpperHalfPlane) :
    weberSquareBranch i (ModularGroup.T • τ) =
      (zeta48 ^ 2) ^ (if i = 2 then (2 : ℤ) else -1) *
        weberSquareBranch (Equiv.swap 0 1 i) τ := by
  have hT : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]
    simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_one]
    exact add_comm _ _
  simp only [weberSquareBranch, hT]
  fin_cases i <;>
    simp [Equiv.swap_apply_def, weberF_add_one,
      weberF₁_add_one, weberF₂_add_one, mul_pow, inv_pow, zeta48_sq]

/-- Every integral modular transformation acts monomially on the actual three
branches, with integral powers of the twenty-fourth root. -/
theorem exists_weberSquareBranch_smul (g : SL(2, ℤ)) :
    ∃ (e : Equiv.Perm (Fin 3)) (k : Fin 3 → ℤ), ∀ i τ,
      weberSquareBranch i (g • τ) =
        (zeta48 ^ 2) ^ (k i) * weberSquareBranch (e i) τ := by
  have hζ : (zeta48 ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 zeta48_ne_zero
  have hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ⟨Equiv.swap 1 2, fun _ => 0, by simpa using weberSquareBranch_S⟩
      · exact ⟨Equiv.swap 0 1, fun i => if i = 2 then 2 else -1, weberSquareBranch_T⟩
  | one =>
      exact ⟨Equiv.refl _, fun _ => 0, by intro i τ; simp⟩
  | mul g h _ _ hg hh =>
      obtain ⟨e, k, he⟩ := hg
      obtain ⟨f, l, hf⟩ := hh
      refine ⟨e.trans f, fun i => k i + l (e i), ?_⟩
      intro i τ
      rw [mul_smul, he, hf, zpow_add₀ hζ, mul_assoc]
      rfl
  | inv g _ hg =>
      obtain ⟨e, k, he⟩ := hg
      refine ⟨e.symm, fun i => -k (e.symm i), ?_⟩
      intro i τ
      have h := he (e.symm i) (g⁻¹ • τ)
      rw [smul_inv_smul, e.apply_symm_apply] at h
      calc
        weberSquareBranch i (g⁻¹ • τ) =
            (zeta48 ^ 2) ^ (-k (e.symm i)) *
              ((zeta48 ^ 2) ^ (k (e.symm i)) * weberSquareBranch i (g⁻¹ • τ)) := by
          rw [← mul_assoc, ← zpow_add₀ hζ, neg_add_cancel, zpow_zero, one_mul]
        _ = _ := by rw [← h]

private theorem weberSquarePhase_pow_twenty_four : (zeta48 ^ 2) ^ 24 = 1 := by
  rw [zeta48_sq, ← Complex.exp_nat_mul,
    show ((24 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 24) =
      2 * Real.pi * Complex.I by push_cast; ring,
    Complex.exp_two_pi_mul_I]

private theorem weberSquarePhase_zpow_representative (k : ℤ) :
    (zeta48 ^ 2) ^ k = (zeta48 ^ 2) ^ (k : ZMod 24).val := by
  have hζ : (zeta48 ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 zeta48_ne_zero
  have hd : (24 : ℤ) ∣ k - ((k : ZMod 24).val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (k - ((k : ZMod 24).val : ℤ)) 24).mp
    push_cast
    simp
  obtain ⟨q, hq⟩ := hd
  have hk : k = ((k : ZMod 24).val : ℤ) + 24 * q := by omega
  calc
    (zeta48 ^ 2) ^ k =
        (zeta48 ^ 2) ^ (((k : ZMod 24).val : ℤ) + 24 * q) := congrArg _ hk
    _ = (zeta48 ^ 2) ^ ((k : ZMod 24).val : ℤ) *
        ((zeta48 ^ 2) ^ (24 : ℤ)) ^ q := by rw [zpow_add₀ hζ, zpow_mul]
    _ = _ := by
      simp only [zpow_natCast, zpow_ofNat, weberSquarePhase_pow_twenty_four,
        one_zpow, mul_one]

/-- Every actual modular transform is one of at most seventy-two phase-branch
functions; the finite phase representative works on the whole upper half-plane. -/
theorem exists_weberSquareBranch_smul_finite (g : SL(2, ℤ)) (i : Fin 3) :
    ∃ (r : Fin 24) (j : Fin 3), ∀ τ : UpperHalfPlane,
      weberSquareBranch i (g • τ) =
        (zeta48 ^ 2) ^ r.val * weberSquareBranch j τ := by
  obtain ⟨e, k, h⟩ := exists_weberSquareBranch_smul g
  refine ⟨⟨(k i : ZMod 24).val, ZMod.val_lt _⟩, e i, ?_⟩
  intro τ
  rw [h, weberSquarePhase_zpow_representative]

/-- None of the three actual Weber-square branches vanishes on the upper half-plane. -/
theorem weberSquareBranch_ne_zero (i : Fin 3) (τ : UpperHalfPlane) :
    weberSquareBranch i τ ≠ 0 := by
  fin_cases i
  · exact pow_ne_zero 2 (weberF_ne_zero τ.im_pos)
  · exact pow_ne_zero 2 (weberF₁_ne_zero τ.im_pos)
  · exact pow_ne_zero 2 (weberF₂_ne_zero τ.im_pos)

end ModularForm
