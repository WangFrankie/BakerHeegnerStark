/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.FixedMatrixDiscriminant
import Mathlib.Data.Int.GCD

/-!
# Primitive integral quadratic relations

Dividing an integral triple by its positive content gives an actual primitive
triple. For a positive-leading quadratic relation at an upper-half-plane point,
this preserves the root and the positive leading coefficient. The resulting
primitive relation has negative discriminant by nonreality of the root.

Primitivity is the gcd of all three absolute values, not pairwise coprimality.
-/

namespace BakerHeegnerStark

/-- A triple with nonzero first coefficient is a positive natural common factor
 times a primitive integer triple. No signs are imposed on the coefficients. -/
theorem exists_pos_mul_primitive_integer_triple (a b c : ℤ) (ha : a ≠ 0) :
    ∃ (d : ℕ) (a' b' c' : ℤ), 0 < d ∧
      Nat.gcd (Nat.gcd a'.natAbs b'.natAbs) c'.natAbs = 1 ∧
      a = (d : ℤ) * a' ∧ b = (d : ℤ) * b' ∧ c = (d : ℤ) * c' := by
  let d : ℕ := Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs
  have hd : 0 < d :=
    Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr ha))
  have hda : (d : ℤ) ∣ a := Int.ofNat_dvd_left.mpr
    (Nat.dvd_trans (Nat.gcd_dvd_left (Nat.gcd a.natAbs b.natAbs) c.natAbs)
      (Nat.gcd_dvd_left a.natAbs b.natAbs))
  have hdb : (d : ℤ) ∣ b := Int.ofNat_dvd_left.mpr
    (Nat.dvd_trans (Nat.gcd_dvd_left (Nat.gcd a.natAbs b.natAbs) c.natAbs)
      (Nat.gcd_dvd_right a.natAbs b.natAbs))
  have hdc : (d : ℤ) ∣ c :=
    Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_right (Nat.gcd a.natAbs b.natAbs) c.natAbs)
  let a' : ℤ := a / (d : ℤ)
  let b' : ℤ := b / (d : ℤ)
  let c' : ℤ := c / (d : ℤ)
  have ha' : a = (d : ℤ) * a' := (Int.mul_ediv_cancel' hda).symm
  have hb' : b = (d : ℤ) * b' := (Int.mul_ediv_cancel' hdb).symm
  have hc' : c = (d : ℤ) * c' := (Int.mul_ediv_cancel' hdc).symm
  have hcontent : d = d * Nat.gcd (Nat.gcd a'.natAbs b'.natAbs) c'.natAbs := by
    change Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = _
    rw [ha', hb', hc']
    simp only [Int.natAbs_mul, Int.natAbs_natCast, Nat.gcd_mul_left]
  have hprim : Nat.gcd (Nat.gcd a'.natAbs b'.natAbs) c'.natAbs = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hd
    simpa only [mul_one] using hcontent.symm
  exact ⟨d, a', b', c', hd, hprim, ha', hb', hc'⟩

/-- Every positive-leading integral quadratic relation at an upper-half-plane
point admits actual positive-leading primitive coefficients of negative
 discriminant, with the same root. -/
theorem exists_primitive_integer_quadratic (τ : UpperHalfPlane) (a b c : ℤ)
    (ha : 0 < a)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0) :
    ∃ a' b' c' : ℤ, 0 < a' ∧
      Nat.gcd (Nat.gcd a'.natAbs b'.natAbs) c'.natAbs = 1 ∧
      b' ^ 2 - 4 * a' * c' < 0 ∧
      (a' : ℂ) * (τ : ℂ) ^ 2 + (b' : ℂ) * (τ : ℂ) + c' = 0 := by
  obtain ⟨d, a', b', c', hd, hprim, haeq, hbeq, hceq⟩ :=
    exists_pos_mul_primitive_integer_triple a b c (ne_of_gt ha)
  have hdZ : (0 : ℤ) < d := Int.natCast_pos.mpr hd
  have ha' : 0 < a' := Int.pos_of_mul_pos_right (haeq ▸ ha) hdZ
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hprod : (d : ℂ) *
      ((a' : ℂ) * (τ : ℂ) ^ 2 + (b' : ℂ) * (τ : ℂ) + c') = 0 := by
    calc
      (d : ℂ) * ((a' : ℂ) * (τ : ℂ) ^ 2 + (b' : ℂ) * (τ : ℂ) + c') =
          (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c := by
        rw [haeq, hbeq, hceq]
        push_cast
        ring
      _ = 0 := hτ
  have hτ' : (a' : ℂ) * (τ : ℂ) ^ 2 + (b' : ℂ) * (τ : ℂ) + c' = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hdC
  exact ⟨a', b', c', ha', hprim,
    quadratic_discriminant_neg_of_upperHalfPlane_root τ (ne_of_gt ha') hτ', hτ'⟩

end BakerHeegnerStark
