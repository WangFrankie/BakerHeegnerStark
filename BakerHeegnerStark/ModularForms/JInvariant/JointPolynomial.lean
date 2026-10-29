/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.Coefficients
import BakerHeegnerStark.Algebra.Polynomial.JointOrbit
import BakerHeegnerStark.ModularForms.JInvariant.Polynomial

/-!
# Two coefficient indices of finite joint products

Finite products with polynomial-valued roots preserve holomorphic scalar
coefficients and uniform polynomial growth. Linear auxiliary roots also give a
finite rectangular coefficient support. Weight-zero scalar coefficients can
then be assembled into a trivariate polynomial, retaining their degree bounds
in the innermost variable.
-/

open UpperHalfPlane ModularForm Filter Asymptotics Polynomial
open scoped Topology Manifold MatrixGroups

noncomputable section
namespace BakerHeegnerStark

/-- Holomorphic scalar coefficients of polynomial-valued roots give holomorphic
scalar coefficients of the entire root product. -/
theorem mdifferentiable_prod_X_sub_C_coeff_coeff {ι : Type*}
    (s : Finset ι) (root : ι → UpperHalfPlane → ℂ[X])
    (hroot : ∀ i ∈ s, ∀ l, MDiff (fun τ => (root i τ).coeff l)) :
    ∀ k l : ℕ, MDiff (fun τ =>
      ((∏ i ∈ s, (X - C (root i τ))).coeff k).coeff l : UpperHalfPlane → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro k l
      simpa only [Finset.prod_empty] using
        (mdifferentiable_const : MDiff
          (fun _ : UpperHalfPlane => ((1 : ℂ[X][X]).coeff k).coeff l))
  | @insert i s hi ih =>
      have hs := ih (fun j hj => hroot j (Finset.mem_insert_of_mem hj))
      have hm (k l : ℕ) : MDiff (fun τ =>
          (root i τ * (∏ j ∈ s, (X - C (root j τ))).coeff k).coeff l) := by
        have ht (b : ℕ × ℕ) : MDiff (fun τ =>
            (root i τ).coeff b.1 * ((∏ j ∈ s, (X - C (root j τ))).coeff k).coeff b.2) :=
          (hroot i (Finset.mem_insert_self i s) b.1).mul (hs k b.2)
        convert (MDifferentiable.sum (t := Finset.antidiagonal l) (fun b _ => ht b)) using 1
        funext τ
        simp only [Polynomial.coeff_mul, Finset.sum_apply]
      intro k l
      cases k with
      | zero =>
          simpa only [Finset.prod_insert hi, sub_mul, Polynomial.coeff_sub,
            Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul, zero_sub,
            Polynomial.coeff_neg] using! (hm 0 l).neg
      | succ k =>
          simpa only [Finset.prod_insert hi, Polynomial.coeff_X_sub_C_mul,
            Polynomial.coeff_sub] using! (hs k l).sub (hm (k + 1) l)

/-- A uniform growth exponent for every scalar root coefficient gives the
cardinality-times-exponent bound for every scalar product coefficient. -/
theorem isBigO_prod_X_sub_C_coeff_coeff {ι : Type*}
    (s : Finset ι) (root : ι → UpperHalfPlane → ℂ[X]) (g : UpperHalfPlane → ℂ)
    (n : ℕ) (hg : ∀ᶠ τ in atImInfty, 1 ≤ ‖g τ‖)
    (hroot : ∀ i ∈ s, ∀ l, (fun τ => (root i τ).coeff l)
      =O[atImInfty] (fun τ => g τ ^ n)) :
    ∀ k l, (fun τ => ((∏ i ∈ s, (X - C (root i τ))).coeff k).coeff l)
      =O[atImInfty] (fun τ => g τ ^ (n * s.card)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro k l
      simpa only [Finset.prod_empty, Finset.card_empty, Nat.mul_zero, pow_zero] using
        (isBigO_const_one (F := ℂ) (((1 : ℂ[X][X]).coeff k).coeff l) atImInfty)
  | @insert i s hi ih =>
      have hs := ih (fun j hj => hroot j (Finset.mem_insert_of_mem hj))
      have hraise : (fun τ => g τ ^ (n * s.card))
          =O[atImInfty] (fun τ => g τ ^ (n * (insert i s).card)) := by
        apply IsBigO.of_bound 1
        filter_upwards [hg] with τ hτ
        simp only [norm_pow, one_mul]
        apply pow_le_pow_right₀ hτ
        rw [Finset.card_insert_of_notMem hi]
        exact Nat.mul_le_mul_left n (Nat.le_succ s.card)
      have hm (k l : ℕ) : (fun τ =>
          (root i τ * (∏ j ∈ s, (X - C (root j τ))).coeff k).coeff l)
            =O[atImInfty] (fun τ => g τ ^ (n * (insert i s).card)) := by
        have ht (b : ℕ × ℕ) : (fun τ =>
            (root i τ).coeff b.1 * ((∏ j ∈ s, (X - C (root j τ))).coeff k).coeff b.2)
            =O[atImInfty] (fun τ => g τ ^ (n * (insert i s).card)) := by
          convert (hroot i (Finset.mem_insert_self i s) b.1).mul (hs k b.2) using 1
          funext τ
          rw [← pow_add, Finset.card_insert_of_notMem hi, Nat.mul_add, Nat.mul_one]
          congr 1
          omega
        convert (IsBigO.sum (s := Finset.antidiagonal l) (fun b _ => ht b)) using 1
        funext τ
        simp only [Polynomial.coeff_mul, Finset.sum_apply]
      intro k l
      cases k with
      | zero =>
          simpa only [Finset.prod_insert hi, sub_mul, Polynomial.coeff_sub,
            Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul, zero_sub,
            Polynomial.coeff_neg] using (hm 0 l).neg_left
      | succ k =>
          simpa only [Finset.prod_insert hi, Polynomial.coeff_X_sub_C_mul,
            Polynomial.coeff_sub] using ((hs k l).trans hraise).sub (hm (k + 1) l)

/-- Linear auxiliary roots bound every inner coefficient degree by the number
of factors, independently of the outer coefficient index. -/
theorem natDegree_prod_X_sub_C_coeff_le {ι L : Type*} [CommRing L]
    (s : Finset ι) (root : ι → L[X]) (hroot : ∀ i ∈ s, (root i).natDegree ≤ 1) :
    ∀ k, ((∏ i ∈ s, (X - C (root i))).coeff k).natDegree ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro k
      simp only [Finset.prod_empty, Finset.card_empty]
      by_cases hk : k = 0 <;> simp [Polynomial.coeff_one, hk]
  | @insert i s hi ih =>
      have hs := ih (fun j hj => hroot j (Finset.mem_insert_of_mem hj))
      have hm (k : ℕ) :
          (root i * (∏ j ∈ s, (X - C (root j))).coeff k).natDegree ≤ (insert i s).card := by
        exact Polynomial.natDegree_mul_le.trans (by
          rw [Finset.card_insert_of_notMem hi]
          have hr := hroot i (Finset.mem_insert_self i s)
          have hp := hs k
          omega)
      intro k
      cases k with
      | zero =>
          simpa only [Finset.prod_insert hi, sub_mul, Polynomial.coeff_sub,
            Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul, zero_sub,
            Polynomial.natDegree_neg] using hm 0
      | succ k =>
          simp only [Finset.prod_insert hi, Polynomial.coeff_X_sub_C_mul]
          exact (Polynomial.natDegree_sub_le _ _).trans (max_le
            ((hs k).trans (by simp only [Finset.card_insert_of_notMem hi]; omega))
            (hm (k + 1)))

/-- A joint product has uniformly bounded inner degree, even with repeated roots. -/
theorem natDegree_jointOrbitPolynomial_coeff_le {ι L : Type*}
    [Fintype ι] [CommRing L] (v w : ι → L) (k : ℕ) :
    ((jointOrbitPolynomial v w).coeff k).natDegree ≤ Fintype.card ι := by
  classical
  apply natDegree_prod_X_sub_C_coeff_le
  intro i _
  exact Polynomial.natDegree_add_le_of_degree_le (by simp) <|
    (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le

/-- A finite rectangular family of invariant holomorphic scalar coefficients
assembles into a trivariate polynomial, with a uniform innermost degree bound. -/
theorem exists_trivariate_polynomial_jInvariant_of_isBigO
    (F : UpperHalfPlane → ℂ[X][X]) (d n : ℕ)
    (hsupport : ∀ τ k l, d < k ∨ d < l → ((F τ).coeff k).coeff l = 0)
    (hholo : ∀ k l, MDiff (fun τ => ((F τ).coeff k).coeff l))
    (hgrowth : ∀ k l, (fun τ => ((F τ).coeff k).coeff l)
      =O[atImInfty] (fun τ => jInvariant τ ^ n))
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (γ • τ) = F τ) :
    ∃ Φ : ℂ[X][X][X],
      (∀ τ : UpperHalfPlane,
        Φ.map (Polynomial.mapRingHom (Polynomial.evalRingHom (jInvariant τ))) = F τ) ∧
      ∀ k l, ((Φ.coeff k).coeff l).natDegree ≤ n := by
  classical
  have hc (k l : ℕ) : ∃ P : ℂ[X], P.natDegree ≤ n ∧
      ∀ τ : UpperHalfPlane, ((F τ).coeff k).coeff l = P.eval (jInvariant τ) := by
    let φ : SlashInvariantForm 𝒮ℒ 0 :=
      { toFun := fun τ => ((F τ).coeff k).coeff l
        slash_action_eq' := by
          intro γ hγ
          obtain ⟨γ, rfl⟩ := hγ
          change ((fun τ => ((F τ).coeff k).coeff l) ∣[(0 : ℤ)] γ) =
            (fun τ => ((F τ).coeff k).coeff l)
          funext τ
          simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using
            congrArg (fun p : ℂ[X][X] => (p.coeff k).coeff l) (hinv γ τ) }
    exact exists_polynomial_jInvariant_of_isBigO φ (hholo k l) n (hgrowth k l)
  choose P hdegree hP using hc
  let Q (k : ℕ) : ℂ[X][X] := ∑ l ∈ Finset.range (d + 1), C (P k l) * X ^ l
  let Φ : ℂ[X][X][X] := ∑ k ∈ Finset.range (d + 1), C (Q k) * X ^ k
  have hΦ (k l : ℕ) : (Φ.coeff k).coeff l =
      if k ≤ d ∧ l ≤ d then P k l else 0 := by
    have ho : Φ.coeff k = if k ≤ d then Q k else 0 := by
      dsimp only [Φ]
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
    have hi : (Q k).coeff l = if l ≤ d then P k l else 0 := by
      dsimp only [Q]
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
    rw [ho]
    split_ifs <;> simp_all
  refine ⟨Φ, ?_, ?_⟩
  · intro τ
    ext k l
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom,
      Polynomial.coe_evalRingHom]
    rw [hΦ]
    split_ifs with h
    · exact (hP k l τ).symm
    · simpa using (hsupport τ k l (by omega)).symm
  · intro k l
    rw [hΦ]
    split_ifs
    · exact hdegree k l
    · simp

end BakerHeegnerStark
