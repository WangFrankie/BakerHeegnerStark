/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.CyclicSublattice.Basic

/-!
# Coefficients of the Cyclic-Sublattice Product

The actual finite product of the cyclic-sublattice j-values has holomorphic
coefficient functions. Every coefficient has cusp growth bounded by
`j ^ (N * (cyclicSublatticeTriples N).card)`. These analytic facts do not
assert modular invariance or the existence of the general modular polynomial.
-/

open UpperHalfPlane ModularForm Filter Complex Asymptotics Polynomial
open scoped Topology Manifold

noncomputable section

namespace BakerHeegnerStark

/-- The monic polynomial whose roots are the actual level-`N`
cyclic-sublattice j-values. -/
def cyclicSublatticePolynomial (N : ℕ) (τ : UpperHalfPlane) : ℂ[X] :=
  ∏ t ∈ cyclicSublatticeTriples N, (X - C (jInvariant (cyclicSublatticePoint t τ)))

/-- Holomorphic roots give holomorphic coefficients of their actual finite root product. -/
theorem mdifferentiable_prod_X_sub_C_coeff {ι : Type*}
    (s : Finset ι) (root : ι → UpperHalfPlane → ℂ) :
    (∀ i ∈ s, MDiff (root i)) → ∀ k : ℕ,
      MDiff (fun τ => (∏ i ∈ s, (X - C (root i τ))).coeff k : UpperHalfPlane → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _ k
      simpa only [Finset.prod_empty] using
        (mdifferentiable_const : MDiff (fun _ : UpperHalfPlane => (1 : ℂ[X]).coeff k))
  | @insert i s hi ih =>
      intro hroot k
      have hrooti := hroot i (Finset.mem_insert_self i s)
      have hroots : ∀ j ∈ s, MDiff (root j) :=
        fun j hj => hroot j (Finset.mem_insert_of_mem hj)
      cases k with
      | zero =>
          simpa only [Finset.prod_insert hi, sub_mul, Polynomial.coeff_sub,
            Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul, zero_sub] using!
            (hrooti.mul (ih hroots 0)).neg
      | succ k =>
          simpa only [Finset.prod_insert hi, Polynomial.coeff_X_sub_C_mul] using!
            (ih hroots k).sub (hrooti.mul (ih hroots (k + 1)))

/-- Uniform polynomial growth of the roots bounds every coefficient of their product. -/
theorem isBigO_prod_X_sub_C_coeff {ι : Type*}
    (s : Finset ι) (root : ι → UpperHalfPlane → ℂ) (g : UpperHalfPlane → ℂ)
    (n : ℕ) (hg : ∀ᶠ τ in atImInfty, 1 ≤ ‖g τ‖) :
    (∀ i ∈ s, root i =O[atImInfty] (fun τ => g τ ^ n)) → ∀ k : ℕ,
      (fun τ => (∏ i ∈ s, (X - C (root i τ))).coeff k)
        =O[atImInfty] (fun τ => g τ ^ (n * s.card)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _ k
      simpa only [Finset.prod_empty, Finset.card_empty, Nat.mul_zero, pow_zero] using
        (isBigO_const_one (F := ℂ) ((1 : ℂ[X]).coeff k) atImInfty)
  | @insert i s hi ih =>
      intro hroot k
      have hrooti := hroot i (Finset.mem_insert_self i s)
      have hroots : ∀ j ∈ s, root j =O[atImInfty] (fun τ => g τ ^ n) :=
        fun j hj => hroot j (Finset.mem_insert_of_mem hj)
      have hraise : (fun τ => g τ ^ (n * s.card))
          =O[atImInfty] (fun τ => g τ ^ (n * (insert i s).card)) := by
        apply IsBigO.of_bound 1
        filter_upwards [hg] with τ hτ
        simp only [norm_pow, one_mul]
        apply pow_le_pow_right₀ hτ
        rw [Finset.card_insert_of_notMem hi]
        exact Nat.mul_le_mul_left n (Nat.le_succ s.card)
      have hmul (k : ℕ) :
          (fun τ => root i τ * (∏ j ∈ s, (X - C (root j τ))).coeff k)
            =O[atImInfty] (fun τ => g τ ^ (n * (insert i s).card)) := by
        convert hrooti.mul (ih hroots k) using 1
        funext τ
        rw [← pow_add, Finset.card_insert_of_notMem hi, Nat.mul_add, Nat.mul_one]
        congr 1
        omega
      cases k with
      | zero =>
          simpa only [Finset.prod_insert hi, sub_mul, Polynomial.coeff_sub,
            Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul, zero_sub] using
            (hmul 0).neg_left
      | succ k =>
          simpa only [Finset.prod_insert hi, Polynomial.coeff_X_sub_C_mul] using
            ((ih hroots k).trans hraise).sub (hmul (k + 1))

/-- Every coefficient of the actual cyclic-sublattice product is holomorphic. -/
theorem mdifferentiable_cyclicSublatticePolynomial_coeff {N : ℕ} (hN : 0 < N)
    (k : ℕ) : MDiff (fun τ => (cyclicSublatticePolynomial N τ).coeff k) := by
  apply mdifferentiable_prod_X_sub_C_coeff
  intro t ht
  have had := ((mem_cyclicSublatticeTriples hN).mp ht).1
  have ha : 0 < t.1 := by
    by_contra h
    have hz : t.1 = 0 := by omega
    simp [hz] at had
    omega
  have hd : 0 < t.2.2 := by
    by_contra h
    have hz : t.2.2 = 0 := by omega
    simp [hz] at had
    omega
  exact mdifferentiable_jInvariant_cyclicSublatticePoint ha hd

/-- A uniform integral j-growth bound for every actual coefficient; no
modular invariance assumption is needed. -/
theorem isBigO_cyclicSublatticePolynomial_coeff {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (fun τ => (cyclicSublatticePolynomial N τ).coeff k)
      =O[atImInfty]
        (fun τ => jInvariant τ ^ (N * (cyclicSublatticeTriples N).card)) := by
  exact isBigO_prod_X_sub_C_coeff (cyclicSublatticeTriples N)
    (fun t τ => jInvariant (cyclicSublatticePoint t τ)) jInvariant N
    eventually_one_le_norm_jInvariant
    (fun _ ht => isBigO_jInvariant_of_mem_cyclicSublatticeTriples hN ht) k

end BakerHeegnerStark
