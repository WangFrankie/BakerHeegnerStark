/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.LevelTwo

/-!
# The Classical Modular Polynomial of Level `N`

For `N ≥ 1`, let `C(N)` be the set of triples `(a, b, d)` with `ad = N`,
`0 ≤ b < d` and `gcd(a, b, d) = 1`. The classical modular polynomial `Φ_N` is
the polynomial with integer coefficients satisfying
`Φ_N(j(τ), Y) = ∏_{(a,b,d) ∈ C(N)} (Y - j((aτ + b)/d))`; when `N` is not a
square, `Φ_N(X, X)` has leading coefficient `±1` (Cox, *Primes of the form
x² + ny²*, Theorem 11.18).

Polynomial representation for holomorphic level-one functions with growth
`O(jⁿ)`, including their discriminant regularization, is proved locally in
`ModularForms/JInvariant/Polynomial.lean`. `ModularForms/ModularPolynomial/Coefficients.lean` proves holomorphicity
and polynomial j-growth of the actual coefficient functions.
`ModularForms/ModularPolynomial/Modularity.lean` proves modular invariance and constructs
the polynomial over `ℂ`. `ModularForms/ModularPolynomial/Rationality.lean` proves its descent
to `ℤ` using integral q-expansions and finite cyclotomic Galois theory.
`ModularForms/ModularPolynomial/Diagonal.lean` proves the unit diagonal leading coefficient
at nonsquare levels and the unconditional `ModularPolynomialTheorem`.

From it we prove the integrality of `j(τ)` whenever `τ` is a root of a monic
integral quadratic `τ² - tτ + N` with `N` not a square: then `τ / N` is
`SL₂(ℤ)`-equivalent to `τ`, so `j(τ)` is a root of `Φ_N(X, X)`.
-/

open Polynomial
open scoped Polynomial.Bivariate MatrixGroups

namespace BakerHeegnerStark

open ModularForm

/-- The index set `C(N)` of the modular polynomial: triples `(a, b, d)` with
`ad = N`, `b < d` and `gcd(a, b, d) = 1`. -/
def cyclicSublatticeTriples (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
    fun t => t.1 * t.2.2 = N ∧ t.2.1 < t.2.2 ∧ Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1

/-- The point `(aτ + b)/d` attached to a triple `(a, b, d)`. -/
noncomputable def cyclicSublatticePoint (t : ℕ × ℕ × ℕ) (τ : UpperHalfPlane) :
    UpperHalfPlane :=
  UpperHalfPlane.ofComplex ((t.1 * (τ : ℂ) + t.2.1) / t.2.2)

/-- **The classical modular polynomial** (Cox, Theorem 11.18): for every `N ≥ 1`
there is `Φ_N ∈ ℤ[X,Y]` with `Φ_N(j(τ), Y) = ∏_{C(N)} (Y - j((aτ + b)/d))`, and
for nonsquare `N` the leading coefficient of `Φ_N(X, X)` is a unit. -/
def ModularPolynomialTheorem : Prop :=
  ∀ N : ℕ, 0 < N → ∃ Φ : ℤ[X][Y],
    (∀ τ : UpperHalfPlane, aevalAeval (C (jInvariant τ)) X Φ =
      ∏ t ∈ cyclicSublatticeTriples N, (X - C (jInvariant (cyclicSublatticePoint t τ)))) ∧
    (¬ IsSquare N → IsUnit (aevalAeval (X : ℤ[X]) X Φ).leadingCoeff)

theorem mem_cyclicSublatticeTriples {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ} :
    t ∈ cyclicSublatticeTriples N ↔
      t.1 * t.2.2 = N ∧ t.2.1 < t.2.2 ∧ Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1 := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨had, hbd, hgcd⟩
    refine Finset.mem_filter.mpr ⟨?_, had, hbd, hgcd⟩
    obtain ⟨a, b, d⟩ := t
    simp only [Finset.mem_product, Finset.mem_range] at *
    have hd : 0 < d := by omega
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h
        omega
      · exact h
    refine ⟨?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith

/-- The level-two case of `ModularPolynomialTheorem`, from the explicit `Φ₂`. -/
theorem modularPolynomialTheorem_two :
    ∃ Φ : ℤ[X][Y],
      (∀ τ : UpperHalfPlane, aevalAeval (C (jInvariant τ)) X Φ =
        ∏ t ∈ cyclicSublatticeTriples 2, (X - C (jInvariant (cyclicSublatticePoint t τ)))) ∧
      (¬ IsSquare 2 → IsUnit (aevalAeval (X : ℤ[X]) X Φ).leadingCoeff) := by
  refine ⟨modularPolynomialTwo, fun τ => ?_, fun _ => ?_⟩
  · have htriples : cyclicSublatticeTriples 2 = {(1, 0, 2), (1, 1, 2), (2, 0, 1)} := by
      decide
    rw [modularPolynomialTwo_jInvariant_factorization_polynomial, htriples]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    simp only [cyclicSublatticePoint, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, one_mul,
      add_zero, div_one]
    ring
  · have hΦ : aevalAeval (X : ℤ[X]) X modularPolynomialTwo =
        -(X ^ 4 - 2978 * X ^ 3 - 40449375 * X ^ 2 - 17496000000 * X + 157464000000000) := by
      simp only [modularPolynomialTwo, map_add, map_sub, map_mul, map_pow, map_ofNat,
        aevalAeval_X, aevalAeval_Y]
      ring
    have hmonic : (X ^ 4 - 2978 * X ^ 3 - 40449375 * X ^ 2 - 17496000000 * X +
        157464000000000 : ℤ[X]).Monic := by
      monicity!
    rw [hΦ, leadingCoeff_neg, hmonic.leadingCoeff]
    exact isUnit_one.neg

/-- Evaluating `Φ(X, X)` at `x` is the bivariate evaluation at `(x, x)`. -/
theorem aeval_aevalAeval_X_X {A : Type*} [CommRing A] [Algebra ℤ A] (Φ : ℤ[X][Y]) (x : A) :
    aeval x (aevalAeval (X : ℤ[X]) X Φ) = aevalAeval x x Φ := by
  have h := ((aevalAevalEquiv ℤ A).apply_symm_apply
    ((aeval x).comp (aevalAeval (X : ℤ[X]) X))).symm
  rw [aevalAevalEquiv_symm_apply] at h
  simp only [AlgHom.comp_apply, aevalAeval_X, aevalAeval_Y, aeval_X] at h
  exact congrArg (fun f : ℤ[X][Y] →ₐ[ℤ] A => f Φ) h

/-- Evaluating `Φ(C b, X)` at `a` is the bivariate evaluation at `(b, a)`. -/
theorem eval_aevalAeval_C_X (Φ : ℤ[X][Y]) (a b : ℂ) :
    eval a (aevalAeval (C b) X Φ) = aevalAeval b a Φ := by
  have h := ((aevalAevalEquiv ℤ ℂ).apply_symm_apply
    (((aeval a).restrictScalars ℤ).comp (aevalAeval (C b) (X : ℂ[X])))).symm
  rw [aevalAevalEquiv_symm_apply] at h
  simp only [AlgHom.comp_apply, aevalAeval_X, aevalAeval_Y, AlgHom.restrictScalars_apply,
    aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply] at h
  have h' := congrArg (fun f : ℤ[X][Y] →ₐ[ℤ] ℂ => f Φ) h
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, coe_aeval_eq_eval] using h'

/-- If `τ² - tτ + N = 0` with `N > 0`, then `τ / N = 1/(t - τ)` is
`SL₂(ℤ)`-equivalent to `τ`. -/
theorem jInvariant_div_of_quadratic {τ : UpperHalfPlane} {t : ℤ} {N : ℕ} (hN : 0 < N)
    (hτ : (τ : ℂ) ^ 2 - t * τ + N = 0) :
    jInvariant (UpperHalfPlane.ofComplex ((τ : ℂ) / N)) = jInvariant τ := by
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have htτ : (t : ℂ) - τ ≠ 0 := by
    intro h
    have : (τ : ℂ) = t := by linear_combination -h
    have him : (τ : ℂ).im = 0 := by simpa using congrArg Complex.im this
    exact (ne_of_gt τ.im_pos) him
  have hpoint : UpperHalfPlane.ofComplex ((τ : ℂ) / N) =
      ModularGroup.S • (ModularGroup.T ^ (-t) • τ) := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_T_zpow_smul]
    have him : 0 < ((τ : ℂ) / N).im := by
      rw [Complex.div_natCast_im]
      exact div_pos τ.im_pos (by exact_mod_cast hN)
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    change (τ : ℂ) / N = (-(((-t : ℤ) : ℝ) + (τ : ℂ)))⁻¹
    have hrw : -(((-t : ℤ) : ℝ) + (τ : ℂ)) = (t : ℂ) - τ := by
      push_cast
      ring
    rw [hrw]
    apply eq_inv_of_mul_eq_one_left
    field_simp
    linear_combination -hτ
  rw [hpoint, jInvariant_smul, jInvariant_smul]

/-- **Integrality from the modular polynomial.** If `τ` is a root of a monic
integral quadratic `τ² - tτ + N` with `N` not a square, then `j(τ)` is an
algebraic integer. -/
theorem isIntegral_jInvariant_of_quadratic (hΦ : ModularPolynomialTheorem)
    {τ : UpperHalfPlane} {t : ℤ} {N : ℕ} (hN : 0 < N) (hsq : ¬ IsSquare N)
    (hτ : (τ : ℂ) ^ 2 - t * τ + N = 0) : IsIntegral ℤ (jInvariant τ) := by
  obtain ⟨Φ, hfac, hlead⟩ := hΦ N hN
  have hmem : ((1, 0, N) : ℕ × ℕ × ℕ) ∈ cyclicSublatticeTriples N := by
    rw [mem_cyclicSublatticeTriples hN]
    simp only [one_mul, Nat.gcd_zero_right, Nat.gcd_one_left, and_true, true_and]
    exact hN
  have hpoint : jInvariant (cyclicSublatticePoint (1, 0, N) τ) = jInvariant τ := by
    have : cyclicSublatticePoint (1, 0, N) τ = UpperHalfPlane.ofComplex ((τ : ℂ) / N) := by
      simp [cyclicSublatticePoint]
    rw [this, jInvariant_div_of_quadratic hN hτ]
  have hroot : aevalAeval (jInvariant τ) (jInvariant τ) Φ = 0 := by
    have h := congrArg (eval (jInvariant τ)) (hfac τ)
    rw [eval_aevalAeval_C_X, eval_prod] at h
    rw [h]
    exact Finset.prod_eq_zero hmem (by simp [hpoint])
  set P : ℤ[X] := aevalAeval (X : ℤ[X]) X Φ with hP
  have hProot : aeval (jInvariant τ) P = 0 := by
    rw [hP, aeval_aevalAeval_X_X, hroot]
  obtain ⟨u, hu⟩ := hlead (hsq)
  have hmonic : (C (↑u⁻¹ : ℤ) * P).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu]; simp)
  refine ⟨C (↑u⁻¹ : ℤ) * P, hmonic, ?_⟩
  rw [← aeval_def, map_mul, hProot, mul_zero]

end BakerHeegnerStark
