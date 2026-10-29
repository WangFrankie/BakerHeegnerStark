/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Gamma.Rationality
import BakerHeegnerStark.ClassNumberOne.Heegner.CubicField
import BakerHeegnerStark.ClassNumberOne.Heegner.PrimeIdentification
import BakerHeegnerStark.ModularForms.Weber.Bounds
import BakerHeegnerStark.ComplexMultiplication.Weber.ClassInvariant
import BakerHeegnerStark.ModularForms.ModularPolynomial.LevelTwo
import BakerHeegnerStark.ClassNumberOne.InertPrimes

/-!
# Heegner's Proof of the Inert Prime Case

Let `p ≡ 3 (mod 8)`, `p ≠ 3`, be a prime with `h(ℚ(√-p)) = 1`, and let
`𝔣 = 𝔣(√-p)`. The proved modular-polynomial, CM degree, and gamma rationality
theorems, together with the Weber class-invariant hypothesis, give:

* `γ := γ₂((3 + √-p)/2)` is an integer, and hence so is `j((1 + √-p)/2) = γ³`;
* `j(√-p)` is a root of the monic cubic `Φ₂(j((1 + √-p)/2), Y)` over `ℚ`, by the
  proved factorization of the level-two modular polynomial;
* `v = 2/𝔣²` lies in `ℚ(j(√-p))` and `v⁴ = 16/𝔣⁸` is a root of `W³ - γW - 16`.

The proved analytic identity `γ = (256 - 𝔣²⁴)/𝔣¹⁶` and exponential bounds for
`𝔣` give `γ < -15`. Heegner's algebraic step then produces an integral point on
`Y² = 2X(X³ + 1)`, whose classification restricts `γ` to six values, and the
exponential bounds recover `p ∈ {11, 19, 43, 67, 163}`.

`inertPrimeClassification_of_complexMultiplication` is proved with
`WeberClassInvariant` as its sole explicit arithmetic hypothesis. General
modular polynomials, singular-modulus integrality, the class-number degree
bound, and gamma rationality are proved. `classNumberOneClassification`
instantiates the hypothesis with the proved `weberClassInvariant`.
Its arithmetic descent uses the actual rational joint modular relation and
CM torsion action, so the final classification is unconditional.

## Reference

D. A. Cox, *Primes of the form x² + ny²*, 2nd ed., §12.C (Heegner's argument).
-/

open ModularForm IntermediateField Polynomial QuadraticNumberFields
open scoped NumberField Real

namespace BakerHeegnerStark

/-- Under class number one, the normalized gamma value is a rational integer. -/
theorem gamma₂_cmPointShift_eq_intCast
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)] (hp : p.Prime)
    (hp8 : p % 8 = 3) (hp3 : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1) :
    ∃ n : ℤ, gamma₂ (cmPointShift p) = n := by
  have hj := jInvariant_cmPointShift hp.pos
  have hbot : ℚ⟮jInvariant (cmPointShift p)⟯ = ⊥ := by
    rw [hj]
    exact jInvariant_cmPoint_adjoin_eq_bot_of_classNumber_eq_one p (by omega) hclass
  have hnot3 : ¬ 3 ∣ p := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  have hsq : Squarefree (p : ℤ) := Int.squarefree_natCast.mpr hp.squarefree
  have hmem := gammaTwoRationality p hp.pos (by omega) hnot3 hsq
  rw [hbot] at hmem
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hmem
  have hγint := isIntegral_gamma₂_cmPointShift hp.pos (by omega)
  rw [← hq] at hγint
  have hqint : IsIntegral ℤ q := isIntegral_algebraMap_iff.mp hγint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
  refine ⟨n, ?_⟩
  rw [← hq, ← hn]
  simp

/-- If `j((1 + √-p)/2)` is rational, then `j(√-p)` is a root of the monic cubic
`Φ₂(j((1 + √-p)/2), Y)` over `ℚ`; in particular its degree is at most three. -/
theorem jInvariant_sqrtPoint_isIntegral_finrank_le (p : ℕ) (hp : 0 < p) (q : ℚ)
    (hq : jInvariant (cmPoint p) = q) :
    IsIntegral ℚ (jInvariant (sqrtPoint p)) ∧
      Module.finrank ℚ ℚ⟮jInvariant (sqrtPoint p)⟯ ≤ 3 := by
  set t := jInvariant (sqrtPoint p) with ht
  have h2τ : jInvariant (UpperHalfPlane.ofComplex (2 * (cmPoint p : ℂ))) = t := by
    rw [coe_cmPoint hp, show 2 * ((1 + (Real.sqrt p : ℂ) * Complex.I) / 2) =
      1 + (Real.sqrt p : ℂ) * Complex.I by ring]
    exact jInvariant_ofComplex_one_add_sqrt hp
  have hroot := (modularPolynomialTwo_jInvariant_eq_zero_iff (cmPoint p) t).mpr
    (Or.inl h2τ.symm)
  rw [hq, modularPolynomialTwo_eval] at hroot
  let Q : ℚ[X] := X ^ 3 + C (-q ^ 2 + 1488 * q - 162000) * X ^ 2 +
    C (1488 * q ^ 2 + 40773375 * q + 8748000000) * X +
    C (q ^ 3 - 162000 * q ^ 2 + 8748000000 * q - 157464000000000)
  have hQmonic : Q.Monic := by
    simp only [Q]
    monicity!
  have hQ : aeval t Q = 0 := by
    simp only [Q, map_add, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast]
    push_cast
    linear_combination hroot
  have hint : IsIntegral ℚ t := ⟨Q, hQmonic, by rwa [aeval_def] at hQ⟩
  refine ⟨hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint]
  have hQdeg : Q.natDegree = 3 := by
    simp only [Q]
    compute_degree!
  have h := Polynomial.natDegree_le_natDegree
    (minpoly.degree_le_of_ne_zero ℚ t hQmonic.ne_zero hQ)
  omega

/-- An algebraic integer in a field of degree at most three over `ℚ` is a root
of a monic integer cubic. -/
theorem exists_monic_cubic_of_mem_adjoin {t v : ℂ} (ht : IsIntegral ℚ t)
    (hdeg : Module.finrank ℚ ℚ⟮t⟯ ≤ 3) (hv : v ∈ ℚ⟮t⟯) (hvint : IsIntegral ℤ v) :
    ∃ a b c : ℤ, v ^ 3 + a * v ^ 2 + b * v + c = 0 := by
  have : FiniteDimensional ℚ ℚ⟮t⟯ := IntermediateField.adjoin.finiteDimensional ht
  have hminℚ : (minpoly ℚ v).natDegree ≤ 3 := by
    have h := minpoly.natDegree_le (A := ℚ) (⟨v, hv⟩ : ℚ⟮t⟯)
    rw [IntermediateField.minpoly_eq] at h
    exact h.trans hdeg
  have hgauss := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hvint
  have hminℤ : (minpoly ℤ v).natDegree ≤ 3 := by
    rwa [hgauss, Polynomial.natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int]
      at hminℚ
  have hmonic := minpoly.monic hvint
  set P : ℤ[X] := minpoly ℤ v * X ^ (3 - (minpoly ℤ v).natDegree) with hP
  have hPmonic : P.Monic := hmonic.mul (monic_X_pow _)
  have hPdeg : P.natDegree = 3 := by
    rw [hP, hmonic.natDegree_mul (monic_X_pow _), natDegree_X_pow]
    omega
  have hPv : aeval v P = 0 := by
    rw [hP, map_mul, minpoly.aeval, zero_mul]
  have hcoeff : P.coeff 3 = 1 := by
    have := hPmonic.coeff_natDegree
    rwa [hPdeg] at this
  refine ⟨P.coeff 2, P.coeff 1, P.coeff 0, ?_⟩
  rw [aeval_eq_sum_range, hPdeg] at hPv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hcoeff, zsmul_eq_mul,
    pow_zero, pow_one] at hPv
  push_cast at hPv
  linear_combination hPv

/-- The exponential error in the product expansion of `𝔣(i y)` is tiny for
`π y > 10`. -/
theorem weber_product_error_le {y : ℝ} (hy : 10 < π * y) :
    Real.exp (-(π * y)) / (1 - Real.exp (-(π * y)) ^ 2) ≤ 1 / 8000 := by
  set r := Real.exp (-(π * y)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have he := two_point_seven_pow_lt_exp 10 (by norm_num)
  norm_num at he
  have hr1 : r < 1 / 20000 := by
    have h₁ : r < Real.exp (-10) := Real.exp_lt_exp.mpr (by linarith)
    have h₂ : Real.exp (-10) = (Real.exp 10)⁻¹ := Real.exp_neg 10
    have h₃ : (Real.exp 10)⁻¹ < 1 / 20000 := by
      rw [inv_lt_comm₀ (Real.exp_pos 10) (by norm_num)]
      norm_num
      linarith
    linarith
  have hden : 0 < 1 - r ^ 2 := by nlinarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- The actual Heegner fourth power lies in the conductor-two j-field, whose
degree is three. This uses gamma rationality and the rational Weber j-expression,
not the Weber class-invariant hypothesis. -/
private theorem heegnerFourthPower_sqrtPoint_mem_and_finrank
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)] (hp : p.Prime)
    (hp8 : p % 8 = 3) (hp3 : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1) :
    (2 / weberF ((Real.sqrt p : ℂ) * Complex.I) ^ 2) ^ 4 ∈
        ℚ⟮jInvariant (sqrtPoint p)⟯ ∧
      Module.finrank ℚ ℚ⟮jInvariant (sqrtPoint p)⟯ = 3 := by
  obtain ⟨n, hn⟩ := gamma₂_cmPointShift_eq_intCast p hp hp8 hp3 hclass
  have hy : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hp11 : 11 ≤ p := by have := hp.two_le; omega
  have hπy : 10 < π * Real.sqrt p := by
    have h₁₁ : (10 : ℝ) < π * Real.sqrt (11 : ℕ) :=
      lt_pi_mul_sqrt (s := 3.31) (by norm_num) (by norm_num) (by norm_num)
    have hs : Real.sqrt (11 : ℕ) ≤ Real.sqrt p := Real.sqrt_le_sqrt (by exact_mod_cast hp11)
    nlinarith [Real.pi_pos]
  have hshift : cmPointShift p = UpperHalfPlane.ofComplex
      ((((Real.sqrt p : ℝ) : ℂ) * Complex.I + 3) / 2) := by
    rw [cmPointShift, add_comm]
  have hn15 : n < -15 := by
    have h := gamma₂_half_add_three_mul_I_re_lt_neg_fifteen (Real.sqrt p) hy hπy
    rw [← hshift, hn] at h
    exact_mod_cast h
  let v : ℂ := 2 / weberF ((Real.sqrt p : ℂ) * Complex.I) ^ 2
  have hw : (v ^ 4) ^ 3 - n * v ^ 4 - 16 = 0 := by
    have h := weberF_fourthPower_cubic (z := (Real.sqrt p : ℂ) * Complex.I) (by simpa using hy)
    rw [← hshift, hn] at h
    exact h
  have hj : jInvariant (sqrtPoint p) * (v ^ 4) ^ 6 =
      (256 - (v ^ 4) ^ 3) ^ 3 := by
    simpa only [v, coe_sqrtPoint hp.pos] using
      jInvariant_mul_weberFourthPower_pow_six (sqrtPoint p)
  have heq := adjoin_heegnerCubic_root_eq_adjoin_j hn15 hw hj
  refine ⟨heq ▸ mem_adjoin_simple_self ℚ (v ^ 4), ?_⟩
  rw [← heq]
  exact finrank_adjoin_heegnerCubic_root hn15 hw

/-- In the nonexceptional inert class-number-one case, the actual conductor-two
singular modulus generates a field of degree exactly three. The rational
Weber j-expression generates the irreducible Heegner cubic field; no Weber
class-invariant hypothesis or general CM degree axiom is used. -/
theorem jInvariant_sqrtPoint_finrank_eq_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)] (hp : p.Prime)
    (hp8 : p % 8 = 3) (hp3 : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1) :
    Module.finrank ℚ ℚ⟮jInvariant (sqrtPoint p)⟯ = 3 :=
  (heegnerFourthPower_sqrtPoint_mem_and_finrank p hp hp8 hp3 hclass).2

/-- Weber's eighth power belongs to the actual conductor-two j-field.
This does not imply the still-needed membership of Weber's square. -/
theorem weberF_pow_eight_sqrtPoint_mem_adjoin
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact (-(p : ℤ) ≠ 1)] (hp : p.Prime)
    (hp8 : p % 8 = 3) (hp3 : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) = 1) :
    weberF ((Real.sqrt p : ℂ) * Complex.I) ^ 8 ∈ ℚ⟮jInvariant (sqrtPoint p)⟯ := by
  have hw := (heegnerFourthPower_sqrtPoint_mem_and_finrank p hp hp8 hp3 hclass).1
  have hy : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hf : weberF ((Real.sqrt p : ℂ) * Complex.I) ≠ 0 :=
    weberF_ne_zero (by simpa using hy)
  have heq : weberF ((Real.sqrt p : ℂ) * Complex.I) ^ 8 =
      16 / (2 / weberF ((Real.sqrt p : ℂ) * Complex.I) ^ 2) ^ 4 := by
    field_simp [hf]
    ring
  rw [heq]
  exact (ℚ⟮jInvariant (sqrtPoint p)⟯).div_mem (by simp) hw

/-- **Heegner's theorem for inert primes, from Weber's class invariant.**
The explicit `WeberClassInvariant` hypothesis is discharged by the proved
`weberClassInvariant` in the canonical classification below. -/
theorem inertPrimeClassification_of_complexMultiplication
    (hweber : WeberClassInvariant) :
    InertPrimeClassification := by
  intro p _ _ hp hp8 hp3 hclass
  have hp11 : 11 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨n, hn⟩ := gamma₂_cmPointShift_eq_intCast p hp hp8 hp3 hclass
  set y := Real.sqrt p with hy_def
  have hy : 0 < y := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hπy : 10 < π * y := by
    have h₁₁ : (10 : ℝ) < π * Real.sqrt (11 : ℕ) :=
      lt_pi_mul_sqrt (s := 3.31) (by norm_num) (by norm_num) (by norm_num)
    have hs : Real.sqrt (11 : ℕ) ≤ y := Real.sqrt_le_sqrt (by exact_mod_cast hp11)
    nlinarith [Real.pi_pos]
  set f := weberF ((y : ℂ) * Complex.I) with hf_def
  have hshift : cmPointShift p =
      UpperHalfPlane.ofComplex (((y : ℂ) * Complex.I + 3) / 2) := by
    rw [cmPointShift, add_comm]
  -- The analytic identity for the normalized gamma value.
  have hγf : (n : ℂ) = (256 - f ^ 24) / f ^ 16 := by
    rw [← hn, hshift]
    exact gamma₂_half_add_three_eq_weberF (by simpa using hy)
  -- `𝔣(√-p)` is a positive real number.
  set x := f.re with hx_def
  have hfx : f = (x : ℂ) := Complex.ext rfl (by simpa using weberF_mul_I_im y hy)
  have hx0 : 0 < x := weberF_mul_I_re_pos y hy
  set F := x ^ 8 with hF_def
  have hF0 : 0 < F := by positivity
  have hcubic : F ^ 3 + (n : ℝ) * F ^ 2 - 256 = 0 := by
    rw [hfx] at hγf
    have hγx : (n : ℝ) = (256 - x ^ 24) / x ^ 16 := by exact_mod_cast hγf
    have hx16 : x ^ 16 ≠ 0 := by positivity
    rw [hγx]
    field_simp
    ring
  -- Exponential bounds for `F = 𝔣(√-p)⁸`.
  have hlow : Real.exp (π * Real.sqrt p) ≤ F ^ 3 := by
    have h := exp_le_weberF_mul_I_re y hy
    rw [← hx_def] at h
    have h24 := pow_le_pow_left₀ (Real.exp_pos _).le h 24
    rw [← Real.exp_nat_mul] at h24
    rw [hF_def, ← pow_mul]
    convert h24 using 2
    push_cast
    ring
  have hup : F ^ 3 ≤ Real.exp (π * Real.sqrt p + 3 / 1000) := by
    have h := weberF_mul_I_re_le_exp y hy
    rw [← hx_def] at h
    have h24 := pow_le_pow_left₀ hx0.le h 24
    rw [← Real.exp_nat_mul] at h24
    rw [hF_def, ← pow_mul]
    refine h24.trans (Real.exp_le_exp.mpr ?_)
    have herr := weber_product_error_le hπy
    push_cast
    nlinarith
  -- `γ < -15`.
  have hn15 : n < -15 := by
    have h := gamma₂_half_add_three_mul_I_re_lt_neg_fifteen y hy hπy
    rw [← hshift, hn] at h
    exact_mod_cast h
  -- Heegner's quantity `v = 2/𝔣²`.
  set v : ℂ := 2 / f ^ 2 with hv_def
  have hw : (v ^ 4) ^ 3 - n * v ^ 4 - 16 = 0 := by
    have h := weberF_fourthPower_cubic (z := (y : ℂ) * Complex.I) (by simpa using hy)
    rw [← hshift, hn] at h
    exact h
  have hvint : IsIntegral ℤ v :=
    isIntegral_two_div_weberF_sq_sqrtPoint hp.pos (by omega)
  -- The degree bound from the level-two modular polynomial.
  have hjK : jInvariant (cmPoint p) = (((n : ℚ) ^ 3 : ℚ) : ℂ) := by
    rw [← jInvariant_cmPointShift hp.pos, ← gamma₂_cube, hn]
    push_cast
    rfl
  obtain ⟨htint, htdeg⟩ := jInvariant_sqrtPoint_isIntegral_finrank_le p hp.pos _ hjK
  -- Weber's class invariant.
  have hf2 := hweber p hp hp8 hp3 hclass
  have hvmem : v ∈ ℚ⟮jInvariant (sqrtPoint p)⟯ := by
    have h2 : (2 : ℂ) ∈ ℚ⟮jInvariant (sqrtPoint p)⟯ := by simp
    exact IntermediateField.div_mem _ h2 hf2
  obtain ⟨a, b, c, habc⟩ := exists_monic_cubic_of_mem_adjoin htint htdeg hvmem hvint
  obtain ⟨X₀, Y₀, hXY, hnXY⟩ := heegner_point_of_monic_cubic habc hw hn15
  have hnset := gamma_mem_heegnerGammaSet_of_xy_solution hXY hnXY
  rcases eq_of_heegnerGamma_of_exp_bounds hp8 hp11 hF0 hlow hup hcubic hnset with
    h | h | h | h | h <;> subst h <;> simp [heegnerSet]

/-- The complete classification, proved from the explicit Weber
class-invariant statement taken as an explicit hypothesis. -/
theorem classNumberOneClassification_of_complexMultiplication
    (hweber : WeberClassInvariant) :
    ClassNumberOneClassification :=
  classNumberOneClassification_iff_inertPrimeClassification.mpr
    (inertPrimeClassification_of_complexMultiplication hweber)

/-- The unconditional Baker-Heegner-Stark classification. The actual Weber
class invariant follows from rational joint relations and CM torsion action.
`scripts/check_axioms.lean` audits this theorem using only the standard axioms. -/
theorem classNumberOneClassification : ClassNumberOneClassification :=
  classNumberOneClassification_of_complexMultiplication weberClassInvariant

end BakerHeegnerStark
