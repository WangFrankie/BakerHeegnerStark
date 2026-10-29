/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.DiscriminantCoefficients
import BakerHeegnerStark.ModularForms.JInvariant.Basic
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Integral q-Expansions of E₄, the Discriminant, and j

The integer pentagonal series maps to the complex pentagonal series, and the
integer divisor-sum series maps to the actual q-expansion of `E₄`. Euler's
pentagonal-number theorem supplies the analytic bridge needed for the full
integer discriminant series, rather than just finitely many coefficients.
An inverse over `ℤ⟦q⟧` then supplies the full integer series for `qj`; this
series is proved to converge to the actual modular function at every point
of the upper half-plane, with constant coefficient one.
-/

open EisensteinSeries UpperHalfPlane Filter Complex
open scoped ArithmeticFunction.sigma Topology Manifold ModularForm

noncomputable section

namespace PowerSeries

/-- The pentagonal series commutes with every coefficient ring homomorphism. -/
theorem map_pentagonalSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    map f (pentagonalSeries R) = pentagonalSeries S := by
  classical
  ext n
  rw [coeff_map]
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    simp only [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow, map_pow, map_neg, map_one]
  · rw [coeff_pentagonalSeries_eq_zero R hn, coeff_pentagonalSeries_eq_zero S hn, map_zero]

/-- Multiplication of absolutely convergent complex power series agrees with
the formal Cauchy product. Complex summability supplies absolute convergence. -/
theorem hasSum_coeff_mul {P Q : PowerSeries ℂ} {z a b : ℂ}
    (hP : HasSum (fun n : ℕ => P.coeff n * z ^ n) a)
    (hQ : HasSum (fun n : ℕ => Q.coeff n * z ^ n) b) :
    HasSum (fun n : ℕ => (P * Q).coeff n * z ^ n) (a * b) := by
  have hcoeff (n : ℕ) : (P * Q).coeff n * z ^ n =
      ∑ ij ∈ Finset.antidiagonal n,
        (P.coeff ij.1 * z ^ ij.1) * (Q.coeff ij.2 * z ^ ij.2) := by
    rw [coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [← Finset.mem_antidiagonal.mp hij, pow_add]
    ring
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm
    hP.summable.norm hQ.summable.norm).of_norm.hasSum
  have ht := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    hP.summable.norm hQ.summable.norm
  rw [hP.tsum_eq, hQ.tsum_eq] at ht
  have hs' : HasSum (fun n : ℕ => ∑ ij ∈ Finset.antidiagonal n,
      (P.coeff ij.1 * z ^ ij.1) * (Q.coeff ij.2 * z ^ ij.2)) (a * b) :=
    ht.symm ▸ hs
  exact hs'.congr_fun hcoeff

/-- All powers of the formal pentagonal series represent the corresponding
power of the actual analytic Euler function throughout the open unit disk. -/
theorem hasSum_pentagonalSeries_pow (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ((pentagonalSeries ℂ) ^ k).coeff n * z ^ n)
      (eulerFunction z ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    have hfun : (fun n : ℕ => (1 : PowerSeries ℂ).coeff n * z ^ n) =
        fun n => if n = 0 then 1 else 0 := by
      funext n
      by_cases hn : n = 0 <;> simp [hn]
    rw [hfun]
    exact hasSum_ite_eq 0 1
  | succ k ih =>
    simpa only [pow_succ] using hasSum_coeff_mul ih (hasSum_eulerFunction_pentagonalSeries hz)

end PowerSeries

namespace ModularForm

/-- The integer divisor-sum power series whose complex image is `E₄`. -/
def eisensteinFourIntegralQExpansion : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)

theorem qExpansion_E₄_eq_map_int :
    qExpansion 1 E₄ =
      PowerSeries.map (Int.castRingHom ℂ) eisensteinFourIntegralQExpansion := by
  rw [qExpansion_E₄]
  ext n
  simp [eisensteinFourIntegralQExpansion, PowerSeries.coeff_map, PowerSeries.coeff_mk]

theorem eisensteinFourIntegralQExpansion_constantCoeff :
    eisensteinFourIntegralQExpansion.constantCoeff = 1 := by
  simp [eisensteinFourIntegralQExpansion]

/-- The integer unit factor `∏ (1-qⁿ)²⁴` in the discriminant expansion. -/
def discriminantUnitIntegralQExpansion : PowerSeries ℤ :=
  (PowerSeries.pentagonalSeries ℤ) ^ 24

theorem discriminantUnitIntegralQExpansion_constantCoeff :
    discriminantUnitIntegralQExpansion.constantCoeff = 1 := by
  have hp : (PowerSeries.pentagonalSeries ℤ).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.coeff_pentagonalSeries_pentagonal ℤ (0 : ℤ)
  change ((PowerSeries.pentagonalSeries ℤ) ^ 24).constantCoeff = 1
  rw [map_pow, hp, one_pow]

/-- The integer power series for `qj`, formed using an inverse over `ℤ⟦q⟧`
rather than division of complex coefficients. -/
def jInvariantIntegralNumerator : PowerSeries ℤ :=
  eisensteinFourIntegralQExpansion ^ 3 *
    PowerSeries.invOfUnit discriminantUnitIntegralQExpansion 1

theorem discriminantUnit_mul_jInvariantIntegralNumerator :
    discriminantUnitIntegralQExpansion * jInvariantIntegralNumerator =
      eisensteinFourIntegralQExpansion ^ 3 := by
  dsimp only [jInvariantIntegralNumerator]
  rw [mul_left_comm, PowerSeries.mul_invOfUnit _
    1 (by simpa using discriminantUnitIntegralQExpansion_constantCoeff), mul_one]

theorem jInvariantIntegralNumerator_constantCoeff :
    jInvariantIntegralNumerator.constantCoeff = 1 := by
  simp [jInvariantIntegralNumerator, eisensteinFourIntegralQExpansion_constantCoeff]

/-- The full integral discriminant series `q ∏ (1-qⁿ)²⁴`, expressed via the
integer pentagonal series. -/
def discriminantIntegralQExpansion : PowerSeries ℤ :=
  PowerSeries.X * (PowerSeries.pentagonalSeries ℤ) ^ 24

/-- The actual discriminant is `q` times the twenty-fourth power of the
analytic Euler function at `q`. -/
theorem discriminant_eq_q_mul_eulerFunction (τ : UpperHalfPlane) :
    discriminant τ = Function.Periodic.qParam 1 (τ : ℂ) *
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 24 := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hq : ‖q‖ < 1 := Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have heta (n : ℕ) : eta_q n τ = q ^ (n + 1) := by
    rw [eta_q_eq_pow]
    congr 1
    simp [q, Function.Periodic.qParam]
  rw [discriminant_eq_q_prod, eulerFunction_eq_tprod hq]
  change q * (∏' n : ℕ, (1 - eta_q n τ) ^ 24) =
    q * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24
  simp_rw [heta]
  rw [(multipliable_one_sub_pow hq).tprod_pow 24]

/-- Euler's analytic product represents the entire integer discriminant series,
not just any finite truncation of its q-expansion. -/
theorem qExpansion_discriminant_eq_map_int :
    qExpansion 1 discriminant =
      PowerSeries.map (Int.castRingHom ℂ) discriminantIntegralQExpansion := by
  have hmap : PowerSeries.map (Int.castRingHom ℂ) discriminantIntegralQExpansion =
      PowerSeries.X * (PowerSeries.pentagonalSeries ℂ) ^ 24 := by
    simp only [discriminantIntegralQExpansion, map_mul, PowerSeries.map_X, map_pow,
      PowerSeries.map_pentagonalSeries]
  rw [hmap]
  ext m
  symm
  apply ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL
    (f := CuspForm.discriminant) ?_ m
  intro τ
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hq : ‖q‖ < 1 := Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hX : HasSum (fun n : ℕ => (PowerSeries.X : PowerSeries ℂ).coeff n * q ^ n) q := by
    convert hasSum_ite_eq 1 q using 1
    funext n
    by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]
  have hprod := PowerSeries.hasSum_coeff_mul hX
    (PowerSeries.hasSum_pentagonalSeries_pow 24 hq)
  have hΔ : discriminant τ = q * eulerFunction q ^ 24 :=
    discriminant_eq_q_mul_eulerFunction τ
  rw [← hΔ] at hprod
  simpa only [smul_eq_mul, CuspForm.coe_discriminant, q] using hprod

/-- The integer numerator satisfies the exact formal identity attached to
`Δ j = E₄³`. This precedes the separate analytic identification of `qj`. -/
theorem qExpansion_discriminant_mul_jInvariantIntegralNumerator :
    qExpansion 1 discriminant * PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator =
      PowerSeries.X * (qExpansion 1 E₄) ^ 3 := by
  rw [qExpansion_discriminant_eq_map_int, qExpansion_E₄_eq_map_int]
  calc
    PowerSeries.map (Int.castRingHom ℂ) discriminantIntegralQExpansion *
        PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator =
        PowerSeries.map (Int.castRingHom ℂ)
          (discriminantIntegralQExpansion * jInvariantIntegralNumerator) := (map_mul _ _ _).symm
    _ = PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.X * eisensteinFourIntegralQExpansion ^ 3) := by
      congr 1
      change (PowerSeries.X * discriminantUnitIntegralQExpansion) *
        jInvariantIntegralNumerator = PowerSeries.X * eisensteinFourIntegralQExpansion ^ 3
      rw [mul_assoc, discriminantUnit_mul_jInvariantIntegralNumerator]
    _ = PowerSeries.X *
        (PowerSeries.map (Int.castRingHom ℂ) eisensteinFourIntegralQExpansion) ^ 3 := by
      rw [map_mul, PowerSeries.map_X, map_pow]

private theorem qParam_one_mdifferentiable :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam 1 (τ : ℂ)) :=
  (Function.Periodic.differentiable_qParam (h := 1)).mdifferentiable.comp mdifferentiable_coe

private theorem qParam_one_periodic :
    Function.Periodic ((fun τ : UpperHalfPlane => Function.Periodic.qParam 1 (τ : ℂ)) ∘
      UpperHalfPlane.ofComplex) 1 := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro τ
  simp [Function.Periodic.qParam, UpperHalfPlane.coe_vadd, mul_add, Complex.exp_add]

private theorem discriminant_mdifferentiable : MDiff discriminant := by
  simpa only [CuspForm.coe_discriminant] using ModularFormClass.holo CuspForm.discriminant

/-- The unit factor `Δ/q` tends to `1` at the cusp, via the locally uniformly
convergent Euler product. -/
theorem tendsto_discriminant_div_qParam :
    Tendsto (fun τ : UpperHalfPlane => discriminant τ / Function.Periodic.qParam 1 (τ : ℂ))
      atImInfty (𝓝 1) := by
  let G : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - q ^ (n + 1))
  have hG : ContinuousAt G 0 :=
    (differentiableOn_tprod_one_sub_pow.differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simp))).continuousAt
  have ht := (hG.tendsto.comp (qParam_tendsto_atImInfty one_pos)).pow 24
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      G (Function.Periodic.qParam 1 (τ : ℂ)) ^ 24) atImInfty (𝓝 1) := by
    simpa [G] using ht
  convert hlim using 1
  funext τ
  rw [discriminant_eq_q_mul_eulerFunction, mul_div_cancel_left₀ _
    (Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ)),
    eulerFunction_eq_tprod (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)]

/-- The actual principal part of `j` is `q⁻¹` with coefficient `1`. -/
theorem tendsto_qParam_mul_jInvariant :
    Tendsto (fun τ : UpperHalfPlane => Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ)
      atImInfty (𝓝 1) := by
  have hE : Tendsto (E₄ : UpperHalfPlane → ℂ) atImInfty (𝓝 1) := by
    simpa using EisensteinSeries.tendsto_E_atImInfty (k := 4)
  have ht := (hE.pow 3).div tendsto_discriminant_div_qParam (by norm_num : (1 : ℂ) ≠ 0)
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      E₄ τ ^ 3 / (discriminant τ / Function.Periodic.qParam 1 (τ : ℂ)))
      atImInfty (𝓝 1) := by
    change Tendsto (fun τ : UpperHalfPlane =>
      E₄ τ ^ 3 / (discriminant τ / Function.Periodic.qParam 1 (τ : ℂ)))
      atImInfty (𝓝 ((1 : ℂ) ^ 3 / 1)) at ht
    simpa only [one_pow, div_one] using ht
  convert hlim using 1
  funext τ
  rw [jInvariant]
  field_simp

private theorem discriminantUnit_analyticAt_cuspFunction :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : UpperHalfPlane =>
      discriminant τ / Function.Periodic.qParam 1 (τ : ℂ))) 0 := by
  apply analyticAt_cuspFunction_zero one_pos
  · have hper : Function.Periodic (discriminant ∘ UpperHalfPlane.ofComplex) 1 := by
      simpa only [CuspForm.coe_discriminant, Complex.ofReal_one] using
        SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
          one_mem_strictPeriods_SL
    exact hper.div qParam_one_periodic
  · exact discriminant_mdifferentiable.div qParam_one_mdifferentiable
      (fun τ => Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ))
  · exact tendsto_discriminant_div_qParam.isBigO_one ℝ

private theorem regularizedJInvariant_periodic :
    Function.Periodic ((fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ) ∘ UpperHalfPlane.ofComplex) 1 := by
  have hj : Function.Periodic (jInvariant ∘ UpperHalfPlane.ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ => jInvariant_add_one τ
  exact qParam_one_periodic.mul hj

private theorem regularizedJInvariant_analyticAt_cuspFunction :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ)) 0 :=
  analyticAt_cuspFunction_zero one_pos regularizedJInvariant_periodic
    (qParam_one_mdifferentiable.mul mdifferentiable_jInvariant)
    (tendsto_qParam_mul_jInvariant.isBigO_one ℝ)

/-- The analytic unit `Δ/q` has the full integer Euler-product expansion. -/
theorem qExpansion_discriminant_div_qParam_eq_map_int :
    qExpansion 1 (fun τ : UpperHalfPlane =>
      discriminant τ / Function.Periodic.qParam 1 (τ : ℂ)) =
      PowerSeries.map (Int.castRingHom ℂ) discriminantUnitIntegralQExpansion := by
  have hmap : PowerSeries.map (Int.castRingHom ℂ) discriminantUnitIntegralQExpansion =
      (PowerSeries.pentagonalSeries ℂ) ^ 24 := by
    simp only [discriminantUnitIntegralQExpansion, map_pow, PowerSeries.map_pentagonalSeries]
  rw [hmap]
  ext m
  symm
  let : FunLike (UpperHalfPlane → ℂ) UpperHalfPlane ℂ := ⟨id, Function.injective_id⟩
  apply UpperHalfPlane.qExpansion_coeff_unique (F := UpperHalfPlane → ℂ) (h := 1)
    (c := fun n => ((PowerSeries.pentagonalSeries ℂ) ^ 24).coeff n)
    (fun τ : UpperHalfPlane => discriminant τ / Function.Periodic.qParam 1 (τ : ℂ))
    one_pos discriminantUnit_analyticAt_cuspFunction ?_ m
  intro τ
  change HasSum _ (discriminant τ / Function.Periodic.qParam 1 (τ : ℂ))
  rw [discriminant_eq_q_mul_eulerFunction, mul_div_cancel_left₀ _
    (Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ))]
  simpa only [smul_eq_mul] using PowerSeries.hasSum_pentagonalSeries_pow 24
    (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)

/-- The entire q-expansion of the actual holomorphic regularization `qj`
is the image of an integer power series, not a formal candidate alone. -/
theorem qExpansion_qParam_mul_jInvariant_eq_map_int :
    qExpansion 1 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ) =
      PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator := by
  have hU : PowerSeries.map (Int.castRingHom ℂ) discriminantUnitIntegralQExpansion ≠ 0 := by
    intro h
    have hc := congrArg (fun P : PowerSeries ℂ => P.coeff 0) h
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      discriminantUnitIntegralQExpansion_constantCoeff] at hc
    norm_num at hc
  apply mul_right_cancel₀ hU
  have hmul := UpperHalfPlane.qExpansion_mul regularizedJInvariant_analyticAt_cuspFunction
    discriminantUnit_analyticAt_cuspFunction
  have hfun : (fun τ : UpperHalfPlane => Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ) *
      (fun τ : UpperHalfPlane => discriminant τ / Function.Periodic.qParam 1 (τ : ℂ)) =
      fun τ : UpperHalfPlane => E₄ τ ^ 3 := by
    funext τ
    dsimp only [Pi.mul_apply]
    rw [jInvariant]
    field_simp [discriminant_ne_zero τ, Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ)]
  have hE : qExpansion 1 (fun τ : UpperHalfPlane => E₄ τ ^ 3) = (qExpansion 1 E₄) ^ 3 := by
    have hfun : (⇑(E₄.pow 3) : UpperHalfPlane → ℂ) =
        fun τ : UpperHalfPlane => E₄ τ ^ 3 := by
      rw [ModularForm.coe_pow]
      funext τ
      exact Pi.pow_apply _ _ _
    exact (congrArg (qExpansion 1) hfun).symm.trans
      (ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3)
  rw [hfun, hE, qExpansion_discriminant_div_qParam_eq_map_int] at hmul
  have hformal := congrArg (PowerSeries.map (Int.castRingHom ℂ))
    discriminantUnit_mul_jInvariantIntegralNumerator
  rw [map_mul, map_pow, ← qExpansion_E₄_eq_map_int] at hformal
  exact hmul.symm.trans (hformal.symm.trans (mul_comm _ _))

/-- The integer series for `qj` converges to the actual modular function at
every point of the upper half-plane. -/
theorem hasSum_jInvariantIntegralNumerator (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (jInvariantIntegralNumerator.coeff n : ℂ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ) := by
  have h := τ.hasSum_qExpansion one_pos regularizedJInvariant_periodic
    (qParam_one_mdifferentiable.mul mdifferentiable_jInvariant)
    (tendsto_qParam_mul_jInvariant.isBigO_one ℝ)
  rw [qExpansion_qParam_mul_jInvariant_eq_map_int] at h
  simpa only [PowerSeries.coeff_map, smul_eq_mul, Int.coe_castRingHom] using h

/-- The constant term of the actual `qj` expansion is `1`. -/
theorem qExpansion_qParam_mul_jInvariant_constantCoeff :
    (qExpansion 1 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ)).constantCoeff = 1 := by
  rw [qExpansion_qParam_mul_jInvariant_eq_map_int,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, jInvariantIntegralNumerator_constantCoeff, map_one]

end ModularForm
