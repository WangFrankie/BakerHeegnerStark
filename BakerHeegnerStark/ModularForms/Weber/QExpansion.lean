import BakerHeegnerStark.ModularForms.Weber.Modularity
import BakerHeegnerStark.ModularForms.Weber.Identity
import BakerHeegnerStark.ModularForms.ModularPolynomial.QExpansion
import BakerHeegnerStark.ModularForms.QExpansion.Identity

/-!
# The Integral q-Expansion of the Actual Weber Square

The actual width-twenty-four regularization of the Weber square is
`E(-q₂)² / E(q₁)²`, with its phase fixed by the eta quotient itself.
The numerator over the integers is obtained by rescaling the pentagonal series
and inverting its width-two Euler denominator. Its constant coefficient is one.
Both the width-two series and its width-twenty-four expansion converge at every
upper-half-plane point and identify the actual q-expansion, not a finite truncation.
No CM or class-invariant field-membership hypothesis is used.
-/

open BakerHeegnerStark UpperHalfPlane Filter Complex
open scoped Topology Manifold ModularForm
noncomputable section
namespace ModularForm

/-- The integer series `E(q²)²` in the width-two parameter. -/
def weberSquareDenominatorIntegralQExpansion : PowerSeries ℤ :=
  PowerSeries.expand 2 (by decide) ((PowerSeries.pentagonalSeries ℤ) ^ 2)

/-- The full integer series for the actual normalized Weber square. -/
def weberSquareIntegralNumerator : PowerSeries ℤ :=
  PowerSeries.rescale (-1) ((PowerSeries.pentagonalSeries ℤ) ^ 2) *
    PowerSeries.invOfUnit weberSquareDenominatorIntegralQExpansion 1

/-- The Euler denominator is a formal unit with constant coefficient one. -/
theorem weberSquareDenominatorIntegralQExpansion_constantCoeff :
    weberSquareDenominatorIntegralQExpansion.constantCoeff = 1 := by
  have hp : (PowerSeries.pentagonalSeries ℤ).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.coeff_pentagonalSeries_pentagonal ℤ (0 : ℤ)
  simp [weberSquareDenominatorIntegralQExpansion, hp]

/-- The integer numerator satisfies its exact formal Euler-product equation. -/
theorem weberSquareDenominator_mul_integralNumerator :
    weberSquareDenominatorIntegralQExpansion * weberSquareIntegralNumerator =
      PowerSeries.rescale (-1) ((PowerSeries.pentagonalSeries ℤ) ^ 2) := by
  dsimp only [weberSquareIntegralNumerator]
  rw [mul_left_comm, PowerSeries.mul_invOfUnit _ 1
    (by simpa using weberSquareDenominatorIntegralQExpansion_constantCoeff), mul_one]

/-- The normalized integer Weber-square series has principal coefficient one. -/
theorem weberSquareIntegralNumerator_constantCoeff :
    weberSquareIntegralNumerator.constantCoeff = 1 := by
  have hp : (PowerSeries.pentagonalSeries ℤ).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.coeff_pentagonalSeries_pentagonal ℤ (0 : ℤ)
  have hr : (PowerSeries.rescale (-1) (PowerSeries.pentagonalSeries ℤ)).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
      pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff, hp]
  simp [weberSquareIntegralNumerator, hr]

/-- The actual eta square has its width-twelve exponential factor. -/
theorem eta_sq_eq_qParam_twelve_mul_eulerFunction (τ : UpperHalfPlane) :
    eta (τ : ℂ) ^ 2 = Function.Periodic.qParam 12 (τ : ℂ) *
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2 := by
  have hq : Function.Periodic.qParam 24 (τ : ℂ) ^ 2 =
      Function.Periodic.qParam 12 (τ : ℂ) := by
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  change (Function.Periodic.qParam 24 (τ : ℂ) *
    ∏' n : ℕ, (1 - Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ 2 = _
  rw [mul_pow, hq, eulerFunction_eq_tprod
    (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)]

/-- The analytic Euler denominator does not vanish on the upper half-plane. -/
theorem eulerFunction_qParam_one_sq_ne_zero (τ : UpperHalfPlane) :
    eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2 ≠ 0 := by
  intro hzero
  have hη : eta (τ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (eta_ne_zero τ.im_pos)
  apply hη
  rw [eta_sq_eq_qParam_twelve_mul_eulerFunction, hzero, mul_zero]

/-- The normalized actual Weber square satisfies the analytic Euler-product equation. -/
theorem qParam_twentyFour_mul_weberF_sq_mul_eulerFunction (τ : UpperHalfPlane) :
    (Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) *
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2 =
      eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2 := by
  let σ := cyclicSublatticePoint (1, 1, 2) τ
  have hσ : (σ : ℂ) = ((τ : ℂ) + 1) / 2 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, one_mul] using
      cyclicSublatticePoint_coe (t := (1, 1, 2)) (by decide) (by decide) τ
  have hqσ : Function.Periodic.qParam 1 (σ : ℂ) =
      -Function.Periodic.qParam 2 (τ : ℂ) := by
    simp only [Function.Periodic.qParam, hσ]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (((τ : ℂ) + 1) / 2) / ((1 : ℝ) : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / ((2 : ℝ) : ℂ) +
          (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hphase : Function.Periodic.qParam 24 (τ : ℂ) * (zeta48 ^ 2)⁻¹ *
      Function.Periodic.qParam 12 (σ : ℂ) / Function.Periodic.qParam 12 (τ : ℂ) = 1 := by
    simp only [Function.Periodic.qParam, zeta48, hσ, ← Complex.exp_nat_mul,
      ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_sub]
    convert Complex.exp_zero using 1
    congr 1
    push_cast
    ring
  have hE0 : eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ≠ 0 := by
    intro h
    apply eulerFunction_qParam_one_sq_ne_zero τ
    simp [h]
  calc
    (Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) *
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2 =
      (Function.Periodic.qParam 24 (τ : ℂ) * (zeta48 ^ 2)⁻¹ *
        Function.Periodic.qParam 12 (σ : ℂ) / Function.Periodic.qParam 12 (τ : ℂ)) *
          eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2 := by
      rw [weberF, mul_pow, div_pow, inv_pow, ← hσ,
        eta_sq_eq_qParam_twelve_mul_eulerFunction σ,
        eta_sq_eq_qParam_twelve_mul_eulerFunction τ, hqσ]
      field_simp [Function.Periodic.qParam_ne_zero (h := 12) (τ : ℂ), hE0, zeta48_ne_zero]
    _ = _ := by rw [hphase, one_mul]

/-- The actual normalized Weber square is the quotient of its analytic Euler factors. -/
theorem qParam_twentyFour_mul_weberF_sq_eq_div_eulerFunction (τ : UpperHalfPlane) :
    Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2 =
      eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2 /
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2 :=
  (eq_div_iff (eulerFunction_qParam_one_sq_ne_zero τ)).mpr
    (qParam_twentyFour_mul_weberF_sq_mul_eulerFunction τ)

private theorem weber_qParam_one_eq_two_sq (z : ℂ) :
    Function.Periodic.qParam 1 z = Function.Periodic.qParam 2 z ^ 2 := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem weber_qParam_two_periodic :
    Function.Periodic ((fun τ : UpperHalfPlane => Function.Periodic.qParam 2 (τ : ℂ)) ∘
      UpperHalfPlane.ofComplex) 2 := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro τ
  simp [Function.Periodic.qParam, UpperHalfPlane.coe_vadd, mul_add, add_div, Complex.exp_add]

private theorem weberSquareDenominator_periodic :
    Function.Periodic ((fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2) ∘
        UpperHalfPlane.ofComplex) 2 := by
  intro z
  simpa only [Function.comp_apply, weber_qParam_one_eq_two_sq] using
    congrArg (fun q : ℂ => eulerFunction (q ^ 2) ^ 2) (weber_qParam_two_periodic z)

private theorem weberSquareEulerNumerator_periodic :
    Function.Periodic ((fun τ : UpperHalfPlane =>
      eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2) ∘
        UpperHalfPlane.ofComplex) 2 := by
  intro z
  exact congrArg (fun q : ℂ => eulerFunction (-q) ^ 2) (weber_qParam_two_periodic z)

/-- The actual width-twenty-four regularization has the shorter period two. -/
theorem periodic_qParam_twentyFour_mul_weberF_sq :
    Function.Periodic ((fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) ∘
        UpperHalfPlane.ofComplex) 2 := by
  intro z
  simpa only [Function.comp_apply, Pi.div_apply,
    qParam_twentyFour_mul_weberF_sq_eq_div_eulerFunction] using
    (weberSquareEulerNumerator_periodic.div weberSquareDenominator_periodic) z

private theorem weber_qParam_mdifferentiable (h : ℝ) :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam h (τ : ℂ)) :=
  (Function.Periodic.differentiable_qParam (h := h)).mdifferentiable.comp mdifferentiable_coe

/-- The normalized actual Weber square is holomorphic on the whole upper half-plane. -/
theorem mdifferentiable_qParam_twentyFour_mul_weberF_sq :
    MDiff (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) := by
  have hW : MDiff (fun τ : UpperHalfPlane => weberF (τ : ℂ)) :=
    fun τ => (analyticOnNhd_weberF (τ : ℂ) τ.im_pos).differentiableAt.mdifferentiableAt.comp
      τ τ.mdifferentiable_coe
  exact (weber_qParam_mdifferentiable 24).mul (hW.pow 2)

private theorem weberSquareDenominator_mdifferentiable :
    MDiff (fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2) := by
  have hη : MDiff (fun τ : UpperHalfPlane => eta (τ : ℂ)) :=
    fun τ => (differentiableAt_eta_of_mem_upperHalfPlaneSet τ.im_pos).mdifferentiableAt.comp
      τ τ.mdifferentiable_coe
  have hfun : (fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2) =
        fun τ : UpperHalfPlane => eta (τ : ℂ) ^ 2 / Function.Periodic.qParam 12 (τ : ℂ) := by
    funext τ
    rw [eta_sq_eq_qParam_twelve_mul_eulerFunction, mul_div_cancel_left₀ _
      (Function.Periodic.qParam_ne_zero (h := 12) (τ : ℂ))]
  rw [hfun]
  exact (hη.pow 2).div (weber_qParam_mdifferentiable 12)
    (fun τ => Function.Periodic.qParam_ne_zero (h := 12) (τ : ℂ))

private theorem weberSquareEulerNumerator_mdifferentiable :
    MDiff (fun τ : UpperHalfPlane =>
      eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2) := by
  have hfun : (fun τ : UpperHalfPlane =>
      eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2) =
        (fun τ : UpperHalfPlane => Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) *
          (fun τ : UpperHalfPlane => eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2) := by
    funext τ
    exact (qParam_twentyFour_mul_weberF_sq_mul_eulerFunction τ).symm
  rw [hfun]
  exact mdifferentiable_qParam_twentyFour_mul_weberF_sq.mul weberSquareDenominator_mdifferentiable

/-- Euler's analytic function tends to one at zero through its convergent product. -/
theorem tendsto_eulerFunction_zero :
    Tendsto (eulerFunction : ℂ → ℂ) (𝓝 0) (𝓝 1) := by
  let G : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - q ^ (n + 1))
  have hG : ContinuousAt G 0 :=
    (differentiableOn_tprod_one_sub_pow.differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simp))).continuousAt
  have hlim : Tendsto G (𝓝 0) (𝓝 1) := by simpa [G] using hG.tendsto
  have heq : G =ᶠ[𝓝 (0 : ℂ)] eulerFunction := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with q hq
    symm
    apply eulerFunction_eq_tprod
    simpa using hq
  exact Filter.Tendsto.congr' heq hlim

private theorem weberSquareDenominator_tendsto :
    Tendsto (fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2) atImInfty (𝓝 1) := by
  simpa using (tendsto_eulerFunction_zero.comp (qParam_tendsto_atImInfty one_pos)).pow 2

private theorem weberSquareEulerNumerator_tendsto :
    Tendsto (fun τ : UpperHalfPlane =>
      eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2) atImInfty (𝓝 1) := by
  have hneg : Tendsto (fun τ : UpperHalfPlane => -Function.Periodic.qParam 2 (τ : ℂ))
      atImInfty (𝓝 (0 : ℂ)) := by
    simpa using (qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 2)).neg
  simpa using (tendsto_eulerFunction_zero.comp hneg).pow 2

/-- The actual regularization has principal coefficient one at the cusp. -/
theorem tendsto_qParam_twentyFour_mul_weberF_sq :
    Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) atImInfty (𝓝 1) := by
  have ht := weberSquareEulerNumerator_tendsto.div weberSquareDenominator_tendsto
    (by norm_num : (1 : ℂ) ≠ 0)
  have hlim : Tendsto (fun τ : UpperHalfPlane =>
      eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2 /
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2) atImInfty (𝓝 1) := by
    change Tendsto (fun τ : UpperHalfPlane =>
      eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2 /
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2)
      atImInfty (𝓝 ((1 : ℂ) / 1)) at ht
    simpa only [div_one] using ht
  simpa only [qParam_twentyFour_mul_weberF_sq_eq_div_eulerFunction] using hlim

private theorem weberSquareDenominator_analyticAt_cuspFunction :
    AnalyticAt ℂ (cuspFunction 2 (fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2)) 0 :=
  analyticAt_cuspFunction_zero (by norm_num) weberSquareDenominator_periodic
    weberSquareDenominator_mdifferentiable (weberSquareDenominator_tendsto.isBigO_one ℝ)

private theorem weberSquareEulerNumerator_analyticAt_cuspFunction :
    AnalyticAt ℂ (cuspFunction 2 (fun τ : UpperHalfPlane =>
      eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2)) 0 :=
  analyticAt_cuspFunction_zero (by norm_num) weberSquareEulerNumerator_periodic
    weberSquareEulerNumerator_mdifferentiable (weberSquareEulerNumerator_tendsto.isBigO_one ℝ)

private theorem regularizedWeberSquare_analyticAt_cuspFunction :
    AnalyticAt ℂ (cuspFunction 2 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2)) 0 :=
  analyticAt_cuspFunction_zero (by norm_num) periodic_qParam_twentyFour_mul_weberF_sq
    mdifferentiable_qParam_twentyFour_mul_weberF_sq
    (tendsto_qParam_twentyFour_mul_weberF_sq.isBigO_one ℝ)

/-- The width-two Euler denominator has its full integer expansion. -/
theorem qExpansion_weberSquareDenominator_eq_map_int :
    qExpansion 2 (fun τ : UpperHalfPlane =>
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2) =
        PowerSeries.map (Int.castRingHom ℂ) weberSquareDenominatorIntegralQExpansion := by
  have hmap : PowerSeries.map (Int.castRingHom ℂ) weberSquareDenominatorIntegralQExpansion =
      PowerSeries.expand 2 (by decide) ((PowerSeries.pentagonalSeries ℂ) ^ 2) := by
    simp only [weberSquareDenominatorIntegralQExpansion, PowerSeries.map_expand,
      map_pow, PowerSeries.map_pentagonalSeries]
  rw [hmap]
  ext m
  symm
  apply UpperHalfPlane.qExpansion_coeff_unique_unbundled (by norm_num : (0 : ℝ) < 2)
    (fun τ => eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2)
    (fun n => (PowerSeries.expand 2 (by decide)
      ((PowerSeries.pentagonalSeries ℂ) ^ 2)).coeff n)
    weberSquareDenominator_analyticAt_cuspFunction
  intro τ
  apply hasSum_powerSeries_expand (by decide)
  simpa only [weber_qParam_one_eq_two_sq, pow_mul] using
    PowerSeries.hasSum_pentagonalSeries_pow 2
      (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)

/-- Rescaling the integer pentagonal series gives the actual signed Euler numerator. -/
theorem qExpansion_weberSquareEulerNumerator_eq_map_int :
    qExpansion 2 (fun τ : UpperHalfPlane =>
      eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2) =
        PowerSeries.map (Int.castRingHom ℂ)
          (PowerSeries.rescale (-1) ((PowerSeries.pentagonalSeries ℤ) ^ 2)) := by
  have hmap : PowerSeries.map (Int.castRingHom ℂ)
      (PowerSeries.rescale (-1) ((PowerSeries.pentagonalSeries ℤ) ^ 2)) =
        PowerSeries.rescale (-1) ((PowerSeries.pentagonalSeries ℂ) ^ 2) := by
    rw [← PowerSeries.rescale_map]
    simp only [map_neg, map_one, map_pow, PowerSeries.map_pentagonalSeries]
  rw [hmap]
  ext m
  symm
  apply UpperHalfPlane.qExpansion_coeff_unique_unbundled (by norm_num : (0 : ℝ) < 2)
    (fun τ => eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2)
    (fun n => (PowerSeries.rescale (-1) ((PowerSeries.pentagonalSeries ℂ) ^ 2)).coeff n)
    weberSquareEulerNumerator_analyticAt_cuspFunction
  intro τ
  have hnorm : ‖-Function.Periodic.qParam 2 (τ : ℂ)‖ < 1 := by
    simpa only [norm_neg] using
      Function.Periodic.norm_qParam_lt_one (by norm_num : (0 : ℝ) < 2) τ.im_pos
  have hs := PowerSeries.hasSum_pentagonalSeries_pow 2 hnorm
  convert hs using 1
  funext n
  rw [PowerSeries.coeff_rescale,
    show -Function.Periodic.qParam 2 (τ : ℂ) =
      (-1 : ℂ) * Function.Periodic.qParam 2 (τ : ℂ) by ring, mul_pow]
  ring

/-- The actual normalized Weber square has the complete integer width-two expansion. -/
theorem qExpansion_qParam_twentyFour_mul_weberF_sq_eq_map_int :
    qExpansion 2 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) =
        PowerSeries.map (Int.castRingHom ℂ) weberSquareIntegralNumerator := by
  have hU : PowerSeries.map (Int.castRingHom ℂ)
      weberSquareDenominatorIntegralQExpansion ≠ 0 := by
    intro hzero
    have hc := congrArg (fun P : PowerSeries ℂ => P.coeff 0) hzero
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      weberSquareDenominatorIntegralQExpansion_constantCoeff] at hc
    norm_num at hc
  apply mul_right_cancel₀ hU
  have hmul := UpperHalfPlane.qExpansion_mul regularizedWeberSquare_analyticAt_cuspFunction
    weberSquareDenominator_analyticAt_cuspFunction
  have hfun : (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) *
        (fun τ : UpperHalfPlane => eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2) =
      (fun τ : UpperHalfPlane => eulerFunction (-Function.Periodic.qParam 2 (τ : ℂ)) ^ 2) := by
    funext τ
    exact qParam_twentyFour_mul_weberF_sq_mul_eulerFunction τ
  rw [hfun, qExpansion_weberSquareDenominator_eq_map_int,
    qExpansion_weberSquareEulerNumerator_eq_map_int] at hmul
  have hformal := congrArg (PowerSeries.map (Int.castRingHom ℂ))
    weberSquareDenominator_mul_integralNumerator
  rw [map_mul] at hformal
  exact hmul.symm.trans (hformal.symm.trans (mul_comm _ _))

/-- The integer width-two series converges to the actual regularization everywhere. -/
theorem hasSum_weberSquareIntegralNumerator (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (weberSquareIntegralNumerator.coeff n : ℂ) *
      Function.Periodic.qParam 2 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) := by
  have hs := τ.hasSum_qExpansion (by norm_num : (0 : ℝ) < 2)
    periodic_qParam_twentyFour_mul_weberF_sq mdifferentiable_qParam_twentyFour_mul_weberF_sq
    (tendsto_qParam_twentyFour_mul_weberF_sq.isBigO_one ℝ)
  rw [qExpansion_qParam_twentyFour_mul_weberF_sq_eq_map_int] at hs
  simpa only [PowerSeries.coeff_map, smul_eq_mul, Int.coe_castRingHom] using hs

/-- The actual width-two q-expansion has constant coefficient one. -/
theorem qExpansion_qParam_twentyFour_mul_weberF_sq_constantCoeff :
    (qExpansion 2 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2)).constantCoeff = 1 := by
  rw [qExpansion_qParam_twentyFour_mul_weberF_sq_eq_map_int,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, weberSquareIntegralNumerator_constantCoeff, map_one]

/-- The integer expansion in the width-twenty-four variable, with inserted zero coefficients. -/
def weberSquareIntegralQExpansion : PowerSeries ℤ :=
  PowerSeries.expand 12 (by decide) weberSquareIntegralNumerator

/-- The integer width-twenty-four expansion has principal coefficient one. -/
theorem weberSquareIntegralQExpansion_constantCoeff :
    weberSquareIntegralQExpansion.constantCoeff = 1 := by
  simp [weberSquareIntegralQExpansion, weberSquareIntegralNumerator_constantCoeff]

private theorem weber_qParam_two_eq_twentyFour_pow_twelve (z : ℂ) :
    Function.Periodic.qParam 2 z = Function.Periodic.qParam 24 z ^ 12 := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The full integer width-twenty-four series converges at every upper-half-plane point. -/
theorem hasSum_weberSquareIntegralQExpansion (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (weberSquareIntegralQExpansion.coeff n : ℂ) *
      Function.Periodic.qParam 24 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) := by
  have hs : HasSum (fun n : ℕ =>
      (PowerSeries.expand 12 (by decide)
        (PowerSeries.map (Int.castRingHom ℂ) weberSquareIntegralNumerator)).coeff n *
          Function.Periodic.qParam 24 (τ : ℂ) ^ n)
        (Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) := by
    apply hasSum_powerSeries_expand (by decide)
    simpa only [PowerSeries.coeff_map, Int.coe_castRingHom,
      weber_qParam_two_eq_twentyFour_pow_twelve, pow_mul] using
      hasSum_weberSquareIntegralNumerator τ
  have hmap := PowerSeries.map_expand (p := 12) (hp := by decide)
    (Int.castRingHom ℂ) weberSquareIntegralNumerator
  rw [← hmap] at hs
  simpa only [weberSquareIntegralQExpansion, PowerSeries.coeff_map, Int.coe_castRingHom] using hs

private theorem regularizedWeberSquare_periodic_twentyFour :
    Function.Periodic ((fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) ∘
        UpperHalfPlane.ofComplex) 24 := by
  convert periodic_qParam_twentyFour_mul_weberF_sq.nat_mul 12 using 1
  norm_num

private theorem regularizedWeberSquare_analyticAt_cuspFunction_twentyFour :
    AnalyticAt ℂ (cuspFunction 24 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2)) 0 :=
  analyticAt_cuspFunction_zero (by norm_num) regularizedWeberSquare_periodic_twentyFour
    mdifferentiable_qParam_twentyFour_mul_weberF_sq
    (tendsto_qParam_twentyFour_mul_weberF_sq.isBigO_one ℝ)

/-- The actual width-twenty-four expansion is the image of the complete integer series. -/
theorem qExpansion_twentyFour_regularized_weberF_sq_eq_map_int :
    qExpansion 24 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2) =
        PowerSeries.map (Int.castRingHom ℂ) weberSquareIntegralQExpansion := by
  ext m
  rw [PowerSeries.coeff_map]
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique_unbundled (by norm_num : (0 : ℝ) < 24)
    (fun τ => Function.Periodic.qParam 24 (τ : ℂ) * weberF (τ : ℂ) ^ 2)
    (fun n => (weberSquareIntegralQExpansion.coeff n : ℂ))
    regularizedWeberSquare_analyticAt_cuspFunction_twentyFour
    hasSum_weberSquareIntegralQExpansion m

end ModularForm
end
