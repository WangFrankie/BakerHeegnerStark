import BakerHeegnerStark.ModularForms.Weber.QExpansion

/-!
# Integral q-expansions of the other Weber squares

The two eta quotients have different, phase-normalized integral expansions.
The first is the sign rescaling of the Weber-square series; the second is
`2 X³` times the width-twenty-four expansion of `E(q²)² / E(q)²`.
Both full series converge to the actual eta quotients throughout the upper
half-plane. The distinguishing coefficients are consequences of these complete
identifications.
-/

open BakerHeegnerStark UpperHalfPlane Filter Complex
open scoped Topology Manifold ModularForm
noncomputable section
namespace ModularForm

/-- The full integer width-two series for the first Weber square. -/
def weberF₁SquareIntegralNumerator : PowerSeries ℤ :=
  PowerSeries.rescale (-1) weberSquareIntegralNumerator

/-- The full integer width-twenty-four series for the first Weber square. -/
def weberF₁SquareIntegralQExpansion : PowerSeries ℤ :=
  PowerSeries.expand 12 (by decide) weberF₁SquareIntegralNumerator

/-- The integral Euler quotient underlying the second Weber square. -/
def weberF₂SquareIntegralNumerator : PowerSeries ℤ :=
  weberSquareDenominatorIntegralQExpansion *
    PowerSeries.invOfUnit ((PowerSeries.pentagonalSeries ℤ) ^ 2) 1

/-- The full integer width-twenty-four series for the second Weber square. -/
def weberF₂SquareIntegralQExpansion : PowerSeries ℤ :=
  2 * PowerSeries.X ^ 3 *
    PowerSeries.expand 24 (by decide) weberF₂SquareIntegralNumerator

private theorem branch_qParam_pow (h : ℝ) (n : ℕ) (z : ℂ) :
    Function.Periodic.qParam h z ^ n =
      Complex.exp (n * (2 * (Real.pi : ℂ) * Complex.I * z / h)) := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]

private theorem branch_qParam_one_eq_two_sq (z : ℂ) :
    Function.Periodic.qParam 1 z = Function.Periodic.qParam 2 z ^ 2 := by
  rw [branch_qParam_pow]
  unfold Function.Periodic.qParam
  congr 1
  push_cast
  ring

private theorem branch_qParam_two_eq_twentyFour_pow_twelve (z : ℂ) :
    Function.Periodic.qParam 2 z = Function.Periodic.qParam 24 z ^ 12 := by
  rw [branch_qParam_pow]
  unfold Function.Periodic.qParam
  congr 1
  push_cast
  ring

private theorem branch_qParam_one_eq_twentyFour_pow (z : ℂ) :
    Function.Periodic.qParam 1 z = Function.Periodic.qParam 24 z ^ 24 := by
  rw [branch_qParam_pow]
  unfold Function.Periodic.qParam
  congr 1
  push_cast
  ring

private theorem branch_qParam_two_add_one (z : ℂ) :
    Function.Periodic.qParam 2 (z + 1) = -Function.Periodic.qParam 2 z := by
  unfold Function.Periodic.qParam
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (z + 1) / ((2 : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * z / ((2 : ℝ) : ℂ) +
        (Real.pi : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

private theorem branch_regularized_weberF_add_one (z : ℂ) :
    Function.Periodic.qParam 24 (z + 1) * weberF (z + 1) ^ 2 =
      Function.Periodic.qParam 24 z * weberF₁ z ^ 2 := by
  have hq : Function.Periodic.qParam 24 (z + 1) =
      Function.Periodic.qParam 24 z * zeta48 ^ 2 := by
    rw [zeta48_sq]
    unfold Function.Periodic.qParam
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hq, weberF_add_one, mul_pow, inv_pow]
  field_simp [zeta48_ne_zero]

/-- The first branch has the unsigned Euler numerator, with its actual eta phase. -/
theorem qParam_twentyFour_mul_weberF₁_sq_eq_div_eulerFunction (τ : UpperHalfPlane) :
    Function.Periodic.qParam 24 (τ : ℂ) * weberF₁ (τ : ℂ) ^ 2 =
      eulerFunction (Function.Periodic.qParam 2 (τ : ℂ)) ^ 2 /
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2 := by
  have h := qParam_twentyFour_mul_weberF_sq_eq_div_eulerFunction ((1 : ℝ) +ᵥ τ)
  have hq1 : Function.Periodic.qParam 1 ((τ : ℂ) + 1) =
      Function.Periodic.qParam 1 (τ : ℂ) := by
    rw [branch_qParam_one_eq_two_sq, branch_qParam_two_add_one,
      branch_qParam_one_eq_two_sq]
    ring
  simpa only [UpperHalfPlane.coe_vadd, Complex.ofReal_one, add_comm (1 : ℂ),
    branch_regularized_weberF_add_one, hq1, branch_qParam_two_add_one, neg_neg] using h

/-- The complete width-two first-branch integer series sums to the actual eta quotient. -/
theorem hasSum_weberF₁SquareIntegralNumerator (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (weberF₁SquareIntegralNumerator.coeff n : ℂ) *
      Function.Periodic.qParam 2 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 24 (τ : ℂ) * weberF₁ (τ : ℂ) ^ 2) := by
  have hs := hasSum_weberSquareIntegralNumerator ((1 : ℝ) +ᵥ τ)
  simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_one, add_comm (1 : ℂ),
    branch_regularized_weberF_add_one, branch_qParam_two_add_one] at hs
  convert hs using 1
  funext n
  simp only [weberF₁SquareIntegralNumerator, PowerSeries.coeff_rescale, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [show -Function.Periodic.qParam 2 (τ : ℂ) =
    (-1 : ℂ) * Function.Periodic.qParam 2 (τ : ℂ) by ring, mul_pow]
  ring

/-- The complete width-twenty-four first-branch series converges at every point. -/
theorem hasSum_weberF₁SquareIntegralQExpansion (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (weberF₁SquareIntegralQExpansion.coeff n : ℂ) *
      Function.Periodic.qParam 24 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 24 (τ : ℂ) * weberF₁ (τ : ℂ) ^ 2) := by
  have hs : HasSum (fun n : ℕ =>
      (PowerSeries.expand 12 (by decide)
        (PowerSeries.map (Int.castRingHom ℂ) weberF₁SquareIntegralNumerator)).coeff n *
          Function.Periodic.qParam 24 (τ : ℂ) ^ n)
        (Function.Periodic.qParam 24 (τ : ℂ) * weberF₁ (τ : ℂ) ^ 2) := by
    apply hasSum_powerSeries_expand (by decide)
    simpa only [PowerSeries.coeff_map, Int.coe_castRingHom,
      branch_qParam_two_eq_twentyFour_pow_twelve, pow_mul] using
      hasSum_weberF₁SquareIntegralNumerator τ
  rw [← PowerSeries.map_expand] at hs
  simpa only [weberF₁SquareIntegralQExpansion, PowerSeries.coeff_map,
    Int.coe_castRingHom] using hs

private theorem branch_qParam_periodic (h : ℝ) :
    Function.Periodic ((fun τ : UpperHalfPlane => Function.Periodic.qParam h (τ : ℂ)) ∘
      UpperHalfPlane.ofComplex) h := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro τ
  by_cases hh : h = 0
  · simp [Function.Periodic.qParam, hh]
  simp [Function.Periodic.qParam, UpperHalfPlane.coe_vadd, mul_add, add_div,
    Complex.exp_add, hh]

private theorem branch_qParam_mdifferentiable (h : ℝ) :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam h (τ : ℂ)) :=
  (Function.Periodic.differentiable_qParam (h := h)).mdifferentiable.comp mdifferentiable_coe

/-- The actual first-branch regularization is holomorphic. -/
theorem mdifferentiable_qParam_twentyFour_mul_weberF₁_sq :
    MDiff (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₁ (τ : ℂ) ^ 2) := by
  have hW : MDiff (fun τ : UpperHalfPlane => weberF₁ (τ : ℂ)) :=
    fun τ => (analyticOnNhd_weberF₁ (τ : ℂ) τ.im_pos).differentiableAt.mdifferentiableAt.comp
      τ τ.mdifferentiable_coe
  exact (branch_qParam_mdifferentiable 24).mul (hW.pow 2)

/-- The actual first branch tends to its unit constant coefficient at the cusp. -/
theorem tendsto_qParam_twentyFour_mul_weberF₁_sq :
    Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₁ (τ : ℂ) ^ 2) atImInfty (𝓝 1) := by
  have hnum := (tendsto_eulerFunction_zero.comp
    (qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 2))).pow 2
  have hden := (tendsto_eulerFunction_zero.comp
    (qParam_tendsto_atImInfty one_pos)).pow 2
  have ht := hnum.div hden (by norm_num : (1 : ℂ) ^ 2 ≠ 0)
  change Tendsto (fun τ : UpperHalfPlane =>
    eulerFunction (Function.Periodic.qParam 2 (τ : ℂ)) ^ 2 /
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2)
    atImInfty (𝓝 ((1 : ℂ) ^ 2 / 1 ^ 2)) at ht
  simpa only [qParam_twentyFour_mul_weberF₁_sq_eq_div_eulerFunction, one_pow, div_one] using ht

/-- The first-branch regularization has period two. -/
theorem periodic_qParam_twentyFour_mul_weberF₁_sq :
    Function.Periodic ((fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₁ (τ : ℂ) ^ 2) ∘
        UpperHalfPlane.ofComplex) 2 := by
  intro z
  have h := branch_qParam_periodic 2 z
  simpa only [Function.comp_apply, Complex.ofReal_ofNat,
    qParam_twentyFour_mul_weberF₁_sq_eq_div_eulerFunction, branch_qParam_one_eq_two_sq] using
    congrArg (fun q : ℂ => eulerFunction q ^ 2 / eulerFunction (q ^ 2) ^ 2) h

/-- The actual first-branch q-expansion is the image of the entire integer series. -/
theorem qExpansion_twentyFour_regularized_weberF₁_sq_eq_map_int :
    qExpansion 24 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₁ (τ : ℂ) ^ 2) =
        PowerSeries.map (Int.castRingHom ℂ) weberF₁SquareIntegralQExpansion := by
  have hper : Function.Periodic ((fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₁ (τ : ℂ) ^ 2) ∘
        UpperHalfPlane.ofComplex) 24 := by
    convert periodic_qParam_twentyFour_mul_weberF₁_sq.nat_mul 12 using 1
    norm_num
  have han := analyticAt_cuspFunction_zero (by norm_num : (0 : ℝ) < 24) hper
    mdifferentiable_qParam_twentyFour_mul_weberF₁_sq
    (tendsto_qParam_twentyFour_mul_weberF₁_sq.isBigO_one ℝ)
  ext m
  rw [PowerSeries.coeff_map]
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique_unbundled (by norm_num : (0 : ℝ) < 24)
    (fun τ => Function.Periodic.qParam 24 (τ : ℂ) * weberF₁ (τ : ℂ) ^ 2)
    (fun n => (weberF₁SquareIntegralQExpansion.coeff n : ℂ)) han
    hasSum_weberF₁SquareIntegralQExpansion m

/-- The second branch has its eta-defined factor `2 q³` and Euler quotient. -/
theorem qParam_twentyFour_mul_weberF₂_sq_mul_eulerFunction (τ : UpperHalfPlane) :
    (Function.Periodic.qParam 24 (τ : ℂ) * weberF₂ (τ : ℂ) ^ 2) *
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2 =
      2 * Function.Periodic.qParam 24 (τ : ℂ) ^ 3 *
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ) ^ 2) ^ 2 := by
  let σ := cyclicSublatticePoint (2, 0, 1) τ
  have hσ : (σ : ℂ) = 2 * (τ : ℂ) := by
    simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero, div_one] using
      cyclicSublatticePoint_coe (t := (2, 0, 1)) (by decide) (by decide) τ
  have hqσ : Function.Periodic.qParam 1 (σ : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ 2 := by
    rw [branch_qParam_pow]
    simp only [Function.Periodic.qParam, hσ]
    congr 1
    push_cast
    ring
  have hphase : Function.Periodic.qParam 24 (τ : ℂ) *
      Function.Periodic.qParam 12 (σ : ℂ) / Function.Periodic.qParam 12 (τ : ℂ) =
        Function.Periodic.qParam 24 (τ : ℂ) ^ 3 := by
    simp only [Function.Periodic.qParam, hσ, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  have hsqrt : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hE0 : eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ≠ 0 := by
    intro h
    apply eulerFunction_qParam_one_sq_ne_zero τ
    simp [h]
  calc
    _ = 2 * (Function.Periodic.qParam 24 (τ : ℂ) *
        Function.Periodic.qParam 12 (σ : ℂ) / Function.Periodic.qParam 12 (τ : ℂ)) *
          eulerFunction (Function.Periodic.qParam 1 (τ : ℂ) ^ 2) ^ 2 := by
      rw [weberF₂, mul_pow, hsqrt, div_pow, ← hσ,
        eta_sq_eq_qParam_twelve_mul_eulerFunction σ,
        eta_sq_eq_qParam_twelve_mul_eulerFunction τ, hqσ]
      field_simp [Function.Periodic.qParam_ne_zero (h := 12) (τ : ℂ), hE0]
    _ = _ := by rw [hphase]

/-- The second branch is the quotient of its actual analytic Euler factors. -/
theorem qParam_twentyFour_mul_weberF₂_sq_eq_div_eulerFunction (τ : UpperHalfPlane) :
    Function.Periodic.qParam 24 (τ : ℂ) * weberF₂ (τ : ℂ) ^ 2 =
      (2 * Function.Periodic.qParam 24 (τ : ℂ) ^ 3 *
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ) ^ 2) ^ 2) /
          eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2 :=
  (eq_div_iff (eulerFunction_qParam_one_sq_ne_zero τ)).mpr
    (qParam_twentyFour_mul_weberF₂_sq_mul_eulerFunction τ)

private def branchEulerDenominator (τ : UpperHalfPlane) : ℂ :=
  eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2

private def branchF₂EulerNumerator (τ : UpperHalfPlane) : ℂ :=
  2 * Function.Periodic.qParam 24 (τ : ℂ) ^ 3 *
    eulerFunction (Function.Periodic.qParam 1 (τ : ℂ) ^ 2) ^ 2

private def branchDenominatorIntegralQExpansion : PowerSeries ℤ :=
  PowerSeries.expand 24 (by decide) ((PowerSeries.pentagonalSeries ℤ) ^ 2)

private def branchF₂NumeratorIntegralQExpansion : PowerSeries ℤ :=
  2 * PowerSeries.X ^ 3 *
    PowerSeries.expand 24 (by decide) weberSquareDenominatorIntegralQExpansion

private theorem branchEulerDenominator_tendsto :
    Tendsto branchEulerDenominator atImInfty (𝓝 1) := by
  change Tendsto (fun τ : UpperHalfPlane =>
    eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2) atImInfty (𝓝 1)
  simpa [branchEulerDenominator] using
    (tendsto_eulerFunction_zero.comp (qParam_tendsto_atImInfty one_pos)).pow 2

private theorem branchF₂EulerNumerator_tendsto :
    Tendsto branchF₂EulerNumerator atImInfty (𝓝 0) := by
  change Tendsto (fun τ : UpperHalfPlane =>
    2 * Function.Periodic.qParam 24 (τ : ℂ) ^ 3 *
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ) ^ 2) ^ 2) atImInfty (𝓝 0)
  have hq := qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 24)
  have hE := (tendsto_eulerFunction_zero.comp
    (by simpa using (qParam_tendsto_atImInfty one_pos).pow 2)).pow 2
  simpa [branchF₂EulerNumerator, Function.comp_def] using
    ((hq.pow 3).const_mul 2).mul hE

/-- The actual second-branch regularization vanishes at the cusp. -/
theorem tendsto_qParam_twentyFour_mul_weberF₂_sq :
    Tendsto (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₂ (τ : ℂ) ^ 2) atImInfty (𝓝 0) := by
  have ht := branchF₂EulerNumerator_tendsto.div branchEulerDenominator_tendsto
    (by norm_num : (1 : ℂ) ≠ 0)
  change Tendsto (fun τ : UpperHalfPlane =>
    (2 * Function.Periodic.qParam 24 (τ : ℂ) ^ 3 *
      eulerFunction (Function.Periodic.qParam 1 (τ : ℂ) ^ 2) ^ 2) /
        eulerFunction (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2)
    atImInfty (𝓝 ((0 : ℂ) / 1)) at ht
  simpa only [qParam_twentyFour_mul_weberF₂_sq_eq_div_eulerFunction, zero_div] using ht

/-- The actual second-branch regularization is holomorphic. -/
theorem mdifferentiable_qParam_twentyFour_mul_weberF₂_sq :
    MDiff (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₂ (τ : ℂ) ^ 2) := by
  have hW : MDiff (fun τ : UpperHalfPlane => weberF₂ (τ : ℂ)) :=
    fun τ => (analyticOnNhd_weberF₂ (τ : ℂ) τ.im_pos).differentiableAt.mdifferentiableAt.comp
      τ τ.mdifferentiable_coe
  exact (branch_qParam_mdifferentiable 24).mul (hW.pow 2)

private theorem branchEulerDenominator_mdifferentiable :
    MDiff branchEulerDenominator := by
  have hη : MDiff (fun τ : UpperHalfPlane => eta (τ : ℂ)) :=
    fun τ => (differentiableAt_eta_of_mem_upperHalfPlaneSet τ.im_pos).mdifferentiableAt.comp
      τ τ.mdifferentiable_coe
  have hfun : branchEulerDenominator =
      fun τ : UpperHalfPlane => eta (τ : ℂ) ^ 2 / Function.Periodic.qParam 12 (τ : ℂ) := by
    funext τ
    rw [eta_sq_eq_qParam_twelve_mul_eulerFunction, mul_div_cancel_left₀ _
      (Function.Periodic.qParam_ne_zero (h := 12) (τ : ℂ))]
    rfl
  rw [hfun]
  exact (hη.pow 2).div (branch_qParam_mdifferentiable 12)
    (fun τ => Function.Periodic.qParam_ne_zero (h := 12) (τ : ℂ))

private theorem branchF₂EulerNumerator_mdifferentiable :
    MDiff branchF₂EulerNumerator := by
  have hfun : branchF₂EulerNumerator =
      (fun τ : UpperHalfPlane => Function.Periodic.qParam 24 (τ : ℂ) * weberF₂ (τ : ℂ) ^ 2) *
        branchEulerDenominator := by
    funext τ
    exact (qParam_twentyFour_mul_weberF₂_sq_mul_eulerFunction τ).symm
  rw [hfun]
  exact mdifferentiable_qParam_twentyFour_mul_weberF₂_sq.mul
    branchEulerDenominator_mdifferentiable

private theorem branchEulerDenominator_periodic :
    Function.Periodic (branchEulerDenominator ∘ UpperHalfPlane.ofComplex) 24 := by
  intro z
  have h := branch_qParam_periodic 24 z
  simpa only [Function.comp_apply, Complex.ofReal_ofNat, branchEulerDenominator,
    branch_qParam_one_eq_twentyFour_pow] using
    congrArg (fun q : ℂ => eulerFunction (q ^ 24) ^ 2) h

private theorem branchF₂EulerNumerator_periodic :
    Function.Periodic (branchF₂EulerNumerator ∘ UpperHalfPlane.ofComplex) 24 := by
  intro z
  have h := branch_qParam_periodic 24 z
  simpa only [Function.comp_apply, Complex.ofReal_ofNat, branchF₂EulerNumerator,
    branch_qParam_one_eq_twentyFour_pow] using
    congrArg (fun q : ℂ => 2 * q ^ 3 * eulerFunction ((q ^ 24) ^ 2) ^ 2) h

/-- The actual second-branch regularization has period twenty-four. -/
theorem periodic_qParam_twentyFour_mul_weberF₂_sq :
    Function.Periodic ((fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₂ (τ : ℂ) ^ 2) ∘
        UpperHalfPlane.ofComplex) 24 := by
  intro z
  simpa only [Function.comp_apply, Pi.div_apply, branchF₂EulerNumerator,
    branchEulerDenominator, qParam_twentyFour_mul_weberF₂_sq_eq_div_eulerFunction] using
    (branchF₂EulerNumerator_periodic.div branchEulerDenominator_periodic) z

private theorem branchEulerDenominator_analyticAt_cuspFunction :
    AnalyticAt ℂ (cuspFunction 24 branchEulerDenominator) 0 :=
  analyticAt_cuspFunction_zero (by norm_num) branchEulerDenominator_periodic
    branchEulerDenominator_mdifferentiable (branchEulerDenominator_tendsto.isBigO_one ℝ)

private theorem branchF₂EulerNumerator_analyticAt_cuspFunction :
    AnalyticAt ℂ (cuspFunction 24 branchF₂EulerNumerator) 0 :=
  analyticAt_cuspFunction_zero (by norm_num) branchF₂EulerNumerator_periodic
    branchF₂EulerNumerator_mdifferentiable (branchF₂EulerNumerator_tendsto.isBigO_one ℝ)

private theorem regularizedWeberF₂Square_analyticAt_cuspFunction :
    AnalyticAt ℂ (cuspFunction 24 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₂ (τ : ℂ) ^ 2)) 0 :=
  analyticAt_cuspFunction_zero (by norm_num) periodic_qParam_twentyFour_mul_weberF₂_sq
    mdifferentiable_qParam_twentyFour_mul_weberF₂_sq
    (tendsto_qParam_twentyFour_mul_weberF₂_sq.isBigO_one ℝ)

private theorem hasSum_branchEulerDenominator (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (branchDenominatorIntegralQExpansion.coeff n : ℂ) *
      Function.Periodic.qParam 24 (τ : ℂ) ^ n) (branchEulerDenominator τ) := by
  have hs : HasSum (fun n : ℕ =>
      (PowerSeries.expand 24 (by decide) ((PowerSeries.pentagonalSeries ℂ) ^ 2)).coeff n *
        Function.Periodic.qParam 24 (τ : ℂ) ^ n) (branchEulerDenominator τ) := by
    apply hasSum_powerSeries_expand (by decide)
    simpa only [branchEulerDenominator, branch_qParam_one_eq_twentyFour_pow, pow_mul] using
      PowerSeries.hasSum_pentagonalSeries_pow 2
        (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)
  have hmap : PowerSeries.map (Int.castRingHom ℂ) branchDenominatorIntegralQExpansion =
      PowerSeries.expand 24 (by decide) ((PowerSeries.pentagonalSeries ℂ) ^ 2) := by
    simp only [branchDenominatorIntegralQExpansion, PowerSeries.map_expand, map_pow,
      PowerSeries.map_pentagonalSeries]
  rw [← hmap] at hs
  simpa only [PowerSeries.coeff_map, Int.coe_castRingHom] using hs

private theorem hasSum_branchF₂EulerNumerator (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (branchF₂NumeratorIntegralQExpansion.coeff n : ℂ) *
      Function.Periodic.qParam 24 (τ : ℂ) ^ n) (branchF₂EulerNumerator τ) := by
  have hD : HasSum (fun n : ℕ =>
      (PowerSeries.expand 24 (by decide)
        (PowerSeries.map (Int.castRingHom ℂ) weberSquareDenominatorIntegralQExpansion)).coeff n *
          Function.Periodic.qParam 24 (τ : ℂ) ^ n)
        (eulerFunction (Function.Periodic.qParam 1 (τ : ℂ) ^ 2) ^ 2) := by
    apply hasSum_powerSeries_expand (by decide)
    have hs : HasSum (fun n : ℕ =>
        (PowerSeries.expand 2 (by decide) ((PowerSeries.pentagonalSeries ℂ) ^ 2)).coeff n *
          Function.Periodic.qParam 1 (τ : ℂ) ^ n)
        (eulerFunction (Function.Periodic.qParam 1 (τ : ℂ) ^ 2) ^ 2) := by
      apply hasSum_powerSeries_expand (by decide)
      have hnorm : ‖Function.Periodic.qParam 1 (τ : ℂ) ^ 2‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _)
          (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos) (by decide)
      simpa only [pow_mul] using PowerSeries.hasSum_pentagonalSeries_pow 2 hnorm
    simpa only [weberSquareDenominatorIntegralQExpansion, PowerSeries.map_expand,
      map_pow, PowerSeries.map_pentagonalSeries, branch_qParam_one_eq_twentyFour_pow,
      pow_mul] using hs
  have hmon : HasSum (fun n : ℕ =>
      ((2 * PowerSeries.X ^ 3 : PowerSeries ℂ).coeff n) *
        Function.Periodic.qParam 24 (τ : ℂ) ^ n)
      (2 * Function.Periodic.qParam 24 (τ : ℂ) ^ 3) := by
    convert hasSum_ite_eq 3 (2 * Function.Periodic.qParam 24 (τ : ℂ) ^ 3) using 1
    funext n
    by_cases hn : n = 3 <;> simp [PowerSeries.coeff_X_pow, hn]
  have hs := PowerSeries.hasSum_coeff_mul hmon hD
  have hmap : PowerSeries.map (Int.castRingHom ℂ) branchF₂NumeratorIntegralQExpansion =
      2 * PowerSeries.X ^ 3 * PowerSeries.expand 24 (by decide)
        (PowerSeries.map (Int.castRingHom ℂ) weberSquareDenominatorIntegralQExpansion) := by
    simp only [branchF₂NumeratorIntegralQExpansion, map_mul, map_ofNat, map_pow,
      PowerSeries.map_X, PowerSeries.map_expand]
  rw [← hmap] at hs
  simpa only [PowerSeries.coeff_map, Int.coe_castRingHom, branchF₂EulerNumerator] using hs

private theorem qExpansion_branchEulerDenominator_eq_map_int :
    qExpansion 24 branchEulerDenominator =
      PowerSeries.map (Int.castRingHom ℂ) branchDenominatorIntegralQExpansion := by
  ext m
  rw [PowerSeries.coeff_map]
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique_unbundled (by norm_num : (0 : ℝ) < 24)
    branchEulerDenominator (fun n => (branchDenominatorIntegralQExpansion.coeff n : ℂ))
    branchEulerDenominator_analyticAt_cuspFunction hasSum_branchEulerDenominator m

private theorem qExpansion_branchF₂EulerNumerator_eq_map_int :
    qExpansion 24 branchF₂EulerNumerator =
      PowerSeries.map (Int.castRingHom ℂ) branchF₂NumeratorIntegralQExpansion := by
  ext m
  rw [PowerSeries.coeff_map]
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique_unbundled (by norm_num : (0 : ℝ) < 24)
    branchF₂EulerNumerator (fun n => (branchF₂NumeratorIntegralQExpansion.coeff n : ℂ))
    branchF₂EulerNumerator_analyticAt_cuspFunction hasSum_branchF₂EulerNumerator m

private theorem branch_pentagonalSeries_sq_constantCoeff :
    ((PowerSeries.pentagonalSeries ℤ) ^ 2).constantCoeff = 1 := by
  have hp : (PowerSeries.pentagonalSeries ℤ).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.coeff_pentagonalSeries_pentagonal ℤ (0 : ℤ)
  simp [hp]

/-- The second-branch Euler quotient satisfies its exact integer denominator equation. -/
theorem pentagonalSeries_sq_mul_weberF₂SquareIntegralNumerator :
    (PowerSeries.pentagonalSeries ℤ) ^ 2 * weberF₂SquareIntegralNumerator =
      weberSquareDenominatorIntegralQExpansion := by
  dsimp only [weberF₂SquareIntegralNumerator]
  rw [mul_left_comm, PowerSeries.mul_invOfUnit _ 1
    (by simpa using branch_pentagonalSeries_sq_constantCoeff), mul_one]

private theorem branchDenominator_mul_weberF₂SquareIntegralQExpansion :
    branchDenominatorIntegralQExpansion * weberF₂SquareIntegralQExpansion =
      branchF₂NumeratorIntegralQExpansion := by
  change PowerSeries.expand 24 (by decide) ((PowerSeries.pentagonalSeries ℤ) ^ 2) *
    (2 * PowerSeries.X ^ 3 *
      PowerSeries.expand 24 (by decide) weberF₂SquareIntegralNumerator) = _
  rw [mul_left_comm, ← map_mul,
    pentagonalSeries_sq_mul_weberF₂SquareIntegralNumerator]
  rfl

/-- The actual second-branch q-expansion is the image of the entire integer series. -/
theorem qExpansion_twentyFour_regularized_weberF₂_sq_eq_map_int :
    qExpansion 24 (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₂ (τ : ℂ) ^ 2) =
        PowerSeries.map (Int.castRingHom ℂ) weberF₂SquareIntegralQExpansion := by
  have hU : PowerSeries.map (Int.castRingHom ℂ) branchDenominatorIntegralQExpansion ≠ 0 := by
    intro hzero
    have hc := congrArg (fun P : PowerSeries ℂ => P.coeff 0) hzero
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      branchDenominatorIntegralQExpansion, PowerSeries.constantCoeff_expand,
      branch_pentagonalSeries_sq_constantCoeff] at hc
    norm_num at hc
  apply mul_right_cancel₀ hU
  have hmul := UpperHalfPlane.qExpansion_mul regularizedWeberF₂Square_analyticAt_cuspFunction
    branchEulerDenominator_analyticAt_cuspFunction
  have hfun : (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam 24 (τ : ℂ) * weberF₂ (τ : ℂ) ^ 2) *
        branchEulerDenominator = branchF₂EulerNumerator := by
    funext τ
    exact qParam_twentyFour_mul_weberF₂_sq_mul_eulerFunction τ
  rw [hfun, qExpansion_branchEulerDenominator_eq_map_int,
    qExpansion_branchF₂EulerNumerator_eq_map_int] at hmul
  have hformal := congrArg (PowerSeries.map (Int.castRingHom ℂ))
    branchDenominator_mul_weberF₂SquareIntegralQExpansion
  rw [map_mul] at hformal
  exact hmul.symm.trans (hformal.symm.trans (mul_comm _ _))

/-- The complete second-branch integer series sums to the actual eta quotient everywhere. -/
theorem hasSum_weberF₂SquareIntegralQExpansion (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (weberF₂SquareIntegralQExpansion.coeff n : ℂ) *
      Function.Periodic.qParam 24 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 24 (τ : ℂ) * weberF₂ (τ : ℂ) ^ 2) := by
  have hs := τ.hasSum_qExpansion (by norm_num : (0 : ℝ) < 24)
    periodic_qParam_twentyFour_mul_weberF₂_sq mdifferentiable_qParam_twentyFour_mul_weberF₂_sq
    (tendsto_qParam_twentyFour_mul_weberF₂_sq.isBigO_one ℝ)
  rw [qExpansion_twentyFour_regularized_weberF₂_sq_eq_map_int] at hs
  simpa only [PowerSeries.coeff_map, smul_eq_mul, Int.coe_castRingHom] using hs

/-- The second-branch Euler quotient has unit constant coefficient. -/
theorem weberF₂SquareIntegralNumerator_constantCoeff :
    weberF₂SquareIntegralNumerator.constantCoeff = 1 := by
  simp [weberF₂SquareIntegralNumerator, weberSquareDenominatorIntegralQExpansion_constantCoeff]

/-- The first nonconstant width-two coefficient of the original branch is two. -/
theorem weberSquareIntegralNumerator_coeff_one :
    weberSquareIntegralNumerator.coeff 1 = 2 := by
  have hp0 : (PowerSeries.pentagonalSeries ℤ).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.coeff_pentagonalSeries_pentagonal ℤ (0 : ℤ)
  have hp1 : (PowerSeries.pentagonalSeries ℤ).coeff 1 = -1 := by
    simpa [pentagonal] using
      PowerSeries.coeff_pentagonalSeries_pentagonal ℤ (1 : ℤ)
  have hs1 : ((PowerSeries.pentagonalSeries ℤ) ^ 2).coeff 1 = -2 := by
    rw [pow_two, PowerSeries.coeff_one_mul, hp0, hp1]
    norm_num
  have hD1 : weberSquareDenominatorIntegralQExpansion.coeff 1 = 0 := by
    exact PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ (by decide)
  have h := congrArg (fun P : PowerSeries ℤ => P.coeff 1)
    weberSquareDenominator_mul_integralNumerator
  norm_num only [PowerSeries.coeff_one_mul, hD1, zero_mul, zero_add,
    weberSquareDenominatorIntegralQExpansion_constantCoeff, mul_one,
    PowerSeries.coeff_rescale, pow_one, hs1] at h
  exact h

/-- The original Weber-square series has coefficient two at width-twenty-four degree twelve. -/
theorem weberSquareIntegralQExpansion_coeff_twelve :
    weberSquareIntegralQExpansion.coeff 12 = 2 := by
  change (PowerSeries.expand 12 (by decide) weberSquareIntegralNumerator).coeff (12 * 1) = 2
  rw [PowerSeries.coeff_expand_mul, weberSquareIntegralNumerator_coeff_one]

/-- The first-branch integer series has constant coefficient one. -/
theorem weberF₁SquareIntegralQExpansion_constantCoeff :
    weberF₁SquareIntegralQExpansion.constantCoeff = 1 := by
  rw [weberF₁SquareIntegralQExpansion, PowerSeries.constantCoeff_expand,
    ← PowerSeries.coeff_zero_eq_constantCoeff, weberF₁SquareIntegralNumerator,
    PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff,
    weberSquareIntegralNumerator_constantCoeff]

/-- The first branch differs from the original branch at degree twelve. -/
theorem weberF₁SquareIntegralQExpansion_coeff_twelve :
    weberF₁SquareIntegralQExpansion.coeff 12 = -2 := by
  change (PowerSeries.expand 12 (by decide) weberF₁SquareIntegralNumerator).coeff (12 * 1) = -2
  rw [PowerSeries.coeff_expand_mul, weberF₁SquareIntegralNumerator,
    PowerSeries.coeff_rescale, pow_one, weberSquareIntegralNumerator_coeff_one]
  norm_num

/-- The second branch has zero constant coefficient. -/
theorem weberF₂SquareIntegralQExpansion_constantCoeff :
    weberF₂SquareIntegralQExpansion.constantCoeff = 0 := by
  simp [weberF₂SquareIntegralQExpansion]

/-- The first nonzero second-branch term is normalized to `2 q³`. -/
theorem weberF₂SquareIntegralQExpansion_coeff_three :
    weberF₂SquareIntegralQExpansion.coeff 3 = 2 := by
  rw [weberF₂SquareIntegralQExpansion, mul_assoc, PowerSeries.coeff_ofNat_mul]
  change 2 * (PowerSeries.X ^ 3 *
    PowerSeries.expand 24 (by decide) weberF₂SquareIntegralNumerator).coeff (0 + 3) = 2
  rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.constantCoeff_expand, weberF₂SquareIntegralNumerator_constantCoeff, mul_one]

end ModularForm
end
