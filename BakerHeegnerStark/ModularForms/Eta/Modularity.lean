import BakerHeegnerStark.ModularForms.Eta.CharacterTwelve
import BakerHeegnerStark.ModularForms.Weber.Basic

/-!
# The Actual Eta-Square Multiplier

The weight-one multiplier of `η²` factors through reduction modulo twelve.
Its exponent is `4e₃-3e₄`, with the previously proved cubic exponent and the
quartic exponent of `ModularForms/Eta/CharacterFour.lean`. It sends `S` to `-I` and `T` to
`exp(2πI/12)`. The full transformation law follows from the actual S/T laws
and the denominator cocycle, not from an equality of powers of eta values.
No CM or class-invariant field-membership assumption is used.
-/

open scoped Real ModularForm MatrixGroups
namespace ModularForm
noncomputable section

/-- The integral eta-square exponent reconstructed from the mod-three and mod-four exponents. -/
def etaExponentTwelve (g : SL(2, ℤ)) : ZMod 12 :=
  4 * ((gammaExponentThree
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g)).val : ZMod 12) -
    3 * ((etaExponentFour
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 4)) g)).val : ZMod 12)

/-- The integral eta-square exponent is its finite model evaluated on reduction modulo twelve. -/
theorem etaExponentTwelve_eq_finite (g : SL(2, ℤ)) :
    etaExponentTwelve g = etaExponentTwelveMod
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 12)) g) := by
  simp only [etaExponentTwelve, etaExponentTwelveMod, specialLinearReduction_comp_of_dvd]

@[simp]
theorem etaExponentTwelve_one : etaExponentTwelve 1 = 0 := by
  norm_num [etaExponentTwelve, ZMod.val_one_eq_one_mod]

/-- The reconstructed exponent is additive under integral matrix multiplication. -/
theorem etaExponentTwelve_mul (g h : SL(2, ℤ)) :
    etaExponentTwelve (g * h) = etaExponentTwelve g + etaExponentTwelve h := by
  simp only [etaExponentTwelve_eq_finite, map_mul, etaExponentTwelveMod_mul]

@[simp]
theorem etaExponentTwelve_S : etaExponentTwelve ModularGroup.S = 9 := by
  norm_num [etaExponentTwelve, ZMod.val_one_eq_one_mod]
  decide

@[simp]
theorem etaExponentTwelve_T : etaExponentTwelve ModularGroup.T = 1 := by
  norm_num [etaExponentTwelve, ZMod.val_one_eq_one_mod]

/-- The twelfth root of unity in the actual eta-square translation formula. -/
def etaPhaseTwelve : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

/-- Cubing the normalized translation phase gives `I`. -/
theorem etaPhaseTwelve_cube : etaPhaseTwelve ^ 3 = Complex.I := by
  rw [etaPhaseTwelve, ← Complex.exp_nat_mul,
    show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 12) =
      (Real.pi : ℂ) / 2 * Complex.I by push_cast; ring,
    Complex.exp_pi_div_two_mul_I]

/-- The translation phase is a twelfth root of unity. -/
theorem etaPhaseTwelve_pow_twelve : etaPhaseTwelve ^ 12 = 1 := by
  rw [show (12 : ℕ) = 3 * 4 by decide, pow_mul, etaPhaseTwelve_cube]
  norm_num

/-- Evaluation of a residue modulo twelve at the normalized translation phase. -/
def etaMultiplierTwelve (r : ZMod 12) : ℂ := etaPhaseTwelve ^ r.val

/-- The zero exponent has multiplier one. -/
theorem etaMultiplierTwelve_zero : etaMultiplierTwelve 0 = 1 := by
  simp [etaMultiplierTwelve]

/-- Addition of exponents multiplies the actual complex phases. -/
theorem etaMultiplierTwelve_add (r s : ZMod 12) :
    etaMultiplierTwelve (r + s) = etaMultiplierTwelve r * etaMultiplierTwelve s := by
  unfold etaMultiplierTwelve
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ etaPhaseTwelve_pow_twelve).symm

/-- The weight-one eta-square character of the integral modular group. -/
def etaSquareCharacter : SL(2, ℤ) →* ℂ where
  toFun g := etaMultiplierTwelve (etaExponentTwelve g)
  map_one' := by rw [etaExponentTwelve_one, etaMultiplierTwelve_zero]
  map_mul' g h := by rw [etaExponentTwelve_mul, etaMultiplierTwelve_add]

/-- The eta-square character takes modular inversion to `-I`. -/
theorem etaSquareCharacter_S : etaSquareCharacter ModularGroup.S = -Complex.I := by
  change etaMultiplierTwelve (etaExponentTwelve ModularGroup.S) = _
  rw [etaExponentTwelve_S]
  change etaPhaseTwelve ^ 9 = _
  rw [show (9 : ℕ) = 3 * 3 by decide, pow_mul, etaPhaseTwelve_cube]
  norm_num

/-- The eta-square character takes translation to the normalized twelfth root. -/
theorem etaSquareCharacter_T : etaSquareCharacter ModularGroup.T = etaPhaseTwelve := by
  change etaMultiplierTwelve (etaExponentTwelve ModularGroup.T) = _
  rw [etaExponentTwelve_T]
  norm_num [etaMultiplierTwelve, ZMod.val_one_eq_one_mod]

private theorem complex_sqrt_sq {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 2 = z := by
  rw [sqrt_eq_exp hz, ← Complex.exp_nat_mul,
    show ((2 : ℕ) : ℂ) * (Complex.log z / 2) = Complex.log z by push_cast; ring,
    Complex.exp_log hz]

/-- The actual weight-one eta-square inversion formula. -/
theorem eta_sq_smul_S (τ : UpperHalfPlane) :
    η ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) ^ 2 =
      -Complex.I * (τ : ℂ) * η (τ : ℂ) ^ 2 := by
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ)
    simp only [inv_neg, neg_div, one_div]
  rw [hS, eta_neg_inv τ.im_pos, mul_pow, mul_pow, inv_pow,
    complex_sqrt_sq Complex.I_ne_zero, complex_sqrt_sq τ.ne_zero]
  norm_num
  ring

/-- The actual eta-square translation formula. -/
theorem eta_sq_add_one (z : ℂ) :
    η (z + 1) ^ 2 = etaPhaseTwelve * η z ^ 2 := by
  rw [eta_add_one, mul_pow]
  congr 1
  rw [← Complex.exp_nat_mul, etaPhaseTwelve]
  congr 1
  push_cast
  ring

private theorem eta_denom_mul (g h : SL(2, ℤ)) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom ((g * h : SL(2, ℤ)) : GL (Fin 2) ℝ) τ =
      UpperHalfPlane.denom g ((h • τ : UpperHalfPlane) : ℂ) * UpperHalfPlane.denom h τ := by
  rw [map_mul, map_mul]
  simpa only [← UpperHalfPlane.coe_smul_of_det_pos
      (by simp : 0 < (h : GL (Fin 2) ℝ).det.val), ← ModularGroup.sl_moeb] using
    UpperHalfPlane.denom_cocycle (g : GL (Fin 2) ℝ) (h : GL (Fin 2) ℝ) τ.im_ne_zero

set_option backward.isDefEq.respectTransparency false in
/-- The complete transformation law for the actual eta square at every upper-half-plane point. -/
theorem eta_sq_smul (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    η ((g • τ : UpperHalfPlane) : ℂ) ^ 2 =
      etaSquareCharacter g * UpperHalfPlane.denom g τ * η (τ : ℂ) ^ 2 := by
  have hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  revert τ
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      intro τ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · simpa only [etaSquareCharacter_S, ModularGroup.denom_S] using eta_sq_smul_S τ
      · have hden : UpperHalfPlane.denom ModularGroup.T τ = 1 := by
          simp [ModularGroup.T, ModularGroup.denom_apply]
        simpa only [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd,
          Complex.ofReal_one, etaSquareCharacter_T, hden, mul_one, add_comm] using
          eta_sq_add_one (τ : ℂ)
  | one =>
      intro τ
      simp
  | mul g h _ _ hg hh =>
      intro τ
      rw [mul_smul, hg, hh, map_mul, eta_denom_mul]
      ring
  | inv g _ hg =>
      intro τ
      have h := hg (g⁻¹ • τ)
      rw [smul_inv_smul] at h
      have hchar : etaSquareCharacter g⁻¹ * etaSquareCharacter g = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      have hden : UpperHalfPlane.denom g ((g⁻¹ • τ : UpperHalfPlane) : ℂ) *
          UpperHalfPlane.denom (g⁻¹ : SL(2, ℤ)) τ = 1 := by
        simpa using (eta_denom_mul g g⁻¹ τ).symm
      calc
        η ((g⁻¹ • τ : UpperHalfPlane) : ℂ) ^ 2 =
            (etaSquareCharacter g⁻¹ * etaSquareCharacter g) *
              (UpperHalfPlane.denom g ((g⁻¹ • τ : UpperHalfPlane) : ℂ) *
                UpperHalfPlane.denom (g⁻¹ : SL(2, ℤ)) τ) *
              η ((g⁻¹ • τ : UpperHalfPlane) : ℂ) ^ 2 := by rw [hchar, hden]; ring
        _ = etaSquareCharacter g⁻¹ * UpperHalfPlane.denom (g⁻¹ : SL(2, ℤ)) τ * η (τ : ℂ) ^ 2 := by
          rw [h]
          ring

/-- The eta-square character never vanishes. -/
theorem etaSquareCharacter_ne_zero (g : SL(2, ℤ)) : etaSquareCharacter g ≠ 0 := by
  change etaPhaseTwelve ^ (etaExponentTwelve g).val ≠ 0
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

/-- Identical reductions modulo three and four give the same actual eta-square character. -/
theorem etaSquareCharacter_eq_of_mod_reductions_eq {g h : SL(2, ℤ)}
    (h3 : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) h)
    (h4 : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 4)) g =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 4)) h) :
    etaSquareCharacter g = etaSquareCharacter h := by
  change etaMultiplierTwelve (etaExponentTwelve g) = etaMultiplierTwelve (etaExponentTwelve h)
  simp only [etaExponentTwelve, h3, h4]

/-- Divisibility of levels gives the reverse inclusion of principal congruence subgroups. -/
theorem principalCongruence_le_of_dvd {N M : ℕ} (hNM : N ∣ M) :
    CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro g hg
  obtain ⟨ha, hb, hc, hd⟩ := CongruenceSubgroup.Gamma_mem.mp hg
  have hcast : ∀ x : ℤ, (x : ZMod M) = 0 → (x : ZMod N) = 0 := by
    intro x hx
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd x N).mpr
    have hdiv : (N : ℤ) ∣ (M : ℤ) := by exact_mod_cast hNM
    exact hdiv.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd x M).mp hx)
  apply CongruenceSubgroup.Gamma_mem.mpr
  refine ⟨?_, hcast _ hb, hcast _ hc, ?_⟩
  · have h := hcast (g 0 0 - 1) (by simpa using sub_eq_zero.mpr ha)
    simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using h
  · have h := hcast (g 1 1 - 1) (by simpa using sub_eq_zero.mpr hd)
    simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using h

/-- The actual eta-square character is trivial on the principal level-twelve subgroup. -/
theorem etaSquareCharacter_eq_one_of_mem_Gamma_twelve (g : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma 12) : etaSquareCharacter g = 1 := by
  have h3 := CongruenceSubgroup.Gamma_mem'.mp
    (principalCongruence_le_of_dvd (by decide : 3 ∣ 12) hg)
  have h4 := CongruenceSubgroup.Gamma_mem'.mp
    (principalCongruence_le_of_dvd (by decide : 4 ∣ 12) hg)
  have h := etaSquareCharacter_eq_of_mod_reductions_eq (g := g) (h := 1)
    (by simpa using h3) (by simpa using h4)
  simpa using h

end
end ModularForm
