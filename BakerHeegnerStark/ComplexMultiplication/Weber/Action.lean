/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Weber.Modularity
import BakerHeegnerStark.ModularForms.Weber.CharacterTwentyFour
import QNFMathlib.Algebra.QuadraticAlgebra.Matrix
import QNFMathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import BakerHeegnerStark.EllipticFunctions.Uniformization.TorsionMatrix

/-!
# The action of normalized CM units on the Weber square

The half-period conjugate of an integral matrix reduces modulo twelve to
`weberThetaConjugateTwelve` of its reduction modulo twenty-four. In particular,
the actual Weber-square multiplier equals the finite exponent computed in
`ModularForms/Weber/CharacterTwentyFour.lean`.

For `m ≡ 3 (mod 8)` with `3 ∤ m`, every integral lift of the right-normalized
CM unit matrix `[[a, -m*b*r], [b, a*r]]`, where `(a² + m*b²)r = 1` modulo
twenty-four, fixes the actual Weber square throughout the upper half-plane.
This also applies to the represented matrix of an actual period-torus or
period-curve torsion automorphism commuting with quadratic-period multiplication.
These are transformation theorems, not a CM reciprocity or field-descent theorem.
-/

open scoped MatrixGroups
namespace ModularForm
noncomputable section

private theorem weber_theta_numerator_reduction (g : SL(2, ℤ)) :
    weberThetaNumeratorTwentyFour
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g) =
        g 0 1 % 24 + g 1 1 % 24 - g 0 0 % 24 - g 1 0 % 24 := by
  simp only [weberThetaNumeratorTwentyFour, SL_reduction_mod_hom_val, ZMod.val_intCast]
  norm_num

/-- The theta-stabilizer condition can be checked modulo twenty-four. -/
theorem weberTheta_even_iff_reduction (g : SL(2, ℤ)) :
    Even (g 0 1 + g 1 1 - g 0 0 - g 1 0) ↔
      Even (weberThetaNumeratorTwentyFour
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g)) := by
  rw [weber_theta_numerator_reduction]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(g 0 1 % 24 + g 1 1 % 24 - g 0 0 % 24 - g 1 0 % 24) / 2, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    refine ⟨(g 0 1 + g 1 1 - g 0 0 - g 1 0) / 2, ?_⟩
    omega

set_option backward.isDefEq.respectTransparency false in
/-- Half-period conjugation commutes with reduction at the required doubled level. -/
theorem weberThetaConjugateTwelve_reduction (g : SL(2, ℤ))
    (hg : Even (g 0 1 + g 1 1 - g 0 0 - g 1 0))
    (hr : Even (weberThetaNumeratorTwentyFour
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g))) :
    weberThetaConjugateTwelve
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g) hr =
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 12)) (weberThetaConjugate g hg) := by
  have hhalf : ((weberThetaNumeratorTwentyFour
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g) / 2 : ℤ) : ZMod 12) =
        ((g 0 1 + g 1 1 - g 0 0 - g 1 0) / 2 : ℤ) := by
    rw [ZMod.intCast_eq_intCast_iff]
    change ((weberThetaNumeratorTwentyFour
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g) / 2) % 12) =
        ((g 0 1 + g 1 1 - g 0 0 - g 1 0) / 2) % 12
    rw [weber_theta_numerator_reduction]
    omega
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [weberThetaConjugateTwelve, weberThetaConjugate,
    SL_reduction_mod_hom_val, hhalf]

/-- The actual eta-character difference is exactly the finite Weber exponent. -/
theorem weberExponent_reduction (g : SL(2, ℤ))
    (hg : Even (g 0 1 + g 1 1 - g 0 0 - g 1 0))
    (hr : Even (weberThetaNumeratorTwentyFour
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g))) :
    etaExponentTwelve (weberThetaConjugate g hg) - etaExponentTwelve g =
      weberExponentTwentyFour
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g) hr := by
  unfold weberExponentTwentyFour
  rw [weberThetaConjugateTwelve_reduction g hg hr, specialLinearReduction_comp_of_dvd]
  simp only [etaExponentTwelve_eq_finite]

/-- All lifts of a normalized CM unit fix the actual Weber square. -/
theorem weberF_sq_smul_of_cm_unit_reduction (g : SL(2, ℤ)) (m a b r : ZMod 24)
    (h : (a ^ 2 + m * b ^ 2) * r = 1) (hm : m = 11 ∨ m = 19)
    (hmod : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g =
      weberCMUnitMatrixTwentyFour m a b r h) (τ : UpperHalfPlane) :
    weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2 = weberF (τ : ℂ) ^ 2 := by
  have hr : Even (weberThetaNumeratorTwentyFour
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g)) := by
    rw [hmod]
    exact weberCMUnitMatrixTwentyFour_parity m a b r h hm
  have hg := (weberTheta_even_iff_reduction g).mpr hr
  have hz : ∀ hp : Even (weberThetaNumeratorTwentyFour
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g)),
      weberExponentTwentyFour
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g) hp = 0 := by
    rw [hmod]
    intro hp
    exact weberExponentTwentyFour_cmUnitMatrix m a b r h hm
  have he : etaExponentTwelve (weberThetaConjugate g hg) = etaExponentTwelve g := by
    apply sub_eq_zero.mp
    rw [weberExponent_reduction g hg hr]
    exact hz hr
  have hc : etaSquareCharacter (weberThetaConjugate g hg) = etaSquareCharacter g :=
    congrArg etaMultiplierTwelve he
  rw [weberF_sq_smul g hg τ, hc, div_self (etaSquareCharacter_ne_zero g), one_mul]

/-- The two residue classes cover every `m ≡ 3 (mod 8)` prime to three. -/
theorem weberParameter_mod_twentyFour {m : ℕ} (hm8 : m % 8 = 3) (hm3 : ¬ 3 ∣ m) :
    (m : ZMod 24) = 11 ∨ (m : ZMod 24) = 19 := by
  have h3 : m % 3 ≠ 0 := by
    intro hzero
    apply hm3
    exact ⟨m / 3, by omega⟩
  have h24 : m % 24 = 11 ∨ m % 24 = 19 := by omega
  rcases h24 with h11 | h19
  · left
    apply Fin.ext
    exact h11
  · right
    apply Fin.ext
    exact h19

/-- Every normalized lift of an invertible CM centralizer fixes the actual Weber square. -/
theorem weberF_sq_smul_of_cm_centralizer_reduction (g : SL(2, ℤ)) (m : ZMod 24)
    (A : GL (Fin 2) (ZMod 24))
    (hA : Commute (A : Matrix (Fin 2) (Fin 2) (ZMod 24)) !![0, -m; 1, 0])
    (hm : m = 11 ∨ m = 19)
    (hmod : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g =
      A.specialLinearPart) (τ : UpperHalfPlane) :
    weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2 = weberF (τ : ℂ) ^ 2 := by
  have hcomm : Commute (A : Matrix (Fin 2) (Fin 2) (ZMod 24))
      (Algebra.leftMulMatrix (QuadraticAlgebra.basis (-m) 0) QuadraticAlgebra.omega) := by
    simpa [QuadraticAlgebra.leftMulMatrix_eq] using hA
  have hn : (A 0 0 ^ 2 + m * A 1 0 ^ 2) * (A.det.inv : ZMod 24) = 1 := by
    simpa [QuadraticAlgebra.norm_def, pow_two, mul_assoc] using
      (QuadraticAlgebra.norm_mul_inv_det_eq_one_of_commute_leftMulMatrix_omega A hcomm)
  apply weberF_sq_smul_of_cm_unit_reduction g m (A 0 0) (A 1 0) A.det.inv hn hm _ τ
  rw [hmod]
  obtain ⟨h01, h11⟩ :=
    (QuadraticAlgebra.commute_leftMulMatrix_omega_iff
      (a := -m) (b := 0) (A : Matrix (Fin 2) (Fin 2) (ZMod 24))).mp hcomm
  simp only [zero_mul, add_zero] at h11
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.GeneralLinearGroup.specialLinearPart,
    weberCMUnitMatrixTwentyFour, h01, h11]

open BakerHeegnerStark in
/-- Actual CM-compatible torsion automorphisms give Weber-invariant normalized lifts. -/
theorem weberF_sq_smul_of_periodTorsionCMEnd_commute (τ : ℂ) (hτ : τ.im ≠ 0)
    (m : ℤ) (hquad : τ ^ 2 = -(m : ℂ))
    (u : Multiplicative (AddAut (PeriodTorsion τ 24)))
    (hu : ∀ p, u.toAdd (periodTorsionCMEnd τ 24 m hquad p) =
      periodTorsionCMEnd τ 24 m hquad (u.toAdd p))
    (g : SL(2, ℤ)) (hm : (m : ZMod 24) = 11 ∨ (m : ZMod 24) = 19)
    (hg : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g =
      (periodTorsionAutMatrix τ hτ 24 (by decide) u).specialLinearPart)
    (z : UpperHalfPlane) :
    weberF ((g • z : UpperHalfPlane) : ℂ) ^ 2 = weberF (z : ℂ) ^ 2 := by
  exact weberF_sq_smul_of_cm_centralizer_reduction g (m : ZMod 24)
    (periodTorsionAutMatrix τ hτ 24 (by decide) u)
    ((periodTorsionAutMatrix_commute_iff τ hτ 24 (by decide) m hquad u).mpr hu) hm hg z

open BakerHeegnerStark in
/-- Actual curve CM-compatible torsion automorphisms give Weber-invariant normalized lifts. -/
theorem weberF_sq_smul_of_periodCurveTorsionCMEnd_commute [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℤ) (hquad : (τ : ℂ) ^ 2 = -(m : ℂ))
    (u : Multiplicative (AddAut (PeriodCurveTorsion τ 24)))
    (hu : ∀ P, u.toAdd (periodCurveTorsionCMEnd τ 24 m hquad P) =
      periodCurveTorsionCMEnd τ 24 m hquad (u.toAdd P))
    (g : SL(2, ℤ)) (hm : (m : ZMod 24) = 11 ∨ (m : ZMod 24) = 19)
    (hg : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g =
      (periodCurveTorsionAutMatrix τ 24 (by decide) u).specialLinearPart)
    (z : UpperHalfPlane) :
    weberF ((g • z : UpperHalfPlane) : ℂ) ^ 2 = weberF (z : ℂ) ^ 2 := by
  exact weberF_sq_smul_of_cm_centralizer_reduction g (m : ZMod 24)
    (periodCurveTorsionAutMatrix τ 24 (by decide) u)
    ((periodCurveTorsionAutMatrix_commute_iff τ 24 (by decide) m hquad u).mpr hu) hm hg z

end
end ModularForm
