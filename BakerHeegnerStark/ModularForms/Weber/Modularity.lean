import BakerHeegnerStark.ModularForms.Eta.Modularity
import BakerHeegnerStark.ModularForms.CyclicSublattice.Mobius

/-!
# The Actual Weber Square on Its Theta Stabilizer

The half-period matrix `H = [1,1;0,2]` conjugates a stabilizing integral matrix
to another integral matrix. The ratio of their proved eta-square characters
is the exact multiplier of the actual Weber square. Its two denominator factors
cancel, without taking roots of a higher-power identity.

Matrices in the principal subgroup of level twenty-four have trivial ratio.
Consequently equal reductions modulo twenty-four act identically on the actual
Weber square. These are modular transformation results, not CM field descent.
-/

open scoped MatrixGroups ModularForm
open BakerHeegnerStark
namespace ModularForm
noncomputable section

/-- Integral conjugation by the half-period matrix on the stabilizer of its theta branch. -/
def weberThetaConjugate (g : SL(2, ℤ))
    (hg : Even (g 0 1 + g 1 1 - g 0 0 - g 1 0)) : SL(2, ℤ) :=
  ⟨!![g 0 0 + g 1 0, (g 0 1 + g 1 1 - g 0 0 - g 1 0) / 2;
      2 * g 1 0, g 1 1 - g 1 0], by
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using g.property
    have hhalf : 2 * ((g 0 1 + g 1 1 - g 0 0 - g 1 0) / 2) =
        g 0 1 + g 1 1 - g 0 0 - g 1 0 := by
      obtain ⟨k, hk⟩ := hg
      omega
    simp only [Matrix.det_fin_two]
    dsimp
    change (g 0 0 + g 1 0) * (g 1 1 - g 1 0) -
      ((g 0 1 + g 1 1 - g 0 0 - g 1 0) / 2) * (2 * g 1 0) = 1
    linear_combination hdet - g 1 0 * hhalf⟩

/-- The half-period conjugate satisfies the exact integral matrix intertwining relation. -/
theorem weberThetaConjugate_relation (g : SL(2, ℤ))
    (hg : Even (g 0 1 + g 1 1 - g 0 0 - g 1 0)) :
    (!![1, 1; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ) =
      (weberThetaConjugate g hg : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 1; 0, 2] := by
  have hhalf : 2 * ((g 0 1 + g 1 1 - g 0 0 - g 1 0) / 2) =
      g 0 1 + g 1 1 - g 0 0 - g 1 0 := by
    obtain ⟨k, hk⟩ := hg
    omega
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [weberThetaConjugate]
  all_goals omega

private theorem weberThetaConjugate_point (g : SL(2, ℤ))
    (hg : Even (g 0 1 + g 1 1 - g 0 0 - g 1 0)) (τ : UpperHalfPlane) :
    cyclicSublatticePoint (1, 1, 2) (g • τ) =
      weberThetaConjugate g hg • cyclicSublatticePoint (1, 1, 2) τ := by
  have hrel := weberThetaConjugate_relation g hg
  have hH : (!![1, 1; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ) =
      (weberThetaConjugate g hg : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 1; 0, 2] *
        ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← hrel, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  simpa only [inv_smul_smul] using
    cyclicSublatticePoint_of_matrix_relation (1, 1, 2) (1, 1, 2)
      (by decide) (by decide) (by decide) (by decide) g⁻¹
      (weberThetaConjugate g hg) hH (g • τ)

set_option backward.isDefEq.respectTransparency false in
private theorem weberThetaConjugate_denom (g : SL(2, ℤ))
    (hg : Even (g 0 1 + g 1 1 - g 0 0 - g 1 0)) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (weberThetaConjugate g hg)
      (cyclicSublatticePoint (1, 1, 2) τ) = UpperHalfPlane.denom g τ := by
  rw [ModularGroup.denom_apply, ModularGroup.denom_apply,
    cyclicSublatticePoint_coe (by decide) (by decide)]
  simp [weberThetaConjugate]
  ring

/-- The exact eta-character ratio for the actual Weber square on its theta stabilizer. -/
theorem weberF_sq_smul (g : SL(2, ℤ))
    (hg : Even (g 0 1 + g 1 1 - g 0 0 - g 1 0)) (τ : UpperHalfPlane) :
    weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2 =
      (etaSquareCharacter (weberThetaConjugate g hg) / etaSquareCharacter g) *
        weberF (τ : ℂ) ^ 2 := by
  have hnum := eta_sq_smul (weberThetaConjugate g hg)
    (cyclicSublatticePoint (1, 1, 2) τ)
  rw [← weberThetaConjugate_point g hg τ, weberThetaConjugate_denom g hg τ] at hnum
  have hnum' : η ((((g • τ : UpperHalfPlane) : ℂ) + 1) / 2) ^ 2 =
      etaSquareCharacter (weberThetaConjugate g hg) * UpperHalfPlane.denom g τ *
        η (((τ : ℂ) + 1) / 2) ^ 2 := by
    simpa only [cyclicSublatticePoint_coe (t := (1, 1, 2)) (by decide) (by decide),
      Nat.cast_one, Nat.cast_ofNat, one_mul] using hnum
  have hden := eta_sq_smul g τ
  simp only [weberF, mul_pow, div_pow]
  rw [hnum', hden]
  field_simp [etaSquareCharacter_ne_zero g, UpperHalfPlane.denom_ne_zero g τ,
    eta_ne_zero τ.im_pos]

/-- The actual Weber square is invariant under the principal level-twenty-four subgroup. -/
theorem weberF_sq_smul_of_mem_Gamma_twenty_four (g : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma 24) (τ : UpperHalfPlane) :
    weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2 = weberF (τ : ℂ) ^ 2 := by
  obtain ⟨ha, hb, hc, hd⟩ := CongruenceSubgroup.Gamma_mem.mp hg
  have h24 : (24 : ℤ) ∣ g 0 1 + g 1 1 - g 0 0 - g 1 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).mp
    simp [ha, hb, hc, hd]
  have heven : Even (g 0 1 + g 1 1 - g 0 0 - g 1 0) := by
    obtain ⟨k, hk⟩ := h24
    exact ⟨12 * k, by omega⟩
  have hhalf : (((g 0 1 + g 1 1 - g 0 0 - g 1 0) / 2 : ℤ) : ZMod 12) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mpr
    obtain ⟨k, hk⟩ := h24
    exact ⟨k, by omega⟩
  have hg12 := principalCongruence_le_of_dvd (by decide : 12 ∣ 24) hg
  obtain ⟨ha12, _, hc12, hd12⟩ := CongruenceSubgroup.Gamma_mem.mp hg12
  have hconj : weberThetaConjugate g heven ∈ CongruenceSubgroup.Gamma 12 := by
    apply CongruenceSubgroup.Gamma_mem.mpr
    simp [weberThetaConjugate, ha12, hc12, hd12, hhalf]
  rw [weberF_sq_smul g heven τ,
    etaSquareCharacter_eq_one_of_mem_Gamma_twelve _ hconj,
    etaSquareCharacter_eq_one_of_mem_Gamma_twelve _ hg12]
  simp

/-- Equal reductions modulo twenty-four give equal actions on the actual Weber square. -/
theorem weberF_sq_smul_of_mod_twenty_four_eq (g h : SL(2, ℤ))
    (hmod : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) g =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 24)) h) (τ : UpperHalfPlane) :
    weberF ((g • τ : UpperHalfPlane) : ℂ) ^ 2 =
      weberF ((h • τ : UpperHalfPlane) : ℂ) ^ 2 := by
  have hk : g * h⁻¹ ∈ CongruenceSubgroup.Gamma 24 := by
    apply CongruenceSubgroup.Gamma_mem'.mpr
    rw [map_mul, map_inv, hmod, mul_inv_cancel]
  simpa only [mul_smul, inv_smul_smul] using
    weberF_sq_smul_of_mem_Gamma_twenty_four (g * h⁻¹) hk (h • τ)

end
end ModularForm
