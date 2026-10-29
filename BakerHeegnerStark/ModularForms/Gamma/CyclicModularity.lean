/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.Gamma.DeterminantThree
import BakerHeegnerStark.ModularForms.Gamma.CyclicSublattice
import BakerHeegnerStark.ModularForms.ModularPolynomial.Modularity

/-!
# Modular Twisted Gamma Products

At levels congruent to two modulo three, the cubic character on the
right-normalized Hermite matrix cancels the two actual gamma multipliers.
The existing Hermite right permutation therefore permutes the actual twisted
roots, not merely their cubes. Their finite product is modular, its
coefficients are holomorphic with polynomial cusp growth, and hence it is a
bivariate polynomial in j. No arithmetic coefficient descent is asserted.
-/

open Matrix UpperHalfPlane ModularForm Polynomial Asymptotics
open scoped MatrixGroups Manifold Polynomial.Bivariate

noncomputable section

namespace BakerHeegnerStark

private def gammaHermiteThree (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  !![(t.1 : ZMod 3), (t.2.1 : ZMod 3); 0, (t.2.2 : ZMod 3)]

private theorem gammaHermiteThree_map (t : ℕ × ℕ × ℕ) :
    (!![(t.1 : ℤ), (t.2.1 : ℤ); 0, (t.2.2 : ℤ)] :
      Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod 3)) = gammaHermiteThree t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gammaHermiteThree]

private theorem gammaLevelThree {N : ℕ} (hN3 : N % 3 = 2) : (N : ZMod 3) = -1 := by
  calc
    (N : ZMod 3) = ((N % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    _ = -1 := by rw [hN3]; decide

private theorem gammaHermiteThree_ad {N : ℕ} (hN : 0 < N) (hN3 : N % 3 = 2)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    (t.1.1 : ZMod 3) * (t.1.2.2 : ZMod 3) = -1 := by
  have had := ((mem_cyclicSublatticeTriples hN).mp t.2).1
  rw [← Nat.cast_mul, had]
  exact gammaLevelThree hN3

private theorem gammaHermiteThree_det {N : ℕ} (hN : 0 < N) (hN3 : N % 3 = 2)
    (t : {t // t ∈ cyclicSublatticeTriples N}) : (gammaHermiteThree t.1).det = -1 := by
  simpa [gammaHermiteThree, Matrix.det_fin_two] using gammaHermiteThree_ad hN hN3 t

private theorem gammaHermiteThree_phase {N : ℕ} (hN : 0 < N) (hN3 : N % 3 = 2)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    gammaPhaseThree ^ (t.1.1 * t.1.2.1) =
      (gammaNegativeDetThree (gammaHermiteThree t.1) (gammaHermiteThree_det hN hN3 t))⁻¹ := by
  rw [← gammaMultiplierThree_natCast, Nat.cast_mul]
  exact (gammaNegativeDetThree_upper_inv _ _ _ (gammaHermiteThree_ad hN hN3 t)).symm

private theorem cyclicSublatticeGammaRoot_eq_character {N : ℕ}
    (hN : 0 < N) (hN3 : N % 3 = 2) (t : {t // t ∈ cyclicSublatticeTriples N})
    (τ : UpperHalfPlane) :
    cyclicSublatticeGammaRoot t.1 τ =
      (gammaNegativeDetThree (gammaHermiteThree t.1) (gammaHermiteThree_det hN hN3 t))⁻¹ *
        gamma₂ τ * gamma₂ (cyclicSublatticePoint t.1 τ) := by
  rw [cyclicSublatticeGammaRoot, gammaHermiteThree_phase hN hN3 t]

private theorem gammaTriple_pos {N : ℕ} (hN : 0 < N)
    (t : {t // t ∈ cyclicSublatticeTriples N}) : 0 < t.1.1 ∧ 0 < t.1.2.2 := by
  obtain ⟨had, hbd, _⟩ := (mem_cyclicSublatticeTriples hN).mp t.2
  have hd : 0 < t.1.2.2 := by omega
  have ha : 0 < t.1.1 := by
    by_contra h
    have hz : t.1.1 = 0 := by omega
    simp [hz] at had
    omega
  exact ⟨ha, hd⟩

/-- The Hermite right permutation preserves the actual twisted gamma roots. -/
theorem cyclicSublatticeGammaRoot_cyclicSublatticeRightPerm {N : ℕ}
    (hN : 0 < N) (hN3 : N % 3 = 2) (γ : SL(2, ℤ))
    (t : {t // t ∈ cyclicSublatticeTriples N}) (τ : UpperHalfPlane) :
    cyclicSublatticeGammaRoot (cyclicSublatticeRightPerm hN γ t).1 τ =
      cyclicSublatticeGammaRoot t.1 (γ • τ) := by
  let u := cyclicSublatticeRightPerm hN γ t
  obtain ⟨haT, hdT⟩ := gammaTriple_pos hN t
  obtain ⟨haU, hdU⟩ := gammaTriple_pos hN u
  obtain ⟨κ, hκ⟩ := exists_smul_eq_cyclicSublatticeRightPerm hN γ t
  have hmat := congrArg Subtype.val hκ
  rw [FixedDetMatrices.smul_coe] at hmat
  change (κ : Matrix (Fin 2) (Fin 2) ℤ) *
      ((cyclicSublatticeMatrix t).1 * (γ : Matrix (Fin 2) (Fin 2) ℤ)) =
    (cyclicSublatticeMatrix u).1 at hmat
  have hmatInt : (!![(u.1.1 : ℤ), (u.1.2.1 : ℤ); 0, (u.1.2.2 : ℤ)] :
      Matrix (Fin 2) (Fin 2) ℤ) =
      (κ : Matrix (Fin 2) (Fin 2) ℤ) *
        (!![(t.1.1 : ℤ), (t.1.2.1 : ℤ); 0, (t.1.2.2 : ℤ)] :
          Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    simpa only [u, cyclicSublatticeMatrix, Matrix.mul_assoc] using hmat.symm
  have hmod : gammaHermiteThree u.1 =
      (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) κ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        gammaHermiteThree t.1 *
        (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    have hm := congrArg
      (fun A : Matrix (Fin 2) (Fin 2) ℤ => A.map (Int.castRingHom (ZMod 3))) hmatInt
    rw [Matrix.map_mul, Matrix.map_mul, gammaHermiteThree_map, gammaHermiteThree_map] at hm
    exact hm
  let χt := gammaNegativeDetThree (gammaHermiteThree t.1) (gammaHermiteThree_det hN hN3 t)
  let χu := gammaNegativeDetThree (gammaHermiteThree u.1) (gammaHermiteThree_det hN hN3 u)
  have hχ : χu = gammaCharacter κ * χt * (gammaCharacter γ)⁻¹ :=
    gammaNegativeDetThree_of_matrix_relation _ _ _ _
      (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) γ)
      (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) κ) hmod
  have hpoint := cyclicSublatticePoint_of_matrix_relation t.1 u.1
    haT hdT haU hdU γ κ hmatInt τ
  change cyclicSublatticeGammaRoot u.1 τ = cyclicSublatticeGammaRoot t.1 (γ • τ)
  rw [cyclicSublatticeGammaRoot_eq_character hN hN3 u,
    cyclicSublatticeGammaRoot_eq_character hN hN3 t, hpoint,
    ModularForm.gamma₂_smul, ModularForm.gamma₂_smul]
  change χu⁻¹ * gamma₂ τ *
      (gammaCharacter κ * gamma₂ (cyclicSublatticePoint t.1 (γ • τ))) =
    χt⁻¹ * (gammaCharacter γ * gamma₂ τ) *
      gamma₂ (cyclicSublatticePoint t.1 (γ • τ))
  have hk : gammaCharacter κ ≠ 0 := gammaCharacterThree_ne_zero _
  have hg : gammaCharacter γ ≠ 0 := gammaCharacterThree_ne_zero _
  have ht : χt ≠ 0 := gammaNegativeDetThree_ne_zero _ _
  rw [hχ]
  field_simp [hk, hg, ht]

/-- The monic product of the actual character-twisted cyclic-sublattice roots. -/
def cyclicSublatticeGammaPolynomial (N : ℕ) (τ : UpperHalfPlane) : ℂ[X] :=
  ∏ t ∈ cyclicSublatticeTriples N, (X - C (cyclicSublatticeGammaRoot t τ))

theorem monic_cyclicSublatticeGammaPolynomial (N : ℕ) (τ : UpperHalfPlane) :
    (cyclicSublatticeGammaPolynomial N τ).Monic := by
  classical
  exact monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_cyclicSublatticeGammaPolynomial (N : ℕ) (τ : UpperHalfPlane) :
    (cyclicSublatticeGammaPolynomial N τ).natDegree = (cyclicSublatticeTriples N).card := by
  classical
  unfold cyclicSublatticeGammaPolynomial
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp

/-- The actual twisted product is invariant under the whole integral modular group. -/
theorem cyclicSublatticeGammaPolynomial_smul {N : ℕ} (hN : 0 < N) (hN3 : N % 3 = 2)
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    cyclicSublatticeGammaPolynomial N (γ • τ) = cyclicSublatticeGammaPolynomial N τ := by
  classical
  unfold cyclicSublatticeGammaPolynomial
  let e := cyclicSublatticeRightPerm hN γ
  refine Finset.prod_bij (fun t ht => (e ⟨t, ht⟩).1) (fun t ht => (e ⟨t, ht⟩).2) ?_ ?_ ?_
  · intro a ha b hb hab
    have heq : e ⟨a, ha⟩ = e ⟨b, hb⟩ := Subtype.ext hab
    exact congrArg Subtype.val (e.injective heq)
  · intro b hb
    refine ⟨(e.symm ⟨b, hb⟩).1, (e.symm ⟨b, hb⟩).2, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
  · intro t ht
    exact congrArg (fun z : ℂ => (X - C z : ℂ[X]))
      (cyclicSublatticeGammaRoot_cyclicSublatticeRightPerm hN hN3 γ ⟨t, ht⟩ τ).symm

/-- Every coefficient of the actual twisted product is modular invariant. -/
theorem cyclicSublatticeGammaPolynomial_coeff_smul {N : ℕ}
    (hN : 0 < N) (hN3 : N % 3 = 2) (k : ℕ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    (cyclicSublatticeGammaPolynomial N (γ • τ)).coeff k =
      (cyclicSublatticeGammaPolynomial N τ).coeff k :=
  congrArg (fun p : ℂ[X] => p.coeff k) (cyclicSublatticeGammaPolynomial_smul hN hN3 γ τ)

/-- The actual twisted product has holomorphic coefficient functions. -/
theorem mdifferentiable_cyclicSublatticeGammaPolynomial_coeff {N : ℕ} (hN : 0 < N) (k : ℕ) :
    MDiff (fun τ => (cyclicSublatticeGammaPolynomial N τ).coeff k) := by
  apply mdifferentiable_prod_X_sub_C_coeff
  intro t ht
  obtain ⟨ha, hd⟩ := gammaTriple_pos hN ⟨t, ht⟩
  exact mdifferentiable_cyclicSublatticeGammaRoot ha hd

/-- Every actual coefficient has an explicit polynomial bound at the cusp. -/
theorem isBigO_cyclicSublatticeGammaPolynomial_coeff {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (fun τ => (cyclicSublatticeGammaPolynomial N τ).coeff k)
      =O[atImInfty] (fun τ => jInvariant τ ^ ((N + 1) * (cyclicSublatticeTriples N).card)) :=
  isBigO_prod_X_sub_C_coeff (cyclicSublatticeTriples N) cyclicSublatticeGammaRoot jInvariant
    (N + 1) eventually_one_le_norm_jInvariant
    (fun _ ht => isBigO_cyclicSublatticeGammaRoot_of_mem hN ht) k

/-- At levels congruent to two modulo three, a complex bivariate polynomial
realizes the entire actual twisted product at every upper-half-plane point.
Rationality or integrality of its coefficients is not asserted here. -/
theorem exists_complex_gammaModularPolynomial {N : ℕ} (hN : 0 < N) (hN3 : N % 3 = 2) :
    ∃ Ψ : ℂ[X][Y], ∀ τ : UpperHalfPlane,
      aevalAeval (C (jInvariant τ)) X Ψ = cyclicSublatticeGammaPolynomial N τ :=
  exists_bivariate_polynomial_jInvariant_of_isBigO (cyclicSublatticeGammaPolynomial N)
    (cyclicSublatticeTriples N).card ((N + 1) * (cyclicSublatticeTriples N).card)
    (natDegree_cyclicSublatticeGammaPolynomial N)
    (mdifferentiable_cyclicSublatticeGammaPolynomial_coeff hN)
    (isBigO_cyclicSublatticeGammaPolynomial_coeff hN)
    (cyclicSublatticeGammaPolynomial_smul hN hN3)

end BakerHeegnerStark
