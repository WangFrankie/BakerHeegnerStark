/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.CyclicNeighbors.Data
import BakerHeegnerStark.ModularForms.Weber.CoefficientConjugation
import BakerHeegnerStark.ModularForms.QExpansion.CyclotomicPowerSeries
import BakerHeegnerStark.ModularForms.QExpansion.PolynomialAnalytic

/-!
# Actual neighboring kernels and complete cyclotomic series

The actual character diagonal acts on the prescribed cyclic-kernel coordinates
by the existing coprime translation-residue permutation. The full neighboring
j-series therefore have the exact same formal coefficient action inside the
actual Weber phase field. Their complex embeddings recover the actual analytic
series, convergent throughout the upper half-plane. Expanding to width twenty-four
and shifting by the proven common pole order 192 gives simultaneous series for
the entire neighboring tuple and its fixed natural-power weighting. These
coefficient identities are formal; no field automorphism is passed through an
infinite complex sum, and no CM evaluation reciprocity is assumed.
-/

open ModularForm
open scoped MatrixGroups BigOperators

noncomputable section
namespace BakerHeegnerStark

private theorem neighborCyclotomicLevel_pos {N : ℕ} (hN : N = 3 ∨ N = 8) : 0 < N := by
  rcases hN with rfl | rfl <;> decide

private theorem neighborCyclotomicLevel_dvd {N : ℕ} (hN : N = 3 ∨ N = 8) : N ∣ 24 := by
  rcases hN with rfl | rfl <;> decide

/-- The actual character diagonal acts on Hermite labels by the already proved
coprime translation-residue permutation, in the prescribed period coordinates. -/
theorem cyclicNeighborPerm_weberCoefficientDiagonal {N : ℕ} (hN : N = 3 ∨ N = 8)
    (u : (ZMod 24)ˣ) :
    cyclicNeighborPerm hN (weberCoefficientDiagonal u) =
      cyclicSublatticeResiduePerm (neighborCyclotomicLevel_pos hN) (u : ZMod 24).val
        ((ZMod.val_coe_unit_coprime u).of_dvd_right (neighborCyclotomicLevel_dvd hN)) := by
  classical
  let hpos := neighborCyclotomicLevel_pos hN
  let : NeZero N := ⟨Nat.ne_of_gt hpos⟩
  let π := ZMod.castHom (neighborCyclotomicLevel_dvd hN) (ZMod N)
  let v : (ZMod N)ˣ := Units.map π u
  let U := periodCoordinateGL (Matrix.GeneralLinearGroup.map π (weberCoefficientDiagonal u))
  have hcast : π (u : ZMod 24) = ((u : ZMod 24).val : ZMod N) :=
    (congrArg π (ZMod.natCast_zmod_val (u : ZMod 24))).symm.trans (map_natCast π _)
  apply Equiv.ext
  intro t
  let s := cyclicSublatticeResiduePerm hpos (u : ZMod 24).val
    ((ZMod.val_coe_unit_coprime u).of_dvd_right (neighborCyclotomicLevel_dvd hN)) t
  let M := periodCoordinateMatrix ((cyclicSublatticeMatrix t).val.map (Int.castRingHom (ZMod N)))
  let Q := periodCoordinateMatrix ((cyclicSublatticeMatrix s).val.map (Int.castRingHom (ZMod N)))
  let q : ZMod N := (((u : ZMod 24).val * t.val.2.1 / t.val.2.2 : ℕ) : ZMod N)
  let K : GL (Fin 2) (ZMod N) :=
    ⟨!![(v : ZMod N), q; 0, 1], !![(↑(v⁻¹) : ZMod N), -(↑(v⁻¹) : ZMod N) * q; 0, 1], by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two], by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hq : (t.val.2.2 : ZMod N) * q +
      (((u : ZMod 24).val * t.val.2.1 % t.val.2.2 : ℕ) : ZMod N) =
        ((u : ZMod 24).val : ZMod N) * (t.val.2.1 : ZMod N) := by
    have he := congrArg (fun n : ℕ => (n : ZMod N))
      (Nat.mod_add_div ((u : ZMod 24).val * t.val.2.1) t.val.2.2)
    simp only [Nat.cast_add, Nat.cast_mul] at he
    change (t.val.2.2 : ZMod N) * q + _ = _
    dsimp only [q]
    linear_combination he
  have hcols (r : {r // r ∈ cyclicSublatticeTriples N}) :
      periodCoordinateMatrix ((cyclicSublatticeMatrix r).val.map (Int.castRingHom (ZMod N))) =
        !![(r.val.2.2 : ZMod N), (r.val.2.1 : ZMod N); 0, (r.val.1 : ZMod N)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [periodCoordinateMatrix, cyclicSublatticeMatrix]
  have hU : (U : Matrix (Fin 2) (Fin 2) (ZMod N)) = !![π (u : ZMod 24), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, periodCoordinateGL, periodCoordinateMatrix, weberCoefficientDiagonal]
  have hvcast : (v : ZMod N) = ((u : ZMod 24).val : ZMod N) := hcast
  have hM : (U : Matrix (Fin 2) (Fin 2) (ZMod N)) * M =
      Q * (K : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    dsimp only [M, Q]
    rw [hU, hcols t, hcols s]
    simp only [s, cyclicSublatticeResiduePerm_apply_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [K, Matrix.mul_apply, Fin.sum_univ_two, hcast, hvcast]
    all_goals first | exact hq.symm | ring
  apply cyclicResidueKernel_injective hN
  change cyclicResidueKernel N (cyclicKernelAction hN U t).val = cyclicResidueKernel N s.val
  rw [← cyclicKernelAction_spec, cyclicResidueKernel_eq_image_columns hpos t,
    cyclicResidueKernel_eq_image_columns hpos s, Finset.image_image]
  change Finset.univ.image ((U : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec ∘ M.mulVec) =
    Finset.univ.image Q.mulVec
  have hvec : (U : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec ∘ M.mulVec =
      Q.mulVec ∘ (K : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec := by
    funext x
    simp only [Function.comp_apply, Matrix.mulVec_mulVec, hM]
  rw [hvec, ← Finset.image_image]
  have hsur : Function.Surjective (K : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec :=
    (Matrix.GeneralLinearGroup.toLin K).toLinearEquiv.surjective
  rw [Finset.image_univ_of_surjective hsur]

/-- The level-three/eight common phase inside the actual Weber phase field. -/
def cyclicNeighborPhase (N : ℕ) : weberBranchCoefficientField :=
  weberBranchPhase ^ (24 / N)

theorem cyclicNeighborPhase_pow {N : ℕ} (hN : N = 3 ∨ N = 8) :
    cyclicNeighborPhase N ^ N = 1 := by
  have h := isPrimitiveRoot_weberBranchPhase.pow_eq_one
  rcases hN with rfl | rfl <;> simpa [cyclicNeighborPhase, ← pow_mul] using h

/-- The embedded phase is the actual normalized complex translation phase. -/
theorem coe_cyclicNeighborPhase {N : ℕ} (hN : N = 3 ∨ N = 8) :
    (cyclicNeighborPhase N : ℂ) = cyclicSublatticePhase 1 N := by
  rcases hN with rfl | rfl
  all_goals
    simp only [cyclicNeighborPhase, IntermediateField.coe_pow, coe_weberBranchPhase,
      zeta48_sq, cyclicSublatticePhase]
    rw [← Complex.exp_nat_mul]
    congr 1; norm_num; ring

private theorem neighborCyclotomicTriple_a_pos {N : ℕ} (hN : N = 3 ∨ N = 8)
    (t : {t // t ∈ cyclicSublatticeTriples N}) : 0 < t.val.1 := by
  have had := ((mem_cyclicSublatticeTriples (neighborCyclotomicLevel_pos hN)).mp t.property).1
  by_contra h
  have hz : t.val.1 = 0 := by omega
  simp [hz] at had
  have := neighborCyclotomicLevel_pos hN
  omega

/-- The full neighboring root series over the actual common phase field, in
its level-N parameter and with its genuine square-a pole regularization. -/
def cyclicNeighborRootPowerSeries {N : ℕ} (hN : N = 3 ∨ N = 8)
    (t : {t // t ∈ cyclicSublatticeTriples N}) : PowerSeries weberBranchCoefficientField :=
  cyclotomicRootQExpansion (cyclicNeighborPhase N) t.val (neighborCyclotomicTriple_a_pos hN t)

/-- Embedding the full field-valued series recovers the actual complex series. -/
theorem map_cyclicNeighborRootPowerSeries {N : ℕ} (hN : N = 3 ∨ N = 8)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    PowerSeries.map (algebraMap weberBranchCoefficientField ℂ) (cyclicNeighborRootPowerSeries hN t) =
      cyclicSublatticeRootQExpansion t.val (neighborCyclotomicTriple_a_pos hN t) := by
  unfold cyclicNeighborRootPowerSeries
  rw [map_cyclotomicRootQExpansion,
    show algebraMap weberBranchCoefficientField ℂ (cyclicNeighborPhase N) =
      cyclicSublatticePhase 1 N from coe_cyclicNeighborPhase hN]
  exact cyclotomicRootQExpansion_complex (neighborCyclotomicLevel_pos hN) t.property _

/-- Formal coefficient conjugation is exactly the actual character-diagonal
permutation of the neighboring kernel labels. No analytic conjugation is used. -/
theorem cyclicNeighborRootPowerSeries_coefficientAction {N : ℕ} (hN : N = 3 ∨ N = 8)
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    PowerSeries.map σ.toRingHom (cyclicNeighborRootPowerSeries hN t) =
      cyclicNeighborRootPowerSeries hN
        (cyclicNeighborPerm hN (weberCoefficientDiagonal (weberBranchCyclotomicCharacter σ)) t) := by
  have hσ : σ.toRingHom (cyclicNeighborPhase N) =
      cyclicNeighborPhase N ^ (weberBranchCyclotomicCharacter σ : ZMod 24).val := by
    change σ (cyclicNeighborPhase N) = _
    simp only [cyclicNeighborPhase, map_pow, ← weberBranchCyclotomicCharacter_spec,
      ← pow_mul]
    rw [Nat.mul_comm]
  unfold cyclicNeighborRootPowerSeries
  rw [map_cyclotomicRootQExpansion, cyclicNeighborPerm_weberCoefficientDiagonal, hσ]
  exact (cyclotomicRootQExpansion_residuePerm (neighborCyclotomicLevel_pos hN)
    (cyclicNeighborPhase N) (cyclicNeighborPhase_pow hN)
    (weberBranchCyclotomicCharacter σ : ZMod 24).val
    ((ZMod.val_coe_unit_coprime (weberBranchCyclotomicCharacter σ)).of_dvd_right
      (neighborCyclotomicLevel_dvd hN)) t).symm

/-- The entire embedded neighboring series converges to the actual regularized
j-value throughout the upper half-plane. -/
theorem hasSum_cyclicNeighborRootPowerSeries {N : ℕ} (hN : N = 3 ∨ N = 8)
    (t : {t // t ∈ cyclicSublatticeTriples N}) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => ((cyclicNeighborRootPowerSeries hN t).coeff n : ℂ) *
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ n)
      (Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ (t.val.1 * t.val.1) *
        jInvariant (cyclicSublatticePoint t.val τ)) := by
  have h := hasSum_cyclicSublatticeRootQExpansion (neighborCyclotomicLevel_pos hN)
    t.property (neighborCyclotomicTriple_a_pos hN t) τ
  rw [← map_cyclicNeighborRootPowerSeries hN t] at h
  simpa only [PowerSeries.coeff_map, IntermediateField.algebraMap_apply] using h

private theorem neighborCyclotomicWidth_pos {N : ℕ} (hN : N = 3 ∨ N = 8) : 0 < 24 / N := by
  rcases hN with rfl | rfl <;> decide

private theorem qParam_neighbor_eq_twentyFour_pow {N : ℕ} (hN : N = 3 ∨ N = 8)
    (τ : UpperHalfPlane) :
    Function.Periodic.qParam (N : ℝ) (τ : ℂ) =
      Function.Periodic.qParam 24 (τ : ℂ) ^ (24 / N) := by
  rcases hN with rfl | rfl
  all_goals
    simp only [Function.Periodic.qParam]
    rw [← Complex.exp_nat_mul]
    congr 1; norm_num; ring

private theorem cyclicNeighborPole_le {N : ℕ} (hN : N = 3 ∨ N = 8)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    (24 / N) * (t.val.1 * t.val.1) ≤ 192 := by
  have had := ((mem_cyclicSublatticeTriples (neighborCyclotomicLevel_pos hN)).mp t.property).1
  have hd : 0 < t.val.2.2 := by
    by_contra h
    have hz : t.val.2.2 = 0 := by omega
    simp [hz] at had
    have := neighborCyclotomicLevel_pos hN
    omega
  have ha : t.val.1 ≤ N := by
    calc
      t.val.1 = t.val.1 * 1 := by simp
      _ ≤ t.val.1 * t.val.2.2 := Nat.mul_le_mul_left _ (by omega)
      _ = N := had
  have hs := Nat.mul_le_mul ha ha
  rcases hN with rfl | rfl <;> norm_num only [Nat.reduceDiv] <;> omega

/-- All actual neighboring j-values have a common width-24 series with the
same pole regularization `q^192`, over the actual Weber phase field. -/
def cyclicNeighborPowerSeries {N : ℕ} (hN : N = 3 ∨ N = 8)
    (t : {t // t ∈ cyclicSublatticeTriples N}) : PowerSeries weberBranchCoefficientField :=
  PowerSeries.X ^ (192 - (24 / N) * (t.val.1 * t.val.1)) *
    PowerSeries.expand (24 / N) (Nat.ne_of_gt (neighborCyclotomicWidth_pos hN))
      (cyclicNeighborRootPowerSeries hN t)

/-- The same actual diagonal reindexes the full common-width regularized
series; the pole shift is invariant because the Hermite `a` is unchanged. -/
theorem cyclicNeighborPowerSeries_coefficientAction {N : ℕ} (hN : N = 3 ∨ N = 8)
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    PowerSeries.map σ.toRingHom (cyclicNeighborPowerSeries hN t) =
      cyclicNeighborPowerSeries hN
        (cyclicNeighborPerm hN (weberCoefficientDiagonal (weberBranchCyclotomicCharacter σ)) t) := by
  have ha : (cyclicNeighborPerm hN
      (weberCoefficientDiagonal (weberBranchCyclotomicCharacter σ)) t).val.1 = t.val.1 := by
    rw [cyclicNeighborPerm_weberCoefficientDiagonal, cyclicSublatticeResiduePerm_apply_val]
  simp only [cyclicNeighborPowerSeries, map_mul, map_pow, PowerSeries.map_X,
    PowerSeries.map_expand, cyclicNeighborRootPowerSeries_coefficientAction, ha]

/-- The full common-width series converges to `q^192` times the actual
neighboring value throughout the upper half-plane. -/
theorem hasSum_cyclicNeighborPowerSeries {N : ℕ} (hN : N = 3 ∨ N = 8)
    (t : {t // t ∈ cyclicSublatticeTriples N}) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => ((cyclicNeighborPowerSeries hN t).coeff n : ℂ) *
      Function.Periodic.qParam 24 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 24 (τ : ℂ) ^ 192 *
        jInvariant (cyclicSublatticePoint t.val τ)) := by
  let f := algebraMap weberBranchCoefficientField ℂ
  let q := Function.Periodic.qParam 24 (τ : ℂ)
  let p := (24 / N) * (t.val.1 * t.val.1)
  have hbase : HasSum (fun n : ℕ =>
      (PowerSeries.map f (cyclicNeighborRootPowerSeries hN t)).coeff n * q ^ ((24 / N) * n))
      (q ^ p * jInvariant (cyclicSublatticePoint t.val τ)) := by
    simpa only [PowerSeries.coeff_map, f, q, p, IntermediateField.algebraMap_apply,
      qParam_neighbor_eq_twentyFour_pow hN τ, ← pow_mul] using
      hasSum_cyclicNeighborRootPowerSeries hN t τ
  have he := hasSum_powerSeries_expand (Nat.ne_of_gt (neighborCyclotomicWidth_pos hN)) hbase
  have hs := PowerSeries.hasSum_coeff_X_pow_mul he (192 - p)
  have hm : PowerSeries.map f (cyclicNeighborPowerSeries hN t) =
      PowerSeries.X ^ (192 - p) *
        PowerSeries.expand (24 / N) (Nat.ne_of_gt (neighborCyclotomicWidth_pos hN))
          (PowerSeries.map f (cyclicNeighborRootPowerSeries hN t)) := by
    simp only [cyclicNeighborPowerSeries, map_mul, map_pow, PowerSeries.map_X,
      PowerSeries.map_expand, p]
  rw [← hm] at hs
  have hp : 192 - p + p = 192 := Nat.sub_add_cancel (cyclicNeighborPole_le hN t)
  simpa only [PowerSeries.coeff_map, f, q, IntermediateField.algebraMap_apply,
    ← mul_assoc, ← pow_add, hp] using hs

/-- The full common-width series for every coordinate of the actual neighboring tuple. -/
def cyclicNeighborDataPowerSeries (A : GL (Fin 2) (ZMod 24)) :
    cyclicNeighborIndex → PowerSeries weberBranchCoefficientField
  | .inl t => cyclicNeighborPowerSeries (Or.inl rfl) (cyclicNeighborPerm (Or.inl rfl) A t)
  | .inr t => cyclicNeighborPowerSeries (Or.inr rfl) (cyclicNeighborPerm (Or.inr rfl) A t)

/-- Coefficient action right-multiplies the same attached matrix by the actual
character diagonal, simultaneously for all neighboring coordinates. -/
theorem cyclicNeighborDataPowerSeries_coefficientAction
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (A : GL (Fin 2) (ZMod 24)) (i : cyclicNeighborIndex) :
    PowerSeries.map σ.toRingHom (cyclicNeighborDataPowerSeries A i) =
      cyclicNeighborDataPowerSeries
        (A * weberCoefficientDiagonal (weberBranchCyclotomicCharacter σ)) i := by
  rcases i with t | t <;>
    simp only [cyclicNeighborDataPowerSeries, cyclicNeighborPowerSeries_coefficientAction,
      cyclicNeighborPerm_mul, Equiv.Perm.mul_apply]

/-- Each entire coordinate series converges to the actual neighboring value
with the common pole factor, not merely a formal value with the same phase. -/
theorem hasSum_cyclicNeighborDataPowerSeries (A : GL (Fin 2) (ZMod 24))
    (i : cyclicNeighborIndex) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => ((cyclicNeighborDataPowerSeries A i).coeff n : ℂ) *
      Function.Periodic.qParam 24 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 24 (τ : ℂ) ^ 192 * cyclicNeighborData A τ i) := by
  rcases i with t | t
  · exact hasSum_cyclicNeighborPowerSeries (Or.inl rfl) _ τ
  · exact hasSum_cyclicNeighborPowerSeries (Or.inr rfl) _ τ

/-- The full common-width series for the rational-power weighting of the
actual neighboring tuple, with the same fixed natural weights. -/
def cyclicNeighborWeightedPowerSeries (a : ℕ) (A : GL (Fin 2) (ZMod 24)) :
    PowerSeries weberBranchCoefficientField :=
  ∑ k : Fin (Fintype.card cyclicNeighborIndex), PowerSeries.C ((a : weberBranchCoefficientField) ^ k.val) *
    cyclicNeighborDataPowerSeries A ((Fintype.equivFin cyclicNeighborIndex).symm k)

/-- Natural power weights are fixed by coefficient action, so the weighted
series has the same exact character-diagonal matrix law. -/
theorem cyclicNeighborWeightedPowerSeries_coefficientAction
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (a : ℕ) (A : GL (Fin 2) (ZMod 24)) :
    PowerSeries.map σ.toRingHom (cyclicNeighborWeightedPowerSeries a A) =
      cyclicNeighborWeightedPowerSeries a
        (A * weberCoefficientDiagonal (weberBranchCyclotomicCharacter σ)) := by
  simp only [cyclicNeighborWeightedPowerSeries, map_sum, map_mul,
    map_pow, map_natCast, cyclicNeighborDataPowerSeries_coefficientAction]

/-- The entire weighted series converges everywhere to the actual weighted
data, after the single common pole regularization. -/
theorem hasSum_cyclicNeighborWeightedPowerSeries (a : ℕ) (A : GL (Fin 2) (ZMod 24))
    (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => ((cyclicNeighborWeightedPowerSeries a A).coeff n : ℂ) *
      Function.Periodic.qParam 24 (τ : ℂ) ^ n)
      (Function.Periodic.qParam 24 (τ : ℂ) ^ 192 * cyclicNeighborWeighted a A τ) := by
  have hs := hasSum_sum (s := Finset.univ) (fun k _ =>
    (hasSum_cyclicNeighborDataPowerSeries A
      ((Fintype.equivFin cyclicNeighborIndex).symm k) τ).mul_left ((a : ℂ) ^ k.val))
  convert hs using 1
  · funext n
    have hc : (cyclicNeighborWeightedPowerSeries a A).coeff n =
        ∑ k : Fin (Fintype.card cyclicNeighborIndex),
          (a : weberBranchCoefficientField) ^ k.val *
            (cyclicNeighborDataPowerSeries A ((Fintype.equivFin cyclicNeighborIndex).symm k)).coeff n := by
      simp only [cyclicNeighborWeightedPowerSeries, map_sum, PowerSeries.coeff_C_mul]
    rw [hc]
    change algebraMap weberBranchCoefficientField ℂ
        (∑ k : Fin (Fintype.card cyclicNeighborIndex),
          (a : weberBranchCoefficientField) ^ k.val *
            (cyclicNeighborDataPowerSeries A ((Fintype.equivFin cyclicNeighborIndex).symm k)).coeff n) *
          Function.Periodic.qParam 24 (τ : ℂ) ^ n = _
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, map_pow, map_natCast]
    exact mul_assoc _ _ _
  · rw [cyclicNeighborWeighted, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

end BakerHeegnerStark
