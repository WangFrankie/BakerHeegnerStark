/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Weber.JointPolynomial
import BakerHeegnerStark.ModularForms.Weber.BranchPowerSeries
import BakerHeegnerStark.ComplexMultiplication.CyclicNeighbors.QExpansion
import BakerHeegnerStark.ModularForms.ModularPolynomial.CoefficientQExpansion
import BakerHeegnerStark.ModularForms.QExpansion.Identity

/-!
# Full cyclotomic q-expansion of the actual joint polynomial

Both polynomial variables are retained in the finite product over the actual
paired index. Each factor has the common pole regularization 192. Complete
Cauchy products give convergence on the entire upper half-plane; coefficient
Galois action permutes the same paired factors, entirely formally.
-/

open UpperHalfPlane Polynomial BakerHeegnerStark
open scoped BigOperators MatrixGroups

noncomputable section
namespace ModularForm

/-- Complete scalar coefficient sums commute with multiplication in two formal
polynomial variables. -/
theorem hasSum_powerSeries_bivariate_mul
    {P Q : (PowerSeries ℂ)[X][X]} {p q : ℂ[X][X]} {z : ℂ}
    (hP : ∀ k l, HasSum (fun m : ℕ => ((P.coeff k).coeff l).coeff m * z ^ m)
      ((p.coeff k).coeff l))
    (hQ : ∀ k l, HasSum (fun m : ℕ => ((Q.coeff k).coeff l).coeff m * z ^ m)
      ((q.coeff k).coeff l)) (k l : ℕ) :
    HasSum (fun m : ℕ => (((P * Q).coeff k).coeff l).coeff m * z ^ m)
      (((p * q).coeff k).coeff l) := by
  classical
  have h := hasSum_sum (s := Finset.antidiagonal k) (fun ij _ =>
    hasSum_sum (s := Finset.antidiagonal l) (fun uv _ =>
      PowerSeries.hasSum_coeff_mul (hP ij.1 uv.1) (hQ ij.2 uv.2)))
  convert h using 1 <;>
    simp only [Polynomial.coeff_mul, Polynomial.finsetSum_coeff, map_sum, Finset.sum_mul]

/-- Complete scalar coefficient sums commute with a finite product, retaining
both formal polynomial variables. -/
theorem hasSum_powerSeries_bivariate_prod {ι : Type*} (s : Finset ι)
    (P : ι → (PowerSeries ℂ)[X][X]) (p : ι → ℂ[X][X]) (z : ℂ)
    (h : ∀ i ∈ s, ∀ k l, HasSum
      (fun m : ℕ => (((P i).coeff k).coeff l).coeff m * z ^ m)
      (((p i).coeff k).coeff l)) (k l : ℕ) :
    HasSum (fun m : ℕ => (((∏ i ∈ s, P i).coeff k).coeff l).coeff m * z ^ m)
      (((∏ i ∈ s, p i).coeff k).coeff l) := by
  classical
  induction s using Finset.induction_on generalizing k l with
  | empty =>
      by_cases hk : k = 0
      · subst k
        by_cases hl : l = 0
        · subst l
          simpa using PowerSeries.hasSum_coeff_X_pow 0 z
        · simp [Polynomial.coeff_one, hl]
      · simp [Polynomial.coeff_one, hk]
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact hasSum_powerSeries_bivariate_mul
        (h i (Finset.mem_insert_self i s))
        (fun k l => ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) k l) k l

/-- The full regularized joint product over the actual phase field. The inner
variable is the tuple-separating variable, and the outer variable is the root. -/
def weberJointQPolynomial (a : ℕ) :
    (PowerSeries weberBranchCoefficientField)[X][X] :=
  ∏ p : weberJointIndex,
    (C (C ((PowerSeries.X : PowerSeries weberBranchCoefficientField) ^ 192)) * X -
      C (jointOrbitLinearPolynomial
        (PowerSeries.X ^ 191 * weberBranchSpacePowerSeries (weberJointBranch p))
        (cyclicNeighborWeightedPowerSeries a (weberJointMatrix p))))

private theorem hasSum_jointQFactor {A B D : PowerSeries ℂ} {a b d z : ℂ}
    (hA : HasSum (fun m : ℕ => A.coeff m * z ^ m) a)
    (hB : HasSum (fun m : ℕ => B.coeff m * z ^ m) b)
    (hD : HasSum (fun m : ℕ => D.coeff m * z ^ m) d) (k l : ℕ) :
    HasSum (fun m : ℕ =>
      (((C (C A) * X - C (jointOrbitLinearPolynomial B D) :
        (PowerSeries ℂ)[X][X]).coeff k).coeff l).coeff m * z ^ m)
      (((C (C a) * X - C (jointOrbitLinearPolynomial b d) : ℂ[X][X]).coeff k).coeff l) := by
  cases k with
  | zero =>
      cases l with
      | zero => simpa [jointOrbitLinearPolynomial] using hB.neg
      | succ l =>
          cases l with
          | zero => simpa [jointOrbitLinearPolynomial] using hD.neg
          | succ l => simp [jointOrbitLinearPolynomial]
  | succ k =>
      cases k with
      | zero =>
          cases l with
          | zero => simpa using hA
          | succ l => simp
      | succ k => simp

private theorem regularized_joint_product {ι : Type*} [Fintype ι]
    (v w : ι → ℂ) (z : ℂ) :
    (∏ i, (C (C (z ^ 192)) * X -
      C (jointOrbitLinearPolynomial (z ^ 192 * v i) (z ^ 192 * w i)))) =
      C (C (z ^ (192 * Fintype.card ι))) * jointOrbitPolynomial v w := by
  classical
  have hf (i : ι) :
      (C (C (z ^ 192)) * X -
        C (jointOrbitLinearPolynomial (z ^ 192 * v i) (z ^ 192 * w i))) =
      C (C (z ^ 192)) * (X - C (jointOrbitLinearPolynomial (v i) (w i))) := by
    simp only [jointOrbitLinearPolynomial, mul_sub, ← C_mul, mul_add, ← mul_assoc]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, ← map_pow, ← pow_mul,
    jointOrbitPolynomial]

/-- Every complete scalar coefficient series converges throughout `ℍ` to the
corresponding actual joint coefficient times the single common pole shift. -/
theorem hasSum_weberJointQPolynomial_coeff_coeff (a k l : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ =>
      ((((weberJointQPolynomial a).coeff k).coeff l).coeff m : ℂ) *
        Function.Periodic.qParam 24 (τ : ℂ) ^ m)
      (Function.Periodic.qParam 24 (τ : ℂ) ^ (192 * Fintype.card weberJointIndex) *
        ((weberJointPolynomial a τ).coeff k).coeff l) := by
  classical
  let f := algebraMap weberBranchCoefficientField ℂ
  let z := Function.Periodic.qParam 24 (τ : ℂ)
  let P := (weberJointQPolynomial a).map (Polynomial.mapRingHom (PowerSeries.map f))
  have hf (p : weberJointIndex) : HasSum (fun m : ℕ =>
      (PowerSeries.X ^ 191 * PowerSeries.map f
        (weberBranchSpacePowerSeries (weberJointBranch p))).coeff m * z ^ m)
      (z ^ 192 * (weberJointBranch p : UpperHalfPlane → ℂ) τ) := by
    have hb : HasSum (fun m : ℕ =>
        (PowerSeries.map f (weberBranchSpacePowerSeries (weberJointBranch p))).coeff m * z ^ m)
        (z * (weberJointBranch p : UpperHalfPlane → ℂ) τ) := by
      simpa only [PowerSeries.coeff_map, f, z, IntermediateField.algebraMap_apply] using
        hasSum_weberBranchSpacePowerSeries (weberJointBranch p) τ
    simpa only [← mul_assoc, ← pow_succ] using PowerSeries.hasSum_coeff_X_pow_mul hb 191
  have hw (p : weberJointIndex) : HasSum (fun m : ℕ =>
      (PowerSeries.map f (cyclicNeighborWeightedPowerSeries a (weberJointMatrix p))).coeff m * z ^ m)
      (z ^ 192 * cyclicNeighborWeighted a (weberJointMatrix p) τ) := by
    simpa only [PowerSeries.coeff_map, f, z, IntermediateField.algebraMap_apply] using
      hasSum_cyclicNeighborWeightedPowerSeries a (weberJointMatrix p) τ
  have hs := hasSum_powerSeries_bivariate_prod Finset.univ
    (fun p : weberJointIndex =>
      C (C ((PowerSeries.X : PowerSeries ℂ) ^ 192)) * X -
        C (jointOrbitLinearPolynomial
          (PowerSeries.X ^ 191 * PowerSeries.map f
            (weberBranchSpacePowerSeries (weberJointBranch p)))
          (PowerSeries.map f (cyclicNeighborWeightedPowerSeries a (weberJointMatrix p)))))
    (fun p : weberJointIndex => C (C (z ^ 192)) * X -
      C (jointOrbitLinearPolynomial
        (z ^ 192 * (weberJointBranch p : UpperHalfPlane → ℂ) τ)
        (z ^ 192 * cyclicNeighborWeighted a (weberJointMatrix p) τ))) z
    (fun p _ k l => hasSum_jointQFactor (PowerSeries.hasSum_coeff_X_pow 192 z)
      (hf p) (hw p) k l) k l
  rw [regularized_joint_product, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul] at hs
  have hm : P = ∏ p : weberJointIndex,
      (C (C ((PowerSeries.X : PowerSeries ℂ) ^ 192)) * X -
        C (jointOrbitLinearPolynomial
          (PowerSeries.X ^ 191 * PowerSeries.map f
            (weberBranchSpacePowerSeries (weberJointBranch p)))
          (PowerSeries.map f (cyclicNeighborWeightedPowerSeries a (weberJointMatrix p))))) := by
    simp [P, weberJointQPolynomial, Polynomial.map_prod, jointOrbitLinearPolynomial]
  rw [← hm] at hs
  simpa only [P, Polynomial.coe_mapRingHom, Polynomial.coeff_map, PowerSeries.coeff_map,
    f, IntermediateField.algebraMap_apply, z, weberJointPolynomial] using hs

/-- Character diagonals multiply exactly as their units do. -/
theorem weberCoefficientDiagonal_mul (u v : (ZMod 24)ˣ) :
    weberCoefficientDiagonal (u * v) =
      weberCoefficientDiagonal u * weberCoefficientDiagonal v := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weberCoefficientDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- Left multiplication on the actual coefficient-automorphism coordinate. -/
def weberJointCoefficientPerm
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField) :
    Equiv.Perm weberJointIndex :=
  { toFun := fun p => (σ * p.1, p.2)
    invFun := fun p => (σ⁻¹ * p.1, p.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp }

/-- The paired matrix changes by the same right character diagonal as the
entire neighboring series. -/
theorem weberJointMatrix_coefficientPerm
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField)
    (p : weberJointIndex) :
    weberJointMatrix (weberJointCoefficientPerm σ p) =
      weberJointMatrix p * weberCoefficientDiagonal (weberBranchCyclotomicCharacter σ) := by
  change (p.2 : GL (Fin 2) (ZMod 24)) *
    weberCoefficientDiagonal (weberBranchCyclotomicCharacter (σ * p.1)) = _
  rw [map_mul, mul_comm (weberBranchCyclotomicCharacter σ),
    weberCoefficientDiagonal_mul, ← mul_assoc]
  rfl

/-- Actual coefficient conjugation permutes both coordinates of every formal
factor by one and the same attained paired index. -/
theorem map_weberJointQPolynomial_eq_self (a : ℕ)
    (σ : weberBranchCoefficientField ≃ₐ[ℚ] weberBranchCoefficientField) :
    (weberJointQPolynomial a).map
      (Polynomial.mapRingHom (PowerSeries.map σ.toRingHom)) = weberJointQPolynomial a := by
  classical
  have hb (p : weberJointIndex) :
      PowerSeries.map σ.toRingHom (weberBranchSpacePowerSeries (weberJointBranch p)) =
        weberBranchSpacePowerSeries (weberJointBranch (weberJointCoefficientPerm σ p)) := by
    rw [← weberBranchSpacePowerSeries_coefficientAction]
    simp only [weberJointBranch, weberJointCoefficientPerm, Equiv.coe_fn_mk,
      weberBranchCoefficientAction_mul]
  have hw (p : weberJointIndex) :
      PowerSeries.map σ.toRingHom (cyclicNeighborWeightedPowerSeries a (weberJointMatrix p)) =
        cyclicNeighborWeightedPowerSeries a (weberJointMatrix (weberJointCoefficientPerm σ p)) := by
    rw [cyclicNeighborWeightedPowerSeries_coefficientAction, weberJointMatrix_coefficientPerm]
  simp only [weberJointQPolynomial, Polynomial.map_prod, Polynomial.coe_mapRingHom,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_pow, map_mul, map_pow, PowerSeries.map_X, jointOrbitLinearPolynomial,
    Polynomial.map_add, hb, hw]
  apply Fintype.prod_equiv (weberJointCoefficientPerm σ)
  intro p
  set_option maxRecDepth 10000 in
    rfl

/-- Any bounded-degree complex representative of an actual scalar coefficient
has exactly the embedded full joint series as its width-24 regularization. -/
theorem qRegularization_weberJointPolynomial_repr (a k l : ℕ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ 8 * Fintype.card weberJointIndex)
    (hrep : ∀ τ : UpperHalfPlane,
      ((weberJointPolynomial a τ).coeff k).coeff l = P.eval (jInvariant τ)) :
    P.qRegularization
      (PowerSeries.expand 24 (by decide)
        (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator))
      24 (8 * Fintype.card weberJointIndex) =
      PowerSeries.map (algebraMap weberBranchCoefficientField ℂ)
        ((weberJointQPolynomial a).coeff k |>.coeff l) := by
  apply PowerSeries.eq_of_hasSum_qParam (h := 24) (by norm_num)
    (f := fun τ => Function.Periodic.qParam 24 (τ : ℂ) ^
      (24 * (8 * Fintype.card weberJointIndex)) * P.eval (jInvariant τ))
  · intro τ
    exact Polynomial.hasSum_qRegularization P _ 24 _ hdeg _ _
      (hasSum_jInvariantIntegralNumerator_commonWidth (by decide : 0 < 24) τ)
  · intro τ
    have h := hasSum_weberJointQPolynomial_coeff_coeff a k l τ
    simpa only [PowerSeries.coeff_map, IntermediateField.algebraMap_apply,
      hrep τ, show 192 * Fintype.card weberJointIndex =
        24 * (8 * Fintype.card weberJointIndex) by omega] using h

end ModularForm
