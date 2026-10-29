/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.QExpansion.Polynomial
import BakerHeegnerStark.ModularForms.QExpansion.Integral
import BakerHeegnerStark.ModularForms.ModularPolynomial.QExpansion

/-!
# Convergent Regularized Polynomial q-Expansions

Full complex power-series sums commute with powers, nonnegative shifts, and
finite sums. Consequently the formal regularization of a polynomial evaluates
to its expected analytic value, even at `q = 0`. The integral numerator of `j`
also has a full expansion in every positive integral width.
-/

noncomputable section

namespace PowerSeries

/-- The monomial series converges at every complex argument. -/
theorem hasSum_coeff_X_pow (k : ℕ) (q : ℂ) :
    HasSum (fun m : ℕ => ((X : PowerSeries ℂ) ^ k).coeff m * q ^ m) (q ^ k) := by
  convert hasSum_ite_eq k (q ^ k) using 1
  funext m
  by_cases hm : m = k <;> simp [coeff_X_pow, hm]

/-- Powers of a convergent full complex series represent powers of its sum. -/
theorem hasSum_coeff_pow {J : PowerSeries ℂ} {q z : ℂ}
    (hJ : HasSum (fun m : ℕ => J.coeff m * q ^ m) z) (k : ℕ) :
    HasSum (fun m : ℕ => (J ^ k).coeff m * q ^ m) (z ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using hasSum_coeff_X_pow 0 q
  | succ k ih => simpa only [pow_succ] using hasSum_coeff_mul ih hJ

/-- A nonnegative shift of a convergent full series multiplies its sum by the
corresponding power, without any nonvanishing assumption on the argument. -/
theorem hasSum_coeff_X_pow_mul {J : PowerSeries ℂ} {q z : ℂ}
    (hJ : HasSum (fun m : ℕ => J.coeff m * q ^ m) z) (k : ℕ) :
    HasSum (fun m : ℕ => (X ^ k * J).coeff m * q ^ m) (q ^ k * z) :=
  hasSum_coeff_mul (hasSum_coeff_X_pow k q) hJ

/-- Constant multiplication commutes with a convergent full series. -/
theorem hasSum_coeff_C_mul {J : PowerSeries ℂ} {q z : ℂ}
    (hJ : HasSum (fun m : ℕ => J.coeff m * q ^ m) z) (c : ℂ) :
    HasSum (fun m : ℕ => (C c * J).coeff m * q ^ m) (c * z) := by
  simpa only [coeff_C_mul, mul_assoc] using hJ.mul_left c

/-- Finite sums of full convergent series sum to the finite sum of their values. -/
theorem hasSum_coeff_sum {ι : Type*} (t : Finset ι) (J : ι → PowerSeries ℂ)
    (q : ℂ) (z : ι → ℂ)
    (h : ∀ i ∈ t, HasSum (fun m : ℕ => (J i).coeff m * q ^ m) (z i)) :
    HasSum (fun m : ℕ => (∑ i ∈ t, J i).coeff m * q ^ m) (∑ i ∈ t, z i) := by
  classical
  revert h
  induction t using Finset.induction_on with
  | empty =>
    intro h
    simpa only [Finset.sum_empty, map_zero, zero_mul] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  | @insert i t hi ih =>
    intro h
    simpa only [Finset.sum_insert hi, map_add, add_mul] using
      (h i (Finset.mem_insert_self i t)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end PowerSeries

namespace Polynomial

/-- The full regularized series evaluates to `q^(w*n) P(z)`. The degree bound
makes every shift nonnegative, so the identity also holds when `q = 0`. -/
theorem hasSum_qRegularization (P : ℂ[X]) (J : PowerSeries ℂ) (w n : ℕ)
    (hP : P.natDegree ≤ n) (q z : ℂ)
    (hJ : HasSum (fun m : ℕ => J.coeff m * q ^ m) (q ^ w * z)) :
    HasSum (fun m : ℕ => (P.qRegularization J w n).coeff m * q ^ m)
      (q ^ (w * n) * P.eval z) := by
  have hsum := PowerSeries.hasSum_coeff_sum (Finset.range (n + 1))
    (fun i => PowerSeries.C (P.coeff i) *
      (PowerSeries.X ^ (w * (n - i)) * J ^ i)) q
    (fun i => P.coeff i * (q ^ (w * (n - i)) * (q ^ w * z) ^ i))
    (fun i _ => PowerSeries.hasSum_coeff_C_mul
      (PowerSeries.hasSum_coeff_X_pow_mul (PowerSeries.hasSum_coeff_pow hJ i)
        (w * (n - i))) (P.coeff i))
  have heval : (∑ i ∈ Finset.range (n + 1),
      P.coeff i * (q ^ (w * (n - i)) * (q ^ w * z) ^ i)) =
      q ^ (w * n) * P.eval z := by
    rw [P.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hP) z, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hexp : w * (n - i) + w * i = w * n := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hin]
    rw [mul_pow, ← pow_mul]
    calc
      P.coeff i * (q ^ (w * (n - i)) * (q ^ (w * i) * z ^ i)) =
          q ^ (w * (n - i) + w * i) * (P.coeff i * z ^ i) := by
            rw [pow_add]
            ring
      _ = q ^ (w * n) * (P.coeff i * z ^ i) := by rw [hexp]
  rw [heval] at hsum
  exact hsum

end Polynomial

namespace BakerHeegnerStark

/-- The ordinary `q` parameter is the `N`-th power of the width-`N` parameter. -/
theorem qParam_one_eq_commonWidth_pow {N : ℕ} (hN : 0 < N) (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 (τ : ℂ) =
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ N := by
  have ht : ((N, 0, 1) : ℕ × ℕ × ℕ) ∈ cyclicSublatticeTriples N := by
    apply (mem_cyclicSublatticeTriples hN).mpr
    simp
  simpa only [Nat.cast_one] using qParam_cyclicSublattice_commonWidth hN ht τ

end BakerHeegnerStark

namespace ModularForm

/-- The actual integral numerator of `j` has a full convergent expansion in the
common width-`N` parameter, including the zero coefficients inserted by `expand`. -/
theorem hasSum_jInvariantIntegralNumerator_commonWidth {N : ℕ} (hN : 0 < N)
    (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ =>
      (PowerSeries.expand N (Nat.ne_of_gt hN)
        (PowerSeries.map (Int.castRingHom ℂ) jInvariantIntegralNumerator)).coeff m *
        Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ m)
      (Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ N * jInvariant τ) := by
  apply BakerHeegnerStark.hasSum_powerSeries_expand
  have h := hasSum_jInvariantIntegralNumerator τ
  rw [BakerHeegnerStark.qParam_one_eq_commonWidth_pow hN τ] at h
  simpa only [PowerSeries.coeff_map, Int.coe_castRingHom, ← pow_mul] using h

end ModularForm
