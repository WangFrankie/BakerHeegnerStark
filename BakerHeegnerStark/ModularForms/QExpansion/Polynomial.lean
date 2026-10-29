/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Eval.Subring

/-!
# Coefficient Descent from Regularized q-Expansions

If `j = q⁻ʷ J` with `J(0)=1`, then `q^(wn) P(j)` is a finite sum of
nonnegative shifts of powers of `J`. Its coefficients recover the coefficients
of `P` by a unit triangular system. This is the algebraic q-expansion descent
used after the analytic modular polynomial has been constructed.
-/

noncomputable section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The regularization `q^(wn) P(q⁻ʷ J)`, when `P` has degree at most `n`. -/
def qRegularization (P : R[X]) (J : PowerSeries R) (w n : ℕ) : PowerSeries R :=
  ∑ i ∈ Finset.range (n + 1), PowerSeries.C (P.coeff i) *
    (PowerSeries.X ^ (w * (n - i)) * J ^ i)

/-- The shifted coefficient formula is triangular in the polynomial coefficients. -/
theorem qRegularization_coeff (P : R[X]) (J : PowerSeries R) (w n : ℕ)
    (hw : 0 < w) {i : ℕ} (hi : i ≤ n) :
    (P.qRegularization J w n).coeff (w * (n - i)) =
      ∑ j ∈ Finset.range (n + 1), if i ≤ j then
        P.coeff j * (J ^ j).coeff (w * (j - i)) else 0 := by
  classical
  simp only [qRegularization, map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by
    have := Finset.mem_range.mp hj
    omega
  by_cases hij : i ≤ j
  · have hle : w * (n - j) ≤ w * (n - i) := Nat.mul_le_mul_left w (by omega)
    have hsum : w * (n - i) = w * (n - j) + w * (j - i) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have hdiff : w * (n - i) - w * (n - j) = w * (j - i) := by omega
    rw [ite_eq_left hle, ite_eq_left hij, hdiff]
  · have hbase : n - i < n - j := by omega
    have hshift : w * (n - i) < w * (n - j) := Nat.mul_lt_mul_of_pos_left hbase hw
    rw [ite_eq_right (not_le_of_gt hshift), ite_eq_right hij, mul_zero]

/-- An integral-width regularized expansion over a subring recovers every
polynomial coefficient over that subring. Only `J(0)=1` is needed. -/
theorem coeff_mem_of_qRegularization (P : R[X]) (S : Subring R) (J : PowerSeries S)
    (hJ : J.constantCoeff = 1) (w n : ℕ) (hw : 0 < w) (hP : P.natDegree ≤ n)
    (hreg : ∀ k, (P.qRegularization (PowerSeries.map S.subtype J) w n).coeff k ∈ S) :
    ∀ k, P.coeff k ∈ S := by
  classical
  have hJ0 : (PowerSeries.map S.subtype J).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hJ, map_one]
  have hcoeff : ∀ r : ℕ, ∀ i, i ≤ n → n - i = r → P.coeff i ∈ S := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro i hi hri
      let term (j : ℕ) : R := if i ≤ j then P.coeff j *
        ((PowerSeries.map S.subtype J) ^ j).coeff (w * (j - i)) else 0
      have hterm : term i = P.coeff i := by
        simp only [term, ite_eq_left (le_refl i), Nat.sub_self, mul_zero]
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hJ0, one_pow, mul_one]
      have herase : (∑ j ∈ (Finset.range (n + 1)).erase i, term j) ∈ S := by
        apply S.sum_mem
        intro j hj
        have hjne := (Finset.mem_erase.mp hj).1
        have hjn : j ≤ n := by
          have := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
          omega
        by_cases hij : i ≤ j
        · have hci : P.coeff j ∈ S := ih (n - j) (by omega) j hjn rfl
          have hcJ : ((PowerSeries.map S.subtype J) ^ j).coeff (w * (j - i)) ∈ S := by
            rw [← map_pow, PowerSeries.coeff_map]
            exact ((J ^ j).coeff (w * (j - i))).2
          simp only [term, ite_eq_left hij]
          exact S.mul_mem hci hcJ
        · simp only [term, ite_eq_right hij]
          exact S.zero_mem
      have hsum : (∑ j ∈ (Finset.range (n + 1)).erase i, term j) + P.coeff i =
          (P.qRegularization (PowerSeries.map S.subtype J) w n).coeff (w * (n - i)) := by
        calc
          _ = (∑ j ∈ (Finset.range (n + 1)).erase i, term j) + term i := by rw [hterm]
          _ = ∑ j ∈ Finset.range (n + 1), term j :=
            Finset.sum_erase_add _ _ (Finset.mem_range.mpr (by omega))
          _ = _ := (qRegularization_coeff P (PowerSeries.map S.subtype J) w n hw hi).symm
      have hsub := S.sub_mem (hreg (w * (n - i))) herase
      rw [← hsum, add_sub_cancel_left] at hsub
      exact hsub
  intro k
  by_cases hk : k ≤ n
  · exact hcoeff (n - k) k hk rfl
  · rw [P.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact S.zero_mem

/-- The recovered coefficients construct a polynomial over the subring,
not merely a list of coefficient-membership statements. -/
theorem exists_map_of_qRegularization (P : R[X]) (S : Subring R) (J : PowerSeries S)
    (hJ : J.constantCoeff = 1) (w n : ℕ) (hw : 0 < w) (hP : P.natDegree ≤ n)
    (hreg : ∀ k, (P.qRegularization (PowerSeries.map S.subtype J) w n).coeff k ∈ S) :
    ∃ Q : S[X], Q.map S.subtype = P := by
  have hc := coeff_mem_of_qRegularization P S J hJ w n hw hP hreg
  apply (Polynomial.mem_map_range S.subtype).mpr
  intro k
  exact ⟨⟨P.coeff k, hc k⟩, rfl⟩

/-- Regularized polynomial series commute with coefficient ring homomorphisms. -/
theorem qRegularization_map {T : Type*} [CommRing T] (P : R[X]) (J : PowerSeries R)
    (w n : ℕ) (f : R →+* T) :
    (P.map f).qRegularization (PowerSeries.map f J) w n =
      PowerSeries.map f (P.qRegularization J w n) := by
  classical
  simp only [qRegularization, map_sum, Polynomial.coeff_map, map_mul, map_pow,
    PowerSeries.map_C, PowerSeries.map_X]

/-- A regularized series in the image of a coefficient homomorphism descends
the actual polynomial along the same homomorphism. -/
theorem exists_map_of_qRegularization_eq_map {T : Type*} [CommRing T]
    (f : T →+* R) (P : R[X]) (J : PowerSeries T) (hJ : J.constantCoeff = 1)
    (w n : ℕ) (hw : 0 < w) (hP : P.natDegree ≤ n) (A : PowerSeries T)
    (hreg : P.qRegularization (PowerSeries.map f J) w n = PowerSeries.map f A) :
    ∃ Q : T[X], Q.map f = P := by
  let S : Subring R := f.range
  let JS : PowerSeries S := PowerSeries.map f.rangeRestrict J
  have hmap : PowerSeries.map S.subtype JS = PowerSeries.map f J := rfl
  have hJS : JS.constantCoeff = 1 := by
    change (PowerSeries.map f.rangeRestrict J).constantCoeff = 1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hJ, map_one]
  have hmem : ∀ k, (P.qRegularization (PowerSeries.map S.subtype JS) w n).coeff k ∈ S := by
    intro k
    rw [hmap, hreg, PowerSeries.coeff_map]
    exact ⟨A.coeff k, rfl⟩
  exact (Polynomial.mem_map_range f).mpr
    (coeff_mem_of_qRegularization P S JS hJS w n hw hP hmem)

/-- Fixing the unit numerator and the full regularized series forces a
coefficient endomorphism to fix the polynomial itself. -/
theorem map_eq_of_qRegularization_fixed (P : R[X]) (J : PowerSeries R)
    (hJ : J.constantCoeff = 1) (w n : ℕ) (hw : 0 < w) (hP : P.natDegree ≤ n)
    (σ : R →+* R) (hσJ : PowerSeries.map σ J = J)
    (hσreg : PowerSeries.map σ (P.qRegularization J w n) = P.qRegularization J w n) :
    P.map σ = P := by
  let S : Subring R := σ.eqLocus (RingHom.id R)
  have hJmem (k : ℕ) : J.coeff k ∈ S := by
    change σ (J.coeff k) = J.coeff k
    simpa only [PowerSeries.coeff_map] using congrArg (PowerSeries.coeff k) hσJ
  let JS : PowerSeries S := PowerSeries.mk fun k => ⟨J.coeff k, hJmem k⟩
  have hmap : PowerSeries.map S.subtype JS = J := by
    ext k
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  have hJS : JS.constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [JS, PowerSeries.coeff_mk]
    apply Subtype.ext
    exact (PowerSeries.coeff_zero_eq_constantCoeff_apply J).trans hJ
  have hmem : ∀ k, (P.qRegularization (PowerSeries.map S.subtype JS) w n).coeff k ∈ S := by
    intro k
    rw [hmap]
    change σ ((P.qRegularization J w n).coeff k) = (P.qRegularization J w n).coeff k
    simpa only [PowerSeries.coeff_map] using congrArg (PowerSeries.coeff k) hσreg
  have hc := coeff_mem_of_qRegularization P S JS hJS w n hw hP hmem
  ext k
  rw [Polynomial.coeff_map]
  exact hc k

end Polynomial
