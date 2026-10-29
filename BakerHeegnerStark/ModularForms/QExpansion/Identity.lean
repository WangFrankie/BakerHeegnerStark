/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Uniqueness and meromorphic regularization of q-expansions

Two power series that converge to the same function on the upper half plane have
identical coefficients. No regularity hypothesis on the function is needed:
the public constant-term limit theorem applies to each shifted difference series.
The unbundled coefficient lemma also identifies convergent series with the
analytic q-expansion when the cusp function is analytic.
Multiplication by a finite power of the actual q-parameter identifies the
punctured cusp functions exactly. An analytic regularization therefore gives
meromorphy of the original cusp function, at every positive width.
-/

namespace PowerSeries

open Filter
open scoped Topology

/-- Everywhere convergent q-expansions determine their power series uniquely. -/
theorem eq_of_hasSum_qParam {h : ℝ} (hh : 0 < h) {A B : PowerSeries ℂ}
    {f : UpperHalfPlane → ℂ}
    (hA : ∀ τ : UpperHalfPlane,
      HasSum (fun n ↦ A.coeff n * Function.Periodic.qParam h (τ : ℂ) ^ n) (f τ))
    (hB : ∀ τ : UpperHalfPlane,
      HasSum (fun n ↦ B.coeff n * Function.Periodic.qParam h (τ : ℂ) ^ n) (f τ)) :
    A = B := by
  let c : ℕ → ℂ := fun n ↦ A.coeff n - B.coeff n
  have hc : ∀ τ : UpperHalfPlane,
      HasSum (fun n ↦ c n * Function.Periodic.qParam h (τ : ℂ) ^ n) 0 := by
    intro τ
    simpa only [c, sub_mul, sub_self] using (hA τ).sub (hB τ)
  have hc_zero (n : ℕ) : c n = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have htail : ∀ τ : UpperHalfPlane,
          HasSum (fun k ↦ c (k + n) * Function.Periodic.qParam h (τ : ℂ) ^ k) 0 := by
        intro τ
        have hsum : ∑ i ∈ Finset.range n,
            c i * Function.Periodic.qParam h (τ : ℂ) ^ i = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [ih i (Finset.mem_range.mp hi), zero_mul]
        have hshift := (hasSum_nat_add_iff' n).mpr (hc τ)
        rw [hsum, sub_zero] at hshift
        have hq : Function.Periodic.qParam h (τ : ℂ) ^ n ≠ 0 :=
          pow_ne_zero n (Function.Periodic.qParam_ne_zero _)
        have hcancel (k : ℕ) :
            (c (k + n) * Function.Periodic.qParam h (τ : ℂ) ^ (k + n)) *
                (Function.Periodic.qParam h (τ : ℂ) ^ n)⁻¹ =
              c (k + n) * Function.Periodic.qParam h (τ : ℂ) ^ k := by
          rw [pow_add, mul_assoc, mul_assoc, mul_inv_cancel₀ hq, mul_one]
        simpa only [hcancel, zero_mul] using
          hshift.mul_right (Function.Periodic.qParam h (τ : ℂ) ^ n)⁻¹
      have hlim := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion
        (f := fun _ ↦ (0 : ℂ)) (c := fun k ↦ c (k + n)) hh
        (by simpa only [smul_eq_mul] using htail)
      simpa only [Nat.zero_add] using tendsto_nhds_unique hlim tendsto_const_nhds
  ext n
  exact sub_eq_zero.mp (hc_zero n)

end PowerSeries

namespace UpperHalfPlane

open Filter
open scoped Topology

/-- Unbundled convergent series determine the actual q-coefficients at any positive width. -/
theorem qExpansion_coeff_unique_unbundled {h : ℝ} (hh : 0 < h)
    (f : UpperHalfPlane → ℂ) (c : ℕ → ℂ)
    (ha : AnalyticAt ℂ (cuspFunction h f) 0)
    (hs : ∀ τ : UpperHalfPlane, HasSum
      (fun n => c n * Function.Periodic.qParam h (τ : ℂ) ^ n) (f τ)) (m : ℕ) :
    c m = (qExpansion h f).coeff m := by
  let : FunLike (UpperHalfPlane → ℂ) UpperHalfPlane ℂ := ⟨id, Function.injective_id⟩
  exact UpperHalfPlane.qExpansion_coeff_unique (F := UpperHalfPlane → ℂ) (h := h)
    (c := c) f hh ha (fun τ => by
      change HasSum (fun n => c n * Function.Periodic.qParam h (τ : ℂ) ^ n) (f τ)
      exact hs τ) m

/-- A finite q-power regularization identifies the actual punctured cusp function. -/
theorem cuspFunction_regularization_eventuallyEq {h : ℝ} (hh : 0 < h)
    (f : UpperHalfPlane → ℂ) (k : ℕ) :
    cuspFunction h f =ᶠ[𝓝[≠] (0 : ℂ)] fun q => q⁻¹ ^ k *
      cuspFunction h (fun τ : UpperHalfPlane => Function.Periodic.qParam h (τ : ℂ) ^ k * f τ) q := by
  let A : UpperHalfPlane → ℂ :=
    fun τ => Function.Periodic.qParam h (τ : ℂ) ^ k * f τ
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one),
    self_mem_nhdsWithin] with q hqnorm hq
  have hq0 : q ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hq
  have hnorm : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hqnorm
  have him := Function.Periodic.im_invQParam_pos_of_norm_lt_one hh hnorm hq0
  have hQ : Function.Periodic.qParam h
      (UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℂ) = q := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    exact Function.Periodic.qParam_right_inv hh.ne' hq0
  change Function.Periodic.cuspFunction h (f ∘ UpperHalfPlane.ofComplex) q =
    q⁻¹ ^ k * Function.Periodic.cuspFunction h (A ∘ UpperHalfPlane.ofComplex) q
  rw [Function.Periodic.cuspFunction_eq_of_nonzero h (f ∘ UpperHalfPlane.ofComplex) hq0,
    Function.Periodic.cuspFunction_eq_of_nonzero h (A ∘ UpperHalfPlane.ofComplex) hq0]
  change f (UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q)) =
    q⁻¹ ^ k * (Function.Periodic.qParam h
      (UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℂ) ^ k *
        f (UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q)))
  rw [hQ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hq0, one_pow, one_mul]

/-- An analytic finite q-power regularization makes the actual cusp function meromorphic. -/
theorem meromorphicAt_cuspFunction_of_regularization {h : ℝ} (hh : 0 < h)
    (f : UpperHalfPlane → ℂ) (k : ℕ)
    (ha : AnalyticAt ℂ (cuspFunction h (fun τ : UpperHalfPlane =>
      Function.Periodic.qParam h (τ : ℂ) ^ k * f τ)) 0) :
    MeromorphicAt (cuspFunction h f) 0 := by
  have hmer : MeromorphicAt (fun q : ℂ => q⁻¹ ^ k *
      cuspFunction h (fun τ : UpperHalfPlane => Function.Periodic.qParam h (τ : ℂ) ^ k * f τ) q)
      0 := ((MeromorphicAt.id (0 : ℂ)).inv.pow k).mul ha.meromorphicAt
  exact hmer.congr (cuspFunction_regularization_eventuallyEq hh f k).symm

end UpperHalfPlane
