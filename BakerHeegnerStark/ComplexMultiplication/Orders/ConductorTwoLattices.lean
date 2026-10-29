/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.PeriodLattice.Homothety
import BakerHeegnerStark.ComplexMultiplication.Orders.HalfIntegral

/-!
# Intermediate Lattices at Conductor Two

Between twice a two-generator integer module and the module itself there
are at most five submodules. For independent periods, the three intermediate
possibilities are the index-two lattices in the level-two modular equation.
This enumeration alone does not normalize arbitrary invertible order ideals
into that interval.
-/

namespace BakerHeegnerStark

open scoped Pointwise

/-- Enumerate submodules between a two-generator integer module and its double.
No linear independence is needed; some of the displayed modules may coincide. -/
theorem span_pair_conductor_two_cases (a b : ℂ) (L : Submodule ℤ ℂ)
    (hlo : Submodule.span ℤ ({2 * a, 2 * b} : Set ℂ) ≤ L)
    (hhi : L ≤ Submodule.span ℤ ({a, b} : Set ℂ)) :
    L = Submodule.span ℤ ({2 * a, 2 * b} : Set ℂ) ∨
      L = Submodule.span ℤ ({a, 2 * b} : Set ℂ) ∨
      L = Submodule.span ℤ ({2 * a, b} : Set ℂ) ∨
      L = Submodule.span ℤ ({2 * a, a + b} : Set ℂ) ∨
      L = Submodule.span ℤ ({a, b} : Set ℂ) := by
  classical
  have hspan (N : Submodule ℤ ℂ) (x y : ℂ) (hx : x ∈ N) (hy : y ∈ N) :
      Submodule.span ℤ ({x, y} : Set ℂ) ≤ N := by
    apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  have htwo (N : Submodule ℤ ℂ) (x : ℂ) (hx : x ∈ N) : 2 * x ∈ N := by
    simpa only [zsmul_eq_mul, Int.cast_ofNat] using N.smul_mem (2 : ℤ) hx
  have h2a : 2 * a ∈ L := hlo (Submodule.subset_span (by simp))
  have h2b : 2 * b ∈ L := hlo (Submodule.subset_span (by simp))
  have hbound (N : Submodule ℤ ℂ) (h2aN : 2 * a ∈ N) (h2bN : 2 * b ∈ N)
      (haN : a ∈ L → a ∈ N) (hbN : b ∈ L → b ∈ N)
      (hsN : a + b ∈ L → a + b ∈ N) : L ≤ N := by
    intro z hz
    obtain ⟨m, n, heq⟩ : ∃ m n : ℤ, z = (m : ℂ) * a + (n : ℂ) * b := by
      simpa only [Submodule.mem_span_pair, zsmul_eq_mul, eq_comm] using hhi hz
    subst z
    let q : ℂ := ((m / 2 : ℤ) : ℂ) * (2 * a) + ((n / 2 : ℤ) : ℂ) * (2 * b)
    have hqL : q ∈ L := by
      simpa only [q, zsmul_eq_mul] using
        L.add_mem (L.smul_mem (m / 2) h2a) (L.smul_mem (n / 2) h2b)
    have hqN : q ∈ N := by
      simpa only [q, zsmul_eq_mul] using
        N.add_mem (N.smul_mem (m / 2) h2aN) (N.smul_mem (n / 2) h2bN)
    have hm : (m : ℂ) = ((m % 2 : ℤ) : ℂ) + ((m / 2 : ℤ) : ℂ) * 2 := by
      exact_mod_cast (show m = m % 2 + (m / 2) * 2 by omega)
    have hn : (n : ℂ) = ((n % 2 : ℤ) : ℂ) + ((n / 2 : ℤ) : ℂ) * 2 := by
      exact_mod_cast (show n = n % 2 + (n / 2) * 2 by omega)
    have heq : (m : ℂ) * a + (n : ℂ) * b =
        ((m % 2 : ℤ) : ℂ) * a + ((n % 2 : ℤ) : ℂ) * b + q := by
      dsimp only [q]
      linear_combination a * hm + b * hn
    have hrL : ((m % 2 : ℤ) : ℂ) * a + ((n % 2 : ℤ) : ℂ) * b ∈ L := by
      have h := L.sub_mem hz hqL
      rw [heq] at h
      simpa using h
    have hrN : ((m % 2 : ℤ) : ℂ) * a + ((n % 2 : ℤ) : ℂ) * b ∈ N := by
      have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
      have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hm with hm | hm <;> rcases hn with hn | hn <;>
        simp only [hm, hn, Int.cast_zero, Int.cast_one, zero_mul, one_mul,
          zero_add, add_zero] at hrL ⊢
      · exact N.zero_mem
      · exact hbN hrL
      · exact haN hrL
      · exact hsN hrL
    rw [heq]
    exact N.add_mem hrN hqN
  by_cases ha : a ∈ L
  · by_cases hb : b ∈ L
    · right; right; right; right
      exact le_antisymm hhi (hspan L a b ha hb)
    · right; left
      let N := Submodule.span ℤ ({a, 2 * b} : Set ℂ)
      have haN : a ∈ N := Submodule.subset_span (by simp)
      have h2bN : 2 * b ∈ N := Submodule.subset_span (by simp)
      refine le_antisymm (hbound N (htwo N a haN) h2bN (fun _ => haN)
        (fun h => False.elim (hb h)) ?_) (hspan L a (2 * b) ha h2b)
      intro hs
      apply False.elim
      apply hb
      convert L.sub_mem hs ha using 1; ring
  · by_cases hb : b ∈ L
    · right; right; left
      let N := Submodule.span ℤ ({2 * a, b} : Set ℂ)
      have h2aN : 2 * a ∈ N := Submodule.subset_span (by simp)
      have hbN : b ∈ N := Submodule.subset_span (by simp)
      refine le_antisymm (hbound N h2aN (htwo N b hbN)
        (fun h => False.elim (ha h)) (fun _ => hbN) ?_)
        (hspan L (2 * a) b h2a hb)
      intro hs
      apply False.elim
      apply ha
      convert L.sub_mem hs hb using 1; ring
    · by_cases hs : a + b ∈ L
      · right; right; right; left
        let N := Submodule.span ℤ ({2 * a, a + b} : Set ℂ)
        have h2aN : 2 * a ∈ N := Submodule.subset_span (by simp)
        have hsN : a + b ∈ N := Submodule.subset_span (by simp)
        have h2bN : 2 * b ∈ N := by
          convert N.sub_mem (htwo N (a + b) hsN) h2aN using 1; ring
        exact le_antisymm (hbound N h2aN h2bN
          (fun h => False.elim (ha h)) (fun h => False.elim (hb h)) (fun _ => hsN))
          (hspan L (2 * a) (a + b) h2a hs)
      · left
        exact le_antisymm (hbound _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp)) (fun h => False.elim (ha h))
          (fun h => False.elim (hb h)) (fun h => False.elim (hs h))) hlo

/-- The five possible modules in the conductor-two interval, in period form.
For nonreal periods the three middle terms are index-two sublattices, with
the half-period modules scaled by two. -/
theorem periodModule_conductor_two_cases (τ : ℂ) (L : Submodule ℤ ℂ)
    (hlo : (2 : ℂ) • periodModule τ ≤ L) (hhi : L ≤ periodModule τ) :
    L = (2 : ℂ) • periodModule τ ∨ L = periodModule (2 * τ) ∨
      L = (2 : ℂ) • periodModule (τ / 2) ∨
      L = (2 : ℂ) • periodModule ((τ + 1) / 2) ∨ L = periodModule τ := by
  have hsmul (c σ : ℂ) : c • periodModule σ =
      Submodule.span ℤ ({c, c * σ} : Set ℂ) := by
    simp [periodModule, Submodule.smul_span, Set.smul_set_insert,
      Set.smul_set_singleton, smul_eq_mul]
  have hd : (2 : ℂ) • periodModule τ = Submodule.span ℤ ({2, 2 * τ} : Set ℂ) :=
    hsmul 2 τ
  have hh : (2 : ℂ) • periodModule (τ / 2) = Submodule.span ℤ ({2, τ} : Set ℂ) := by
    rw [hsmul, show (2 : ℂ) * (τ / 2) = τ by ring]
  have hs : (2 : ℂ) • periodModule ((τ + 1) / 2) =
      Submodule.span ℤ ({2, 1 + τ} : Set ℂ) := by
    rw [hsmul, show (2 : ℂ) * ((τ + 1) / 2) = 1 + τ by ring]
  have hlo' : Submodule.span ℤ ({2 * (1 : ℂ), 2 * τ} : Set ℂ) ≤ L := by
    simpa only [mul_one, ← hd] using hlo
  rw [hd, hh, hs]
  simpa only [mul_one, periodModule] using
    span_pair_conductor_two_cases 1 τ L hlo' hhi

/-- If the larger quadratic period does not multiply the module into itself,
the two endpoints of the conductor-two interval are impossible. -/
theorem periodModule_conductor_two_middle_cases (τ : ℂ) (u v : ℤ)
    (hτ : τ ^ 2 = (u : ℂ) + (v : ℂ) * τ) (L : Submodule ℤ ℂ)
    (hlo : (2 : ℂ) • periodModule τ ≤ L) (hhi : L ≤ periodModule τ)
    (hnot : ¬ ∀ z ∈ L, τ * z ∈ L) :
    L = periodModule (2 * τ) ∨ L = (2 : ℂ) • periodModule (τ / 2) ∨
      L = (2 : ℂ) • periodModule ((τ + 1) / 2) := by
  have hm : ∀ z ∈ periodModule τ, τ * z ∈ periodModule τ :=
    (mul_preserves_periodModule_iff τ τ u v hτ).mpr
      (Submodule.subset_span (by simp))
  rcases periodModule_conductor_two_cases τ L hlo hhi with h | h | h | h | h
  · apply False.elim
    apply hnot
    rw [h]
    exact (mul_preserves_smul_iff (periodModule τ) 2 τ (by norm_num)).mpr hm
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · apply False.elim
    apply hnot
    rw [h]
    exact hm

/-- A proper square-root-order module already normalized into the actual
conductor-two interval is one of the three displayed lattices. Normalizing
an arbitrary invertible ideal into this interval is a separate arithmetic step. -/
theorem sqrtOrder_conductor_two_periodModule_cases (p : ℕ) (k : ℤ)
    (hk : -(p : ℤ) = 1 + 4 * k) (L : Submodule ℤ ℂ)
    (hlo : (2 : ℂ) • periodModule ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2) ≤ L)
    (hhi : L ≤ periodModule ((1 + (Real.sqrt (p : ℝ) : ℂ) * Complex.I) / 2))
    (hproper : ∀ α : ℂ, (∀ z ∈ L, α * z ∈ L) ↔
      α ∈ (sqrtOrderEmbedding p).toRingHom.range) :
    let s := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
    L = periodModule s ∨ L = (2 : ℂ) • periodModule ((1 + s) / 4) ∨
      L = (2 : ℂ) • periodModule ((3 + s) / 4) := by
  dsimp only
  let s : ℂ := (Real.sqrt (p : ℝ) : ℂ) * Complex.I
  let w : ℂ := (1 + s) / 2
  have hnot : ¬ ∀ z ∈ L, w * z ∈ L := by
    intro h
    exact halfPeriod_not_mem_sqrtOrderEmbedding_range p k hk ((hproper w).mp h)
  have hquad : w ^ 2 = (k : ℂ) + ((1 : ℤ) : ℂ) * w := by
    simpa only [Int.cast_one, one_mul, w, s] using halfPeriod_quadratic p k hk
  have hcases := periodModule_conductor_two_middle_cases w k 1 hquad L hlo hhi hnot
  have hd : periodModule (2 * w) = periodModule s := by
    rw [show 2 * w = (1 : ℂ) + s by dsimp only [w]; ring]
    simpa only [Int.cast_one] using periodModule_add_int s 1
  have hh : w / 2 = (1 + s) / 4 := by dsimp only [w]; ring
  have hs : (w + 1) / 2 = (3 + s) / 4 := by dsimp only [w]; ring
  simpa only [hd, hh, hs] using hcases

end BakerHeegnerStark
