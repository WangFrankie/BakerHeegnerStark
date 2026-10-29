/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.PeriodLattice.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Homothety of Period Lattices

Nonzero complex homotheties preserve scalar multiplier rings. Equality of
homothetic period modules is characterized by an integral change of generators
of determinant `1` or `-1`; no classification of CM values is assumed.
-/

open scoped Pointwise

namespace BakerHeegnerStark

/-- Multiplication by a nonzero complex number does not change the scalar
multipliers of an integer submodule of the complex plane. -/
theorem mul_preserves_smul_iff (L : Submodule ℤ ℂ) (c α : ℂ) (hc : c ≠ 0) :
    (∀ z ∈ c • L, α * z ∈ c • L) ↔ ∀ z ∈ L, α * z ∈ L := by
  constructor
  · intro h z hz
    have hcz : c * z ∈ c • L :=
      Submodule.smul_mem_pointwise_smul z c L hz
    obtain ⟨w, hw, heq⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (h _ hcz)
    have hwz : w = α * z := mul_left_cancel₀ hc (by
      simpa only [smul_eq_mul, mul_left_comm α c z] using heq)
    rwa [← hwz]
  · intro h z hz
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
    apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    exact ⟨α * w, h w hw, by simp only [smul_eq_mul]; ring⟩

/-- A complex homothety identifies two period modules exactly when its images
of the generators form an integral basis. Only the target period needs to be
nonreal in this algebraic criterion. -/
theorem smul_periodModule_eq_iff (τ σ α : ℂ) (hσ : σ.im ≠ 0) :
    α • periodModule τ = periodModule σ ↔
      ∃ a b c d : ℤ, (a * d - b * c = 1 ∨ a * d - b * c = -1) ∧
        α = (a : ℂ) + (b : ℂ) * σ ∧ α * τ = (c : ℂ) + (d : ℂ) * σ := by
  have h1τ : (1 : ℂ) ∈ periodModule τ := Submodule.subset_span (by simp)
  have hττ : τ ∈ periodModule τ := Submodule.subset_span (by simp)
  have h1σ : (1 : ℂ) ∈ periodModule σ := Submodule.subset_span (by simp)
  have hσσ : σ ∈ periodModule σ := Submodule.subset_span (by simp)
  constructor
  · intro heq
    have hα : α ∈ periodModule σ := by
      rw [← heq]
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨1, h1τ, by simp⟩
    have hατ : α * τ ∈ periodModule σ := by
      rw [← heq]
      exact Submodule.smul_mem_pointwise_smul τ α _ hττ
    obtain ⟨a, b, ha⟩ := (mem_periodModule_iff σ α).mp hα
    obtain ⟨c, d, hc⟩ := (mem_periodModule_iff σ (α * τ)).mp hατ
    rw [← heq] at h1σ hσσ
    obtain ⟨z, hz, hz1⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1σ
    obtain ⟨e, f, rfl⟩ := (mem_periodModule_iff τ z).mp hz
    obtain ⟨w, hw, hwσ⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hσσ
    obtain ⟨g, h, rfl⟩ := (mem_periodModule_iff τ w).mp hw
    have hco1 : e * a + f * c = 1 ∧ e * b + f * d = 0 :=
      periodModule_coordinates_eq σ hσ (a := e * a + f * c) (b := e * b + f * d)
        (c := 1) (d := 0) (by
          push_cast
          change α * ((e : ℂ) + (f : ℂ) * τ) = 1 at hz1
          linear_combination -(e : ℂ) * ha - (f : ℂ) * hc + hz1)
    have hcoσ : g * a + h * c = 0 ∧ g * b + h * d = 1 :=
      periodModule_coordinates_eq σ hσ (a := g * a + h * c) (b := g * b + h * d)
        (c := 0) (d := 1) (by
          push_cast
          change α * ((g : ℂ) + (h : ℂ) * τ) = σ at hwσ
          linear_combination -(g : ℂ) * ha - (h : ℂ) * hc + hwσ)
    have hdet : (a * d - b * c) * (e * h - f * g) = 1 := by
      calc
        _ = (e * a + f * c) * (g * b + h * d) -
            (g * a + h * c) * (e * b + f * d) := by ring
        _ = 1 := by rw [hco1.1, hco1.2, hcoσ.1, hcoσ.2]; norm_num
    exact ⟨a, b, c, d, Int.eq_one_or_neg_one_of_mul_eq_one hdet, ha, hc⟩
  · rintro ⟨a, b, c, d, hdet, ha, hc⟩
    let δ : ℤ := a * d - b * c
    have hδ : (δ : ℂ) ^ 2 = 1 := by
      rcases hdet with hd | hd <;> simp [δ, hd]
    have hprod1 : α * ((d : ℂ) - (b : ℂ) * τ) = (δ : ℂ) := by
      dsimp [δ]
      push_cast
      linear_combination (d : ℂ) * ha - (b : ℂ) * hc
    have hprodσ : α * (-(c : ℂ) + (a : ℂ) * τ) = (δ : ℂ) * σ := by
      dsimp [δ]
      push_cast
      linear_combination -(c : ℂ) * ha + (a : ℂ) * hc
    have h1 : (1 : ℂ) ∈ α • periodModule τ := by
      apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      refine ⟨(δ * d : ℤ) + (-(δ * b) : ℤ) * τ, ?_, ?_⟩
      · exact (mem_periodModule_iff τ _).mpr ⟨δ * d, -(δ * b), rfl⟩
      · change α * ((δ * d : ℤ) + (-(δ * b) : ℤ) * τ) = 1
        push_cast
        calc
          _ = (δ : ℂ) * (α * ((d : ℂ) - (b : ℂ) * τ)) := by ring
          _ = 1 := by rw [hprod1, ← pow_two, hδ]
    have hσ' : σ ∈ α • periodModule τ := by
      apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      refine ⟨(-(δ * c) : ℤ) + (δ * a : ℤ) * τ, ?_, ?_⟩
      · exact (mem_periodModule_iff τ _).mpr ⟨-(δ * c), δ * a, rfl⟩
      · change α * ((-(δ * c) : ℤ) + (δ * a : ℤ) * τ) = σ
        push_cast
        calc
          _ = (δ : ℂ) * (α * (-(c : ℂ) + (a : ℂ) * τ)) := by ring
          _ = σ := by rw [hprodσ, ← mul_assoc, ← pow_two, hδ, one_mul]
    apply le_antisymm
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
      obtain ⟨m, n, rfl⟩ := (mem_periodModule_iff τ w).mp hw
      apply (mem_periodModule_iff σ _).mpr
      refine ⟨m * a + n * c, m * b + n * d, ?_⟩
      change α * ((m : ℂ) + (n : ℂ) * τ) = _
      push_cast
      linear_combination (m : ℂ) * ha + (n : ℂ) * hc
    · apply Submodule.span_le.mpr
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact h1
      · exact hσ'

/-- Upper-half-plane period bases have the same orientation, so a complex
homothety between them has determinant one rather than minus one. -/
theorem smul_periodModule_eq_iff_of_im_pos (τ σ α : ℂ) (hτ : 0 < τ.im)
    (hσ : 0 < σ.im) :
    α • periodModule τ = periodModule σ ↔
      ∃ a b c d : ℤ, a * d - b * c = 1 ∧
        α = (a : ℂ) + (b : ℂ) * σ ∧ α * τ = (c : ℂ) + (d : ℂ) * σ := by
  rw [smul_periodModule_eq_iff τ σ α (ne_of_gt hσ)]
  constructor
  · rintro ⟨a, b, c, d, hdet, ha, hc⟩
    refine ⟨a, b, c, d, ?_, ha, hc⟩
    rcases hdet with hd | hd
    · exact hd
    · have harea : Complex.normSq α * τ.im = ((a * d - b * c : ℤ) : ℝ) * σ.im := by
        calc
          _ = (star α * (α * τ)).im := by
            rw [← mul_assoc, mul_comm (star α) α, Complex.star_def, Complex.mul_conj]
            simp
          _ = (star ((a : ℂ) + (b : ℂ) * σ) * ((c : ℂ) + (d : ℂ) * σ)).im := by
            rw [hc, ha]
          _ = _ := by
            simp [Complex.mul_im, Complex.mul_re]
            ring
      have hnonneg := mul_nonneg (Complex.normSq_nonneg α) hτ.le
      rw [hd] at harea
      norm_num at harea
      linarith
  · rintro ⟨a, b, c, d, hd, ha, hc⟩
    exact ⟨a, b, c, d, Or.inl hd, ha, hc⟩

end BakerHeegnerStark
