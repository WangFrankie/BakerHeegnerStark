/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Uniformization.Torsion

/-!
# Division lattices and the actual quadratic-period kernel

Dividing the second period by a positive integer gives an overlattice with
exactly that many explicitly specified cosets. For `τ² = -m`, this is the
inverse image of the original lattice under multiplication by `τ`.
Consequently the actual period-curve CM point-group kernel consists precisely
of the points represented by `kτ/m`, and has cardinality `m`.

These are lattice and actual point-group statements, not an assumption about
the degree or field of definition of an algebraic curve morphism.
-/

namespace BakerHeegnerStark

/-- Divide the second positive imaginary period by a positive integer. -/
noncomputable def dividedPeriod (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) : UpperHalfPlane :=
  ⟨(τ : ℂ) / (N : ℂ), by
    simpa using div_pos τ.im_pos (show (0 : ℝ) < N by exact_mod_cast hN)⟩

/-- The divided period retains its specified complex coordinate. -/
@[simp] theorem coe_dividedPeriod (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) :
    (dividedPeriod τ N hN : ℂ) = (τ : ℂ) / (N : ℂ) := rfl

/-- The specified representatives `kτ/N`, for `0 ≤ k < N`. -/
noncomputable def divisionPeriodRepresentatives (τ : ℂ) (N : ℕ) : Finset ℂ := by
  classical
  exact (Finset.range N).image (fun k : ℕ => (k : ℂ) * τ / (N : ℂ))

/-- The original lattice is contained in the divided-period lattice. -/
theorem periodModule_le_divided (τ : ℂ) (N : ℕ) (hN : 0 < N) :
    periodModule τ ≤ periodModule (τ / (N : ℂ)) := by
  intro z hz
  obtain ⟨a, b, rfl⟩ := (mem_periodModule_iff _ _).mp hz
  apply (mem_periodModule_iff _ _).mpr
  refine ⟨a, b * N, ?_⟩
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hN)]

/-- Every specified representative belongs to the actual finer lattice. -/
theorem divisionPeriodRepresentatives_mem (τ : ℂ) (N : ℕ) {t : ℂ}
    (ht : t ∈ divisionPeriodRepresentatives τ N) : t ∈ periodModule (τ / (N : ℂ)) := by
  classical
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
  exact (mem_periodModule_iff _ _).mpr ⟨0, k, by push_cast; ring⟩

/-- The specified representatives cover every actual finer-lattice coset. -/
theorem divisionPeriodRepresentatives_cover (τ : ℂ) (N : ℕ) (hN : 0 < N)
    {z : ℂ} (hz : z ∈ periodModule (τ / (N : ℂ))) :
    ∃ t ∈ divisionPeriodRepresentatives τ N, z - t ∈ periodModule τ := by
  classical
  let : NeZero N := ⟨ne_of_gt hN⟩
  obtain ⟨a, b, rfl⟩ := (mem_periodModule_iff _ _).mp hz
  let k : ℕ := (b : ZMod N).val
  have hk : k < N := ZMod.val_lt _
  have hdiv : (N : ℤ) ∣ b - (k : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [k]
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨(k : ℂ) * τ / (N : ℂ), Finset.mem_image.mpr
    ⟨k, Finset.mem_range.mpr hk, rfl⟩, (mem_periodModule_iff _ _).mpr ⟨a, q, ?_⟩⟩
  have hbc : (b : ℂ) - (k : ℂ) = (N : ℂ) * (q : ℂ) := by exact_mod_cast hq
  field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hN)]
  linear_combination τ * hbc


/-- Distinct specified residue indices remain distinct modulo the original lattice. -/
theorem divisionPeriodPoint_sub_mem_iff (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N)
    (k l : ℕ) (hk : k < N) (hl : l < N) :
    (k : ℂ) * (τ : ℂ) / (N : ℂ) - (l : ℂ) * (τ : ℂ) / (N : ℂ) ∈
      periodModule (τ : ℂ) ↔ k = l := by
  constructor
  · intro hst
    have hmem : ((0 : ℂ) + (((k : ℤ) - (l : ℤ) : ℤ) : ℂ) * (τ : ℂ)) / (N : ℂ) ∈
        periodModule (τ : ℂ) := by
      convert hst using 1; push_cast; ring
    have hzero : periodTorsionPoint (τ : ℂ) N hN 0 ((k : ℤ) - (l : ℤ)) = 0 := by
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero (periodModule (τ : ℂ))).mpr
        (by simpa only [Int.cast_zero] using hmem)
    have hmod : (k : ZMod N) = (l : ZMod N) := by
      have h := ((periodTorsionPoint_eq_zero_iff (τ : ℂ) (ne_of_gt τ.im_pos) N hN 0
        ((k : ℤ) - (l : ℤ))).mp hzero).2
      simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero] using h
    have h := congrArg ZMod.val hmod
    simpa only [ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hl] using h
  · rintro rfl
    simp

/-- The explicit finite representative set has no repeated lattice cosets. -/
theorem divisionPeriodRepresentatives_separated (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N)
    {s t : ℂ} (hs : s ∈ divisionPeriodRepresentatives τ N)
    (ht : t ∈ divisionPeriodRepresentatives τ N)
    (hst : s - t ∈ periodModule (τ : ℂ)) : s = t := by
  classical
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ht
  rw [(divisionPeriodPoint_sub_mem_iff τ N hN k l (Finset.mem_range.mp hk)
    (Finset.mem_range.mp hl)).mp hst]


/-- There are exactly `N` distinct specified complex representatives. -/
theorem card_divisionPeriodRepresentatives (τ : UpperHalfPlane) (N : ℕ) (hN : 0 < N) :
    (divisionPeriodRepresentatives τ N).card = N := by
  classical
  have hinj : Set.InjOn (fun k : ℕ => (k : ℂ) * (τ : ℂ) / (N : ℂ))
      (Finset.range N) := by
    intro k hk l hl h
    apply (divisionPeriodPoint_sub_mem_iff τ N hN k l (Finset.mem_range.mp hk)
      (Finset.mem_range.mp hl)).mp
    dsimp only at h
    rw [h]
    simp
  simpa only [divisionPeriodRepresentatives, Finset.card_range] using
    Finset.card_image_of_injOn hinj

/-- For a quadratic period, the finer lattice is precisely the preimage under CM multiplication. -/
theorem mul_mem_periodModule_iff_mem_divided (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -(m : ℂ)) (z : ℂ) :
    (τ : ℂ) * z ∈ periodModule (τ : ℂ) ↔
      z ∈ periodModule ((τ : ℂ) / (m : ℂ)) := by
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  constructor
  · intro hz
    obtain ⟨a, b, hab⟩ := (mem_periodModule_iff _ _).mp hz
    apply (mem_periodModule_iff _ _).mpr
    refine ⟨b, -a, ?_⟩
    push_cast
    field_simp [hmC]
    linear_combination -(τ : ℂ) * hab + (z - (b : ℂ)) * hτ
  · intro hz
    obtain ⟨a, b, rfl⟩ := (mem_periodModule_iff _ _).mp hz
    apply (mem_periodModule_iff _ _).mpr
    refine ⟨-b, a, ?_⟩
    push_cast
    field_simp [hmC]
    linear_combination (b : ℂ) * hτ

/-- The actual CM point-group kernel consists exactly of the specified division points. -/
theorem periodCurveCMEnd_ker_iff [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -((m : ℤ) : ℂ))
    (P : (periodCurve (standardPeriodPair τ)).toAffine.Point) :
    periodCurveCMEnd τ m hτ P = 0 ↔
      ∃ k : Fin m, P = standardPeriodPoint τ ((k.val : ℂ) * (τ : ℂ) / (m : ℂ)) := by
  obtain ⟨z, rfl⟩ := standardPeriodPoint_surjective τ P
  rw [periodCurveCMEnd_standardPeriodPoint, standardPeriodPoint_eq_zero_iff,
    mul_mem_periodModule_iff_mem_divided τ m hm (by simpa only [Int.cast_natCast] using hτ)]
  constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := divisionPeriodRepresentatives_cover (τ : ℂ) m hm hz
    simp only [divisionPeriodRepresentatives, Finset.mem_image, Finset.mem_range] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact ⟨⟨k, hk⟩, standardPeriodPoint_eq_of_sub_mem τ hzt⟩
  · rintro ⟨k, hk⟩
    have hdiff := (standardPeriodPoint_eq_iff_sub_mem τ _ _).mp hk
    have ht : (k.val : ℂ) * (τ : ℂ) / (m : ℂ) ∈
        periodModule ((τ : ℂ) / (m : ℂ)) :=
      divisionPeriodRepresentatives_mem _ _ (by
        simp only [divisionPeriodRepresentatives, Finset.mem_image, Finset.mem_range]
        exact ⟨k.val, k.isLt, rfl⟩)
    simpa only [sub_add_cancel] using (periodModule ((τ : ℂ) / (m : ℂ))).add_mem
      (periodModule_le_divided (τ : ℂ) m hm hdiff) ht

/-- A specified division point in the actual CM kernel, including infinity at index zero. -/
noncomputable def periodCurveCMKernelPoint [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -((m : ℤ) : ℂ)) (k : Fin m) :
    (periodCurveCMEnd τ m hτ).ker :=
  ⟨standardPeriodPoint τ ((k.val : ℂ) * (τ : ℂ) / (m : ℂ)),
    (periodCurveCMEnd_ker_iff τ m hm hτ _).mpr ⟨k, rfl⟩⟩

/-- The specified division points enumerate the entire actual CM kernel without repetition. -/
theorem periodCurveCMKernelPoint_bijective [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -((m : ℤ) : ℂ)) :
    Function.Bijective (periodCurveCMKernelPoint τ m hm hτ) := by
  constructor
  · intro k l h
    apply Fin.ext
    have hpoint := congrArg Subtype.val h
    exact (divisionPeriodPoint_sub_mem_iff τ m hm k.val l.val k.isLt l.isLt).mp
      ((standardPeriodPoint_eq_iff_sub_mem τ _ _).mp hpoint)
  · intro P
    obtain ⟨k, hk⟩ := (periodCurveCMEnd_ker_iff τ m hm hτ P).mp P.property
    exact ⟨k, Subtype.ext hk.symm⟩

/-- The explicit finite coordinate equivalence onto the actual CM kernel. -/
noncomputable def periodCurveCMKernelEquiv [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -((m : ℤ) : ℂ)) :
    Fin m ≃ (periodCurveCMEnd τ m hτ).ker :=
  Equiv.ofBijective _ (periodCurveCMKernelPoint_bijective τ m hm hτ)

/-- The actual quadratic-period point-group kernel has exactly `m` elements. -/
theorem nat_card_periodCurveCMKernel [DecidableEq ℂ]
    (τ : UpperHalfPlane) (m : ℕ) (hm : 0 < m)
    (hτ : (τ : ℂ) ^ 2 = -((m : ℤ) : ℂ)) :
    Nat.card (periodCurveCMEnd τ m hτ).ker = m := by
  calc
    _ = Nat.card (Fin m) := Nat.card_congr (periodCurveCMKernelEquiv τ m hm hτ).symm
    _ = m := Nat.card_fin m

end BakerHeegnerStark
