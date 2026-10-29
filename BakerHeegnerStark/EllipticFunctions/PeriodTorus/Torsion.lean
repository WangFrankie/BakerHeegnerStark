/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.PeriodLattice.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Torsion coordinates on a quadratic period torus

For a nonreal period `τ` and a positive integer `N`, the actual quotient
`ℂ / (ℤ + ℤτ)` has `N`-torsion additively equivalent to `(ℤ/Nℤ)²`.
The specified coordinates send `(a,b)` to the class of `(a+bτ)/N`;
they are not a Smith-normal-form basis chosen up to an unspecified change.

When `τ² = -m`, multiplication by `τ` descends to the actual period torus
and its torsion, satisfies the same quadratic relation, and acts on these
coordinate columns by `[[0,-m],[1,0]]`. This is the quadratic generator in
`LinearAlgebra/Matrix/QuadraticCentralizer.lean`.

These are analytic quotient-group statements. They do not identify the torus
with the points of an algebraic elliptic curve, define its CM endomorphism
over a number field, or establish arithmetic Galois compatibility.
-/

open scoped Matrix

namespace BakerHeegnerStark

/-- The actual additive quotient of the complex plane by its two-period lattice. -/
abbrev PeriodTorus (τ : ℂ) := ℂ ⧸ periodModule τ
/-- The actual `N`-torsion subgroup of the period torus. -/
abbrev PeriodTorsion (τ : ℂ) (N : ℕ) :=
  AddSubgroup.torsionBy (PeriodTorus τ) (N : ℤ)

/-- The division point represented by `(a+bτ)/N` in the actual torsion subgroup. -/
noncomputable def periodTorsionPoint (τ : ℂ) (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    PeriodTorsion τ N :=
  ⟨(periodModule τ).mkQ (((a : ℂ) + (b : ℂ) * τ) / (N : ℂ)), by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    rw [← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt hN))]
    exact (Submodule.Quotient.mk_eq_zero (periodModule τ)).mpr ((mem_periodModule_iff τ _).mpr ⟨a, b, rfl⟩)⟩

/-- A division point is zero exactly when both coordinates vanish modulo `N`. -/
theorem periodTorsionPoint_eq_zero_iff (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    periodTorsionPoint τ N hN a b = 0 ↔ (a : ZMod N) = 0 ∧ (b : ZMod N) = 0 := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  rw [Subtype.ext_iff]
  change ((Submodule.Quotient.mk (((a : ℂ) + (b : ℂ) * τ) / (N : ℂ)) :
    PeriodTorus τ) = 0) ↔ _
  rw [Submodule.Quotient.mk_eq_zero, mem_periodModule_iff,
    ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨c, d, h⟩
    have heq : (a : ℂ) + (b : ℂ) * τ =
        (((N : ℤ) * c : ℤ) : ℂ) + (((N : ℤ) * d : ℤ) : ℂ) * τ := by
      rw [(div_eq_iff hNC).mp h]
      push_cast
      ring
    obtain ⟨ha, hb⟩ := periodModule_coordinates_eq τ hτ heq
    exact ⟨⟨c, ha⟩, ⟨d, hb⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    refine ⟨c, d, (div_eq_iff hNC).mpr ?_⟩
    push_cast
    ring

/-- The additive coordinate map using the specified division points `1/N` and `τ/N`. -/
noncomputable def periodTorsionCoordinates (τ : ℂ) (N : ℕ) (hN : 0 < N) :
    (Fin 2 → ZMod N) →+ PeriodTorsion τ N := by
  letI := AddSubgroup.torsionBy.zmodModule (A := PeriodTorus τ) (n := N)
  exact
    { toFun := fun x => x 0 • periodTorsionPoint τ N hN 1 0 +
        x 1 • periodTorsionPoint τ N hN 0 1
      map_zero' := by simp
      map_add' := by intro x y; simp [add_smul, add_add_add_comm] }

/-- Integer coordinate representatives give exactly the specified complex division point. -/
theorem periodTorsionCoordinates_intCast (τ : ℂ) (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    periodTorsionCoordinates τ N hN ![(a : ZMod N), (b : ZMod N)] =
      periodTorsionPoint τ N hN a b := by
  let _ := AddSubgroup.torsionBy.zmodModule (A := PeriodTorus τ) (n := N)
  change (a : ZMod N) • periodTorsionPoint τ N hN 1 0 +
    (b : ZMod N) • periodTorsionPoint τ N hN 0 1 = _
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_zsmul, periodTorsionPoint,
    Int.cast_one, Int.cast_zero]
  change a • (periodModule τ).mkQ ((1 + 0 * τ) / (N : ℂ)) +
    b • (periodModule τ).mkQ ((0 + 1 * τ) / (N : ℂ)) = _
  rw [← map_zsmul, ← map_zsmul, ← map_add]
  apply congrArg (periodModule τ).mkQ
  simp only [zsmul_eq_mul, zero_mul, add_zero, one_mul, zero_add]
  ring

/-- The specified coordinate map is bijective for every nonreal period and positive level. -/
theorem periodTorsionCoordinates_bijective (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) : Function.Bijective (periodTorsionCoordinates τ N hN) := by
  have hker : ∀ x, periodTorsionCoordinates τ N hN x = 0 → x = 0 := by
    intro x hx
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (x 0)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (x 1)
    have hxv : x = ![(a : ZMod N), (b : ZMod N)] := by
      ext i
      fin_cases i
      · exact ha.symm
      · exact hb.symm
    rw [hxv, periodTorsionCoordinates_intCast] at hx
    obtain ⟨ha0, hb0⟩ := (periodTorsionPoint_eq_zero_iff τ hτ N hN a b).mp hx
    rw [hxv]
    ext i
    fin_cases i
    · exact ha0
    · exact hb0
  constructor
  · intro x y h
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, h, sub_self]
  · intro x
    obtain ⟨z, hz⟩ := (periodModule τ).mkQ_surjective (x : PeriodTorus τ)
    have hn : (periodModule τ).mkQ ((N : ℂ) * z) = 0 := by
      rw [← nsmul_eq_mul, map_nsmul, hz]
      exact AddSubgroup.torsionBy.nsmul_iff.mp x.property
    obtain ⟨a, b, hab⟩ := (mem_periodModule_iff τ _).mp
      ((Submodule.Quotient.mk_eq_zero (periodModule τ)).mp hn)
    refine ⟨![(a : ZMod N), (b : ZMod N)], ?_⟩
    rw [periodTorsionCoordinates_intCast]
    apply Subtype.ext
    change (periodModule τ).mkQ (((a : ℂ) + (b : ℂ) * τ) / (N : ℂ)) = _
    rw [← hz]
    apply congrArg (periodModule τ).mkQ
    apply (div_eq_iff (Nat.cast_ne_zero.mpr (ne_of_gt hN))).mpr
    simpa only [mul_comm] using hab.symm

/-- The full level-`N` structure of the actual period torus in the ordered basis `[1,τ]`. -/
noncomputable def periodTorsionEquiv (τ : ℂ) (hτ : τ.im ≠ 0) (N : ℕ) (hN : 0 < N) :
    (Fin 2 → ZMod N) ≃+ PeriodTorsion τ N :=
  AddEquiv.ofBijective (periodTorsionCoordinates τ N hN)
    (periodTorsionCoordinates_bijective τ hτ N hN)

/-- Multiplication by the quadratic period descends to the actual period torus. -/
noncomputable def periodTorusCMEnd (τ : ℂ) (m : ℤ) (hτ : τ ^ 2 = -(m : ℂ)) :
    PeriodTorus τ →ₗ[ℤ] PeriodTorus τ :=
  (periodModule τ).mapQ (periodModule τ) (LinearMap.mulLeft ℤ τ) (by
    intro z hz
    have hmem : τ ∈ periodModule τ := (mem_periodModule_iff τ τ).mpr ⟨0, 1, by simp⟩
    exact ((mul_preserves_periodModule_iff τ τ (-m) 0
      (by simpa using hτ)).mpr hmem) z hz)

/-- The actual CM endomorphism restricts to the actual `N`-torsion subgroup. -/
noncomputable def periodTorsionCMEnd (τ : ℂ) (N : ℕ) (m : ℤ)
    (hτ : τ ^ 2 = -(m : ℂ)) : PeriodTorsion τ N →+ PeriodTorsion τ N where
  toFun x := ⟨periodTorusCMEnd τ m hτ x, by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp x.property, map_zero]⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _

/-- Multiplication by `τ` sends integer division-point coordinates `(a,b)` to `(-mb,a)`. -/
theorem periodTorsionCMEnd_point (τ : ℂ) (N : ℕ) (hN : 0 < N) (m : ℤ)
    (hτ : τ ^ 2 = -(m : ℂ)) (a b : ℤ) :
    periodTorsionCMEnd τ N m hτ (periodTorsionPoint τ N hN a b) =
      periodTorsionPoint τ N hN (-m * b) a := by
  apply Subtype.ext
  change (periodModule τ).mkQ (τ * (((a : ℂ) + (b : ℂ) * τ) / (N : ℂ))) =
    (periodModule τ).mkQ ((((-m * b : ℤ) : ℂ) + (a : ℂ) * τ) / (N : ℂ))
  apply congrArg (periodModule τ).mkQ
  push_cast
  simp only [div_eq_mul_inv]
  linear_combination (b : ℂ) * (N : ℂ)⁻¹ * hτ

/-- The full level equivalence retains the specified integer division-point formula. -/
theorem periodTorsionEquiv_intCast (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    periodTorsionEquiv τ hτ N hN ![(a : ZMod N), (b : ZMod N)] =
      periodTorsionPoint τ N hN a b :=
  periodTorsionCoordinates_intCast τ N hN a b

/-- The actual CM endomorphism in the specified residue coordinates. -/
theorem periodTorsionCMEnd_equiv_apply (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) (m : ℤ) (hm : τ ^ 2 = -(m : ℂ)) (x : Fin 2 → ZMod N) :
    periodTorsionCMEnd τ N m hm (periodTorsionEquiv τ hτ N hN x) =
      periodTorsionEquiv τ hτ N hN ![-(m : ZMod N) * x 1, x 0] := by
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (x 0)
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective (x 1)
  have hx : x = ![(a : ZMod N), (b : ZMod N)] := by
    ext i
    fin_cases i
    · exact ha.symm
    · exact hb.symm
  have hex : periodTorsionEquiv τ hτ N hN x = periodTorsionPoint τ N hN a b := by
    rw [hx, periodTorsionEquiv_intCast]
  rw [hex, periodTorsionCMEnd_point, ← periodTorsionEquiv_intCast τ hτ N hN (-m * b) a]
  apply congrArg (periodTorsionEquiv τ hτ N hN)
  ext i
  fin_cases i <;> simp [← ha, ← hb]

/-- The quadratic companion matrix acts on actual period-torus torsion coordinates. -/
theorem periodTorsionCMEnd_eq_matrix (τ : ℂ) (hτ : τ.im ≠ 0)
    (N : ℕ) (hN : 0 < N) (m : ℤ) (hm : τ ^ 2 = -(m : ℂ)) (x : Fin 2 → ZMod N) :
    (periodTorsionEquiv τ hτ N hN).symm
        (periodTorsionCMEnd τ N m hm (periodTorsionEquiv τ hτ N hN x)) =
      (!![0, -(m : ZMod N); 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x := by
  rw [periodTorsionCMEnd_equiv_apply, AddEquiv.symm_apply_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The actual torsion subgroup has `N²` elements, also at composite levels. -/
theorem nat_card_periodTorsion (τ : ℂ) (hτ : τ.im ≠ 0) (N : ℕ) (hN : 0 < N) :
    Nat.card (PeriodTorsion τ N) = N ^ 2 := by
  calc
    Nat.card (PeriodTorsion τ N) = Nat.card (Fin 2 → ZMod N) :=
      Nat.card_congr (periodTorsionEquiv τ hτ N hN).symm.toEquiv
    _ = N ^ 2 := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

/-- The actual torus endomorphism satisfies the quadratic CM relation. -/
theorem periodTorusCMEnd_sq (τ : ℂ) (m : ℤ) (hτ : τ ^ 2 = -(m : ℂ)) :
    (periodTorusCMEnd τ m hτ).comp (periodTorusCMEnd τ m hτ) =
      (-m) • LinearMap.id := by
  ext z
  change (periodModule τ).mkQ (τ * (τ * z)) = (-m) • (periodModule τ).mkQ z
  rw [← map_smul]
  apply congrArg (periodModule τ).mkQ
  simp only [zsmul_eq_mul, Int.cast_neg]
  calc
    τ * (τ * z) = τ ^ 2 * z := by ring
    _ = -(m : ℂ) * z := by rw [hτ]

end BakerHeegnerStark
