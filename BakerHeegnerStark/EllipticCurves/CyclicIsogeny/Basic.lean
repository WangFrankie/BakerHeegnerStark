/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.CyclicSublattice.Basic
import BakerHeegnerStark.EllipticCurves.JInvariant.Isogeny

/-!
# Actual cyclic-sublattice point-group isogenies

The rectangular representatives in the finer lattice give the entire kernel
of the actual point-group homomorphism induced by `z ↦ a*z`. Their specified
level coordinates and the finite-kernel target j-invariant use the existing
actual uniformizations. No scheme-morphism degree is asserted.
-/

open scoped Matrix

namespace BakerHeegnerStark

private theorem cyclicIsogeny_positive {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) : 0 < t.1 ∧ 0 < t.2.2 := by
  have h := (mem_cyclicSublatticeTriples hN).mp ht
  constructor <;> nlinarith [h.1]

/-- The actual nonzero scaling factor `1/a`. -/
noncomputable def cyclicIsogenyScale {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) : ℂˣ :=
  Units.mk0 (t.1 : ℂ)⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr
    (ne_of_gt (cyclicIsogeny_positive hN ht).1)))

/-- The actual finer period pair, homothetic to the cyclic-sublattice target. -/
noncomputable def cyclicIsogenyPeriodPair {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) : PeriodPair :=
  scalePeriodPair (standardPeriodPair (cyclicSublatticePoint t τ)) (cyclicIsogenyScale hN ht)

/-- A specified rectangular representative in the finer lattice. -/
noncomputable def cyclicIsogenyRepresentative (t : ℕ × ℕ × ℕ) (τ : UpperHalfPlane)
    (r s : ℕ) : ℂ :=
  ((r : ℂ) + (s : ℂ) * (cyclicSublatticePoint t τ : ℂ)) / (t.1 : ℂ)

/-- The rectangle `0 ≤ r < a`, `0 ≤ s < d`, including zero. -/
noncomputable def cyclicIsogenyRepresentatives (t : ℕ × ℕ × ℕ) (τ : UpperHalfPlane) :
    Finset ℂ := by
  classical
  exact ((Finset.range t.1) ×ˢ (Finset.range t.2.2)).image
    (fun p => cyclicIsogenyRepresentative t τ p.1 p.2)

/-- The specified representatives have the requested unscaled complex formula. -/
theorem cyclicIsogenyRepresentative_eq {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) (r s : ℕ) :
    cyclicIsogenyRepresentative t τ r s = (r : ℂ) / t.1 +
      (s : ℂ) * ((t.1 : ℂ) * (τ : ℂ) + t.2.1) / N := by
  obtain ⟨ha, hd⟩ := cyclicIsogeny_positive hN ht
  have had : (t.1 : ℂ) * (t.2.2 : ℂ) = N := by
    exact_mod_cast ((mem_cyclicSublatticeTriples hN).mp ht).1
  rw [cyclicIsogenyRepresentative, cyclicSublatticePoint_coe ha hd, ← had]
  field_simp [Nat.cast_ne_zero.mpr (ne_of_gt ha), Nat.cast_ne_zero.mpr (ne_of_gt hd)]

/-- Integer coordinates in the actual finer lattice. -/
theorem mem_cyclicIsogenyPeriodPair_iff {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) (z : ℂ) :
    z ∈ (cyclicIsogenyPeriodPair hN ht τ).lattice ↔
      ∃ A B : ℤ, z = ((A : ℂ) + (B : ℂ) * (cyclicSublatticePoint t τ : ℂ)) / t.1 := by
  rw [cyclicIsogenyPeriodPair, PeriodPair.mem_lattice]
  change (∃ A B : ℤ, (A : ℂ) * ((t.1 : ℂ)⁻¹ * 1) +
    (B : ℂ) * ((t.1 : ℂ)⁻¹ * (cyclicSublatticePoint t τ : ℂ)) = z) ↔ _
  simp only [div_eq_mul_inv]
  constructor <;> rintro ⟨A, B, h⟩ <;> refine ⟨A, B, ?_⟩ <;>
    linear_combination -h

/-- The actual source lattice lies in the specified finer lattice. -/
theorem cyclicIsogeny_lattice_le {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    ((standardPeriodPair τ).lattice : Set ℂ) ⊆ (cyclicIsogenyPeriodPair hN ht τ).lattice := by
  obtain ⟨ha, hd⟩ := cyclicIsogeny_positive hN ht
  intro z hz
  obtain ⟨p, q, rfl⟩ := (mem_periodModule_iff (τ : ℂ) _).mp hz
  apply (mem_cyclicIsogenyPeriodPair_iff hN ht τ _).mpr
  refine ⟨t.1 * p - t.2.1 * q, t.2.2 * q, ?_⟩
  rw [cyclicSublatticePoint_coe ha hd]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (ne_of_gt ha), Nat.cast_ne_zero.mpr (ne_of_gt hd)]
  ring

/-- Every specified representative belongs to the actual finer lattice. -/
theorem cyclicIsogenyRepresentatives_mem {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) {z : ℂ}
    (hz : z ∈ cyclicIsogenyRepresentatives t τ) :
    z ∈ (cyclicIsogenyPeriodPair hN ht τ).lattice := by
  classical
  obtain ⟨⟨r, s⟩, _, rfl⟩ := Finset.mem_image.mp hz
  exact (mem_cyclicIsogenyPeriodPair_iff hN ht τ _).mpr ⟨r, s, rfl⟩

private theorem cyclicIsogeny_indices_eq {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane)
    (r s r' s' : ℕ) (hr : r < t.1) (hs : s < t.2.2)
    (hr' : r' < t.1) (hs' : s' < t.2.2)
    (hz : cyclicIsogenyRepresentative t τ r s - cyclicIsogenyRepresentative t τ r' s' ∈
      (standardPeriodPair τ).lattice) : r = r' ∧ s = s' := by
  obtain ⟨ha, hd⟩ := cyclicIsogeny_positive hN ht
  obtain ⟨p, q, hpq⟩ := (mem_periodModule_iff (τ : ℂ) _).mp hz
  have heq : (((r : ℤ) - r') * t.2.2 + ((s : ℤ) - s') * t.2.1 : ℤ) +
      ((((s : ℤ) - s') * t.1 : ℤ) : ℂ) * (τ : ℂ) =
      (((t.1 : ℤ) * t.2.2 * p : ℤ) : ℂ) +
      (((t.1 : ℤ) * t.2.2 * q : ℤ) : ℂ) * (τ : ℂ) := by
    dsimp [cyclicIsogenyRepresentative] at hpq
    rw [cyclicSublatticePoint_coe ha hd] at hpq
    push_cast
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt ha), Nat.cast_ne_zero.mpr (ne_of_gt hd)] at hpq
    linear_combination hpq
  obtain ⟨h₁, h₂⟩ := periodModule_coordinates_eq (τ : ℂ) (ne_of_gt τ.im_pos) heq
  have hsd : (s : ℤ) - s' = (t.2.2 : ℤ) * q := by
    nlinarith [show (0 : ℤ) < t.1 by exact_mod_cast ha]
  have hss : s = s' := by
    have hq : q = 0 := by
      have hsi : (s : ℤ) < t.2.2 := by exact_mod_cast hs
      have hsi' : (s' : ℤ) < t.2.2 := by exact_mod_cast hs'
      have hdi : (0 : ℤ) < t.2.2 := by exact_mod_cast hd
      nlinarith
    rw [hq, mul_zero] at hsd
    exact_mod_cast sub_eq_zero.mp hsd
  subst s'
  have hrp : (r : ℤ) - r' = (t.1 : ℤ) * p := by
    nlinarith [show (0 : ℤ) < t.2.2 by exact_mod_cast hd]
  have hrr : r = r' := by
    have hp : p = 0 := by
      have hri : (r : ℤ) < t.1 := by exact_mod_cast hr
      have hri' : (r' : ℤ) < t.1 := by exact_mod_cast hr'
      have hai : (0 : ℤ) < t.1 := by exact_mod_cast ha
      nlinarith
    rw [hp, mul_zero] at hrp
    exact_mod_cast sub_eq_zero.mp hrp
  exact ⟨hrr, rfl⟩

/-- The rectangle contains no repeated source-lattice cosets. -/
theorem cyclicIsogenyRepresentatives_separated {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane)
    (z : ℂ) (hz : z ∈ cyclicIsogenyRepresentatives t τ)
    (w : ℂ) (hw : w ∈ cyclicIsogenyRepresentatives t τ)
    (hzw : z - w ∈ (standardPeriodPair τ).lattice) : z = w := by
  classical
  obtain ⟨⟨r, s⟩, hrs, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨⟨r', s'⟩, hrs', rfl⟩ := Finset.mem_image.mp hw
  simp only [Finset.mem_product, Finset.mem_range] at hrs hrs'
  obtain ⟨rfl, rfl⟩ := cyclicIsogeny_indices_eq hN ht τ r s r' s'
    hrs.1 hrs.2 hrs'.1 hrs'.2 hzw
  rfl

/-- The rectangle covers every coset, with no additional quotient hypothesis. -/
theorem cyclicIsogenyRepresentatives_cover {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) (z : ℂ)
    (hz : z ∈ (cyclicIsogenyPeriodPair hN ht τ).lattice) :
    ∃ w ∈ cyclicIsogenyRepresentatives t τ, z - w ∈ (standardPeriodPair τ).lattice := by
  classical
  obtain ⟨ha, hd⟩ := cyclicIsogeny_positive hN ht
  let : NeZero t.1 := ⟨ne_of_gt ha⟩
  let : NeZero t.2.2 := ⟨ne_of_gt hd⟩
  obtain ⟨A, B, rfl⟩ := (mem_cyclicIsogenyPeriodPair_iff hN ht τ z).mp hz
  let s := (B : ZMod t.2.2).val
  have hs : s < t.2.2 := ZMod.val_lt _
  have hBd : (t.2.2 : ℤ) ∣ B - s := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [s]
  obtain ⟨v, hv⟩ := hBd
  let r := (A + (t.2.1 : ℤ) * v : ZMod t.1).val
  have hr : r < t.1 := ZMod.val_lt _
  have hAa : (t.1 : ℤ) ∣ A + (t.2.1 : ℤ) * v - r := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [r]
  obtain ⟨u, hu⟩ := hAa
  refine ⟨cyclicIsogenyRepresentative t τ r s, Finset.mem_image.mpr
    ⟨(r, s), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hr, Finset.mem_range.mpr hs⟩, rfl⟩,
    (mem_periodModule_iff (τ : ℂ) _).mpr ⟨u, v, ?_⟩⟩
  have hvC : (B : ℂ) - s = (t.2.2 : ℂ) * v := by exact_mod_cast hv
  have huC : (A : ℂ) + (t.2.1 : ℂ) * v - r = (t.1 : ℂ) * u := by exact_mod_cast hu
  rw [cyclicIsogenyRepresentative, cyclicSublatticePoint_coe ha hd]
  field_simp [Nat.cast_ne_zero.mpr (ne_of_gt ha), Nat.cast_ne_zero.mpr (ne_of_gt hd)]
  linear_combination (t.2.2 : ℂ) * huC +
    ((t.1 : ℂ) * (τ : ℂ) + t.2.1) * hvC

/-- Zero is the `(0,0)` representative. -/
theorem zero_mem_cyclicIsogenyRepresentatives {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    0 ∈ cyclicIsogenyRepresentatives t τ := by
  classical
  obtain ⟨ha, hd⟩ := cyclicIsogeny_positive hN ht
  apply Finset.mem_image.mpr
  refine ⟨(0, 0), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hd⟩, ?_⟩
  simp [cyclicIsogenyRepresentative]

/-- There are exactly `N` actual complex representatives. -/
theorem card_cyclicIsogenyRepresentatives {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    (cyclicIsogenyRepresentatives t τ).card = N := by
  classical
  have hinj : Set.InjOn (fun p : ℕ × ℕ => cyclicIsogenyRepresentative t τ p.1 p.2)
      (((Finset.range t.1) ×ˢ (Finset.range t.2.2) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro ⟨r, s⟩ hrs ⟨r', s'⟩ hrs' h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hrs hrs'
    dsimp only at h
    have hzero : cyclicIsogenyRepresentative t τ r s - cyclicIsogenyRepresentative t τ r' s' ∈
        (standardPeriodPair τ).lattice := by
      rw [h, sub_self]
      exact (standardPeriodPair τ).lattice.zero_mem
    obtain ⟨rfl, rfl⟩ := cyclicIsogeny_indices_eq hN ht τ r s r' s'
      hrs.1 hrs.2 hrs'.1 hrs'.2 hzero
    rfl
  rw [cyclicIsogenyRepresentatives, Finset.card_image_of_injOn hinj,
    Finset.card_product, Finset.card_range, Finset.card_range]
  exact ((mem_cyclicSublatticeTriples hN).mp ht).1

/-- The entire actual finite kernel on the source j-model. -/
noncomputable def cyclicIsogenyKernel [DecidableEq ℂ] (t : ℕ × ℕ × ℕ) (τ : UpperHalfPlane) :
    Finset ((jInvariantCurve τ).baseChange ℂ).toAffine.Point :=
  (cyclicIsogenyRepresentatives t τ).image (jInvariantPeriodPoint τ)

/-- Multiplication by `a` sends the finer lattice exactly to the target lattice. -/
theorem cyclicIsogeny_mul_mem_iff {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) (z : ℂ) :
    (t.1 : ℂ) * z ∈ periodModule (cyclicSublatticePoint t τ : ℂ) ↔
      z ∈ (cyclicIsogenyPeriodPair hN ht τ).lattice := by
  have haC : (t.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (cyclicIsogeny_positive hN ht).1)
  rw [mem_periodModule_iff, mem_cyclicIsogenyPeriodPair_iff hN ht τ]
  constructor
  · rintro ⟨A, B, h⟩
    exact ⟨A, B, (eq_div_iff haC).mpr (by simpa only [mul_comm] using h)⟩
  · rintro ⟨A, B, rfl⟩
    exact ⟨A, B, mul_div_cancel₀ _ haC⟩

/-- The quotient map is induced by actual complex multiplication by `a`. -/
noncomputable def cyclicIsogenyTorusMap {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    PeriodTorus (τ : ℂ) →ₗ[ℤ] PeriodTorus (cyclicSublatticePoint t τ : ℂ) :=
  (periodModule (τ : ℂ)).mapQ (periodModule (cyclicSublatticePoint t τ : ℂ))
    (LinearMap.mulLeft ℤ (t.1 : ℂ)) (by
      intro z hz
      exact (cyclicIsogeny_mul_mem_iff hN ht τ z).mpr (cyclicIsogeny_lattice_le hN ht τ hz))

/-- The actual homomorphism of the two chosen j-model point groups. -/
noncomputable def cyclicIsogeny [DecidableEq ℂ] {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    ((jInvariantCurve τ).baseChange ℂ).toAffine.Point →+
      ((jInvariantCurve (cyclicSublatticePoint t τ)).baseChange ℂ).toAffine.Point :=
  (jInvariantCurveTorusEquiv (cyclicSublatticePoint t τ)).toAddMonoidHom.comp
    ((cyclicIsogenyTorusMap hN ht τ).toAddMonoidHom.comp
      (jInvariantCurveTorusEquiv τ).symm.toAddMonoidHom)

/-- The transported map retains the actual complex multiplication formula. -/
theorem cyclicIsogeny_periodPoint [DecidableEq ℂ] {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) (z : ℂ) :
    cyclicIsogeny hN ht τ (jInvariantPeriodPoint τ z) =
      jInvariantPeriodPoint (cyclicSublatticePoint t τ) ((t.1 : ℂ) * z) := by
  let e := jInvariantCurveTorusEquiv τ
  have he : e ((periodModule (τ : ℂ)).mkQ z) = jInvariantPeriodPoint τ z := rfl
  change (jInvariantCurveTorusEquiv (cyclicSublatticePoint t τ))
    (cyclicIsogenyTorusMap hN ht τ (e.symm (jInvariantPeriodPoint τ z))) = _
  rw [← he, e.symm_apply_apply]
  rfl

/-- The explicit finite set is the kernel on all actual source points. -/
theorem cyclicIsogeny_eq_zero_iff [DecidableEq ℂ] {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane)
    (P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) :
    cyclicIsogeny hN ht τ P = 0 ↔ P ∈ cyclicIsogenyKernel t τ := by
  classical
  obtain ⟨z, hz⟩ := (jInvariantCurveTorusEquiv τ).surjective P
  obtain ⟨w, hw⟩ := (periodModule (τ : ℂ)).mkQ_surjective z
  have hP : jInvariantPeriodPoint τ w = P := by
    change jInvariantCurveTorusEquiv τ ((periodModule (τ : ℂ)).mkQ w) = P
    rw [hw, hz]
  rw [← hP]
  rw [cyclicIsogeny_periodPoint, jInvariantPeriodPoint_eq_zero_iff,
    standardPeriodPair_lattice_eq_periodModule, cyclicIsogeny_mul_mem_iff hN ht τ w]
  constructor
  · intro hzM
    obtain ⟨v, hv, hwv⟩ := cyclicIsogenyRepresentatives_cover hN ht τ w hzM
    exact Finset.mem_image.mpr ⟨v, hv, ((jInvariantPeriodPoint_eq_iff_sub_mem τ w v).mpr hwv).symm⟩
  · intro h
    obtain ⟨v, hv, hvp⟩ := Finset.mem_image.mp h
    have hwv := (jInvariantPeriodPoint_eq_iff_sub_mem τ w v).mp hvp.symm
    have := (cyclicIsogenyPeriodPair hN ht τ).lattice.add_mem
      (cyclicIsogeny_lattice_le hN ht τ hwv) (cyclicIsogenyRepresentatives_mem hN ht τ hv)
    simpa only [sub_add_cancel] using this

/-- The actual kernel contains exactly `N` source points. -/
theorem card_cyclicIsogenyKernel [DecidableEq ℂ] {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    (cyclicIsogenyKernel t τ).card = N := by
  classical
  rw [cyclicIsogenyKernel, Finset.card_image_of_injOn
    (jInvariantPeriodPoint_injOn τ _ (cyclicIsogenyRepresentatives_separated hN ht τ)),
    card_cyclicIsogenyRepresentatives hN ht τ]

/-- The actual torsion-coordinate equivalence gives the prescribed coordinate vector. -/
theorem cyclicIsogenyRepresentative_coordinates [DecidableEq ℂ] {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) (r s : ℕ) :
    (jInvariantCurveTorsionCoordinatesEquiv τ N hN
      ![((t.2.2 * r + t.2.1 * s : ℕ) : ZMod N), ((t.1 * s : ℕ) : ZMod N)] :
        ((jInvariantCurve τ).baseChange ℂ).toAffine.Point) =
      jInvariantPeriodPoint τ (cyclicIsogenyRepresentative t τ r s) := by
  change jInvariantCurvePointEquiv τ
    (periodCurveTorsionCoordinatesEquiv τ N hN _) = _
  rw [show ![((t.2.2 * r + t.2.1 * s : ℕ) : ZMod N), ((t.1 * s : ℕ) : ZMod N)] =
    ![(((t.2.2 : ℤ) * r + (t.2.1 : ℤ) * s : ℤ) : ZMod N),
      (((t.1 : ℤ) * s : ℤ) : ZMod N)] by push_cast; rfl,
    periodCurveTorsionCoordinatesEquiv_intCast]
  congr 2
  rw [cyclicIsogenyRepresentative_eq hN ht]
  have had : (t.1 : ℂ) * (t.2.2 : ℂ) = N := by
    exact_mod_cast ((mem_cyclicSublatticeTriples hN).mp ht).1
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (ne_of_gt (cyclicIsogeny_positive hN ht).1),
    Nat.cast_ne_zero.mpr (ne_of_gt hN)]
  linear_combination (r : ℂ) * had

/-- Every point of the actual kernel is killed by `N`. -/
theorem cyclicIsogenyKernel_nsmul [DecidableEq ℂ] {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane)
    {P : ((jInvariantCurve τ).baseChange ℂ).toAffine.Point}
    (hP : P ∈ cyclicIsogenyKernel t τ) : N • P = 0 := by
  obtain ⟨z, hz, hpoint⟩ := Finset.mem_image.mp hP
  obtain ⟨q, hq, hrep⟩ :=
    (@Finset.mem_image (ℕ × ℕ) ℂ Complex.instDecidableEq _ _ _).mp hz
  rcases q with ⟨r, s⟩
  rw [← hpoint, ← hrep, ← cyclicIsogenyRepresentative_coordinates hN ht τ r s]
  exact AddSubgroup.torsionBy.nsmul_iff.mp
    (jInvariantCurveTorsionCoordinatesEquiv τ N hN _).property

/-- Vélu's actual finite-kernel j-expression is the stated cyclic-sublattice j-value. -/
theorem cyclicIsogenyKernel_jInvariant [DecidableEq ℂ] {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    jInvariantKernelJ τ (cyclicIsogenyKernel t τ) =
      ModularForm.jInvariant (cyclicSublatticePoint t τ) :=
  jInvariantKernelJ_scaled_target τ (cyclicSublatticePoint t τ) (cyclicIsogenyScale hN ht)
    (cyclicIsogenyRepresentatives t τ) (cyclicIsogeny_lattice_le hN ht τ)
    (fun _ => cyclicIsogenyRepresentatives_mem hN ht τ)
    (cyclicIsogenyRepresentatives_separated hN ht τ)
    (cyclicIsogenyRepresentatives_cover hN ht τ) (zero_mem_cyclicIsogenyRepresentatives hN ht τ)

/-- The actual kernel invariant expression has nonzero discriminant. -/
theorem cyclicIsogenyKernel_discriminant_ne_zero [DecidableEq ℂ] {N : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    jInvariantKernelG₂ τ (cyclicIsogenyKernel t τ) ^ 3 -
      27 * jInvariantKernelG₃ τ (cyclicIsogenyKernel t τ) ^ 2 ≠ 0 :=
  jInvariantKernel_discriminant_scaled_ne_zero τ (cyclicSublatticePoint t τ)
    (cyclicIsogenyScale hN ht) (cyclicIsogenyRepresentatives t τ)
    (cyclicIsogeny_lattice_le hN ht τ) (fun _ => cyclicIsogenyRepresentatives_mem hN ht τ)
    (cyclicIsogenyRepresentatives_separated hN ht τ)
    (cyclicIsogenyRepresentatives_cover hN ht τ) (zero_mem_cyclicIsogenyRepresentatives hN ht τ)

end BakerHeegnerStark
