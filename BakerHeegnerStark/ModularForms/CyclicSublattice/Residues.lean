/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ModularForms.ModularPolynomial.Basic
import BakerHeegnerStark.ModularForms.QExpansion.Cyclotomic
import Mathlib.Data.Nat.ModEq

/-!
# Coprime Reindexing of Cyclic-Sublattice Residues

Multiplication by a natural number coprime to the level permutes the actual
primitive triples `(a, b, d)` by replacing `b` with `(u * b) % d`. The associated
translation phase is raised to the `u`-th power. These are finite combinatorial
inputs for cyclotomic reindexing, not a coefficient-descent assertion.
-/

noncomputable section

namespace BakerHeegnerStark

/-- Coprime multiplication modulo the width preserves every defining condition
of a primitive cyclic-sublattice triple. -/
theorem cyclicSublatticeTriples_mul_mod_mem {N u : ℕ} (hN : 0 < N)
    (hu : Nat.Coprime u N) {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicSublatticeTriples N) :
    (t.1, (u * t.2.1) % t.2.2, t.2.2) ∈ cyclicSublatticeTriples N := by
  obtain ⟨had, hbd, hgcd⟩ := (mem_cyclicSublatticeTriples hN).mp ht
  have hd : 0 < t.2.2 := lt_of_le_of_lt (Nat.zero_le _) hbd
  have hdN : t.2.2 ∣ N := by
    rw [← had]
    exact Nat.dvd_mul_left _ _
  have hud : Nat.Coprime u t.2.2 := hu.of_dvd_right hdN
  have hgcdmod : Nat.gcd ((u * t.2.1) % t.2.2) t.2.2 = Nat.gcd t.2.1 t.2.2 := by
    rw [← Nat.gcd_rec, Nat.gcd_comm t.2.2, hud.gcd_mul_left_cancel]
  apply (mem_cyclicSublatticeTriples hN).mpr
  refine ⟨had, Nat.mod_lt _ hd, ?_⟩
  simpa only [Nat.gcd_assoc, hgcdmod] using hgcd

private def cyclicSublatticeResidueMap {N : ℕ} (hN : 0 < N) (u : ℕ)
    (hu : Nat.Coprime u N) :
    {t // t ∈ cyclicSublatticeTriples N} → {t // t ∈ cyclicSublatticeTriples N} :=
  fun t => ⟨(t.val.1, (u * t.val.2.1) % t.val.2.2, t.val.2.2),
    cyclicSublatticeTriples_mul_mod_mem hN hu t.property⟩

private theorem cyclicSublatticeResidueMap_injective {N : ℕ} (hN : 0 < N) (u : ℕ)
    (hu : Nat.Coprime u N) : Function.Injective (cyclicSublatticeResidueMap hN u hu) := by
  intro s t h
  have hval :
      (s.val.1, (u * s.val.2.1) % s.val.2.2, s.val.2.2) =
        (t.val.1, (u * t.val.2.1) % t.val.2.2, t.val.2.2) :=
    congrArg Subtype.val h
  have ha := congrArg (fun q : ℕ × ℕ × ℕ => q.1) hval
  have hd := congrArg (fun q : ℕ × ℕ × ℕ => q.2.2) hval
  change s.val.1 = t.val.1 at ha
  change s.val.2.2 = t.val.2.2 at hd
  have hbmod : (u * s.val.2.1) % s.val.2.2 = (u * t.val.2.1) % t.val.2.2 :=
    congrArg (fun q : ℕ × ℕ × ℕ => q.2.1) hval
  rw [← hd] at hbmod
  have hs := (mem_cyclicSublatticeTriples hN).mp s.property
  have ht := (mem_cyclicSublatticeTriples hN).mp t.property
  have hdN : s.val.2.2 ∣ N := by
    exact (Nat.dvd_mul_left s.val.2.2 s.val.1).trans (dvd_of_eq hs.1)
  have hud : Nat.Coprime u s.val.2.2 := hu.of_dvd_right hdN
  have hb : s.val.2.1 = t.val.2.1 :=
    (Nat.ModEq.cancel_left_of_coprime hud.symm.gcd_eq_one hbmod).eq_of_lt_of_lt
      hs.2.1 (by simpa only [hd] using ht.2.1)
  exact Subtype.ext (Prod.ext ha (Prod.ext hb hd))

/-- Multiplication by `u`, reduced modulo each width, permutes the primitive
cyclic-sublattice triples when `u` is coprime to the level. -/
def cyclicSublatticeResiduePerm {N : ℕ} (hN : 0 < N) (u : ℕ)
    (hu : Nat.Coprime u N) : Equiv.Perm {t // t ∈ cyclicSublatticeTriples N} :=
  Equiv.ofBijective (cyclicSublatticeResidueMap hN u hu)
    (cyclicSublatticeResidueMap_injective hN u hu).bijective_of_finite

/-- The permutation has the specified residue-multiplication action, not merely
an abstract existence property. -/
@[simp]
theorem cyclicSublatticeResiduePerm_apply_val {N : ℕ} (hN : 0 < N) (u : ℕ)
    (hu : Nat.Coprime u N) (t : {t // t ∈ cyclicSublatticeTriples N}) :
    (cyclicSublatticeResiduePerm hN u hu t).val =
      (t.val.1, (u * t.val.2.1) % t.val.2.2, t.val.2.2) :=
  rfl

/-- Multiplying the translation numerator raises its phase to that power. -/
theorem cyclicSublatticePhase_mul (u b d : ℕ) :
    cyclicSublatticePhase (u * b) d = cyclicSublatticePhase b d ^ u := by
  unfold cyclicSublatticePhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Reduction of the translation numerator modulo a positive width leaves its
phase unchanged. -/
theorem cyclicSublatticePhase_mod (b : ℕ) {d : ℕ} (hd : 0 < d) :
    cyclicSublatticePhase (b % d) d = cyclicSublatticePhase b d := by
  calc
    cyclicSublatticePhase (b % d) d = cyclicSublatticePhase 1 d ^ (b % d) := by
      simpa only [mul_one] using cyclicSublatticePhase_mul (b % d) 1 d
    _ = cyclicSublatticePhase 1 d ^ b :=
      (pow_eq_pow_mod b (cyclicSublatticePhase_pow hd)).symm
    _ = cyclicSublatticePhase b d := by
      simpa only [mul_one] using (cyclicSublatticePhase_mul b 1 d).symm

/-- The precise phase identity for multiplication followed by residue reduction. -/
theorem cyclicSublatticePhase_mul_mod (u b : ℕ) {d : ℕ} (hd : 0 < d) :
    cyclicSublatticePhase ((u * b) % d) d = cyclicSublatticePhase b d ^ u := by
  rw [cyclicSublatticePhase_mod _ hd, cyclicSublatticePhase_mul]

/-- The explicit permutation of primitive triples implements the power action
on their translation phases. -/
theorem cyclicSublatticeResiduePerm_phase {N : ℕ} (hN : 0 < N) (u : ℕ)
    (hu : Nat.Coprime u N) (t : {t // t ∈ cyclicSublatticeTriples N}) :
    cyclicSublatticePhase (cyclicSublatticeResiduePerm hN u hu t).val.2.1
        (cyclicSublatticeResiduePerm hN u hu t).val.2.2 =
      cyclicSublatticePhase t.val.2.1 t.val.2.2 ^ u := by
  have hbd := ((mem_cyclicSublatticeTriples hN).mp t.property).2.1
  change cyclicSublatticePhase ((u * t.val.2.1) % t.val.2.2) t.val.2.2 = _
  exact cyclicSublatticePhase_mul_mod u t.val.2.1 (lt_of_le_of_lt (Nat.zero_le _) hbd)

end BakerHeegnerStark
