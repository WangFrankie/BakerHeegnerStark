/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.FixedMatrixDiscriminant
import BakerHeegnerStark.ModularForms.JInvariant.Basic
import BinaryQuadraticForms.Computable.Reduction
import BinaryQuadraticForms.Core.UpperHalfPlane

/-!
# Actual j-Values of Enumerated Reduced Forms

The finite set below is the image of QNF's existing primitive reduced-form
enumeration under its actual upper-half-plane root and the analytic j-invariant.
A primitive integral quadratic relation at a point of the upper half-plane puts
its j-value in this image: root uniqueness identifies the point with `tauOfForm`,
and proper equivalence supplies an actual modular transformation after reduction.
-/

namespace BakerHeegnerStark

open QuadraticNumberFields BinaryQuadraticForm

/-- The actual j-values of the primitive reduced positive definite forms of
integer discriminant `D`. Positivity is obtained from enumeration membership. -/
noncomputable def reducedFormJValues (D : ℤ) : Finset ℂ := by
  classical
  exact (enumPrimitiveReducedForms D).attach.image fun Q =>
    ModularForm.jInvariant
      (tauOfForm Q.val (of_mem_enumPrimitiveReducedForms Q.property).2.1)

/-- Taking actual j-values cannot increase the size of the reduced-form
 enumeration. -/
theorem card_reducedFormJValues_le (D : ℤ) :
    (reducedFormJValues D).card ≤ (enumPrimitiveReducedForms D).card := by
  classical
  unfold reducedFormJValues
  calc
    _ ≤ (enumPrimitiveReducedForms D).attach.card := Finset.card_image_le
    _ = _ := Finset.card_attach

/-- Every upper-half-plane root of a primitive positive-leading integral
quadratic has the same j-value as an enumerated reduced form of its discriminant. -/
theorem jInvariant_mem_reducedFormJValues {D : ℤ} (τ : UpperHalfPlane)
    (a b c : ℤ) (ha : 0 < a)
    (hprim : Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1)
    (hD : b ^ 2 - 4 * a * c = D)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + c = 0) :
    ModularForm.jInvariant τ ∈ reducedFormJValues D := by
  classical
  let Q : BinaryQuadraticForm := ⟨a, b, c⟩
  have hpos : Q.IsPositiveDefinite :=
    ⟨ha, quadratic_discriminant_neg_of_upperHalfPlane_root τ (ne_of_gt ha) hτ⟩
  have hprimQ : Q.IsPrimitive := by
    change Int.gcd a (Int.gcd b c : ℤ) = 1
    simpa only [Int.gcd_def, Int.natAbs_natCast, ← Nat.gcd_assoc] using hprim
  have hdisc : Q.HasDiscriminant D := hD
  have hτQ : τ = tauOfForm Q hpos := eq_tauOfForm_of_root Q hpos τ hτ
  let R := reduceForm Q hpos
  have hRmem : R ∈ enumPrimitiveReducedForms D :=
    reduceForm_mem_enum Q hdisc hprimQ hpos
  have hRpos : R.IsPositiveDefinite := (of_mem_enumPrimitiveReducedForms hRmem).2.1
  obtain ⟨g, hg⟩ := reduceForm_properEquivalent Q hpos
  change transform Q g = R at hg
  have htranspos : (transform Q g).IsPositiveDefinite :=
    isPositiveDefinite_transform Q hpos g
  have htau : tauOfForm R hRpos = g⁻¹ • τ := by
    simpa only [hg, hτQ] using tauOfForm_transform Q hpos g htranspos
  unfold reducedFormJValues
  refine Finset.mem_image.mpr ⟨⟨R, hRmem⟩, Finset.mem_attach _ _, ?_⟩
  change ModularForm.jInvariant (tauOfForm R hRpos) = ModularForm.jInvariant τ
  rw [htau]
  exact ModularForm.jInvariant_smul g⁻¹ τ

end BakerHeegnerStark
