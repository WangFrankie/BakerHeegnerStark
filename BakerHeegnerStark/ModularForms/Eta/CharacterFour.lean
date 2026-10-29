import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
/-!
# The Quartic Part of the Eta-Square Character

The additive exponent on `SL₂(ℤ/4ℤ)` takes both `S` and `T` to one.
For odd `c` it is `c(a+d-3)`; for even `c` it is `ac+bd+3d-3`.
Together with the existing mod-three exponent, `4e₃-3e₄` reconstructs the
weight-one eta-square exponent modulo twelve. The group law is kernel checked.
This file states no CM field-membership assertion.
-/

open scoped MatrixGroups
namespace ModularForm

/-- The quartic exponent, normalized by `e(S) = e(T) = 1`. -/
def etaExponentFour (g : SL(2, ZMod 4)) : ZMod 4 :=
  if g 1 0 = 0 ∨ g 1 0 = 2 then
    g 0 0 * g 1 0 + g 0 1 * g 1 1 + 3 * g 1 1 - 3
  else
    g 1 0 * (g 0 0 + g 1 1 - 3)

@[simp]
theorem etaExponentFour_one : etaExponentFour (1 : SL(2, ZMod 4)) = 0 := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- The quartic exponent is additive under matrix multiplication. -/
theorem etaExponentFour_mul (g h : SL(2, ZMod 4)) :
    etaExponentFour (g * h) = etaExponentFour g + etaExponentFour h := by
  revert g h
  decide +kernel

@[simp]
theorem etaExponentFour_S :
    etaExponentFour
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 4)) ModularGroup.S) = 1 := by
  decide

@[simp]
theorem etaExponentFour_T :
    etaExponentFour
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 4)) ModularGroup.T) = 1 := by
  decide

/-- Conjugation by the determinant-minus-one diagonal reflection. -/
def etaReflectionFour (g : SL(2, ZMod 4)) : SL(2, ZMod 4) :=
  ⟨!![g 0 0, -g 0 1; -g 1 0, g 1 1], by
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using g.property
    simpa [Matrix.det_fin_two] using hdet⟩

set_option maxRecDepth 4096 in
@[simp]
theorem etaExponentFour_reflection (g : SL(2, ZMod 4)) :
    etaExponentFour (etaReflectionFour g) = -etaExponentFour g := by
  revert g
  decide +kernel

end ModularForm
