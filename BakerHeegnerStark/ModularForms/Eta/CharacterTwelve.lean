import BakerHeegnerStark.ModularForms.Eta.CharacterFour
import BakerHeegnerStark.ModularForms.Gamma.CharacterThree
/-!
# The Finite Eta-Square Exponent Modulo Twelve

The mod-three and mod-four exponents combine as `4e₃-3e₄` on `SL₂(ℤ/12ℤ)`.
This finite exponent is additive and controls the integral eta-square character.
Reduction of integral special-linear matrices commutes with divisor reduction.
No analytic function or CM field-membership statement is used here.
-/

open scoped MatrixGroups
namespace ModularForm

/-- The finite weight-one eta-square exponent on matrices modulo twelve. -/
def etaExponentTwelveMod (g : SL(2, ZMod 12)) : ZMod 12 :=
  4 * ((gammaExponentThree
    (Matrix.SpecialLinearGroup.map (ZMod.castHom (by decide : 3 ∣ 12) (ZMod 3)) g)).val : ZMod 12) -
  3 * ((etaExponentFour
    (Matrix.SpecialLinearGroup.map (ZMod.castHom (by decide : 4 ∣ 12) (ZMod 4)) g)).val : ZMod 12)

@[simp]
theorem etaExponentTwelveMod_one : etaExponentTwelveMod 1 = 0 := by
  norm_num [etaExponentTwelveMod]

/-- The finite eta-square exponent is additive under matrix multiplication. -/
theorem etaExponentTwelveMod_mul (g h : SL(2, ZMod 12)) :
    etaExponentTwelveMod (g * h) = etaExponentTwelveMod g + etaExponentTwelveMod h := by
  have hcrt : ∀ a b : ZMod 3, ∀ c d : ZMod 4,
      (4 * (((a + b).val : ℕ) : ZMod 12) - 3 * (((c + d).val : ℕ) : ZMod 12)) =
        (4 * (a.val : ZMod 12) - 3 * (c.val : ZMod 12)) +
          (4 * (b.val : ZMod 12) - 3 * (d.val : ZMod 12)) := by decide +kernel
  simpa only [etaExponentTwelveMod, map_mul, gammaExponentThree_mul,
    etaExponentFour_mul] using hcrt _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Reduction of integral special-linear matrices commutes with reduction to a divisor level. -/
theorem specialLinearReduction_comp_of_dvd {N M : ℕ} (hNM : N ∣ M) (g : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.map (ZMod.castHom hNM (ZMod N))
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g) =
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) g := by
  ext i j
  change (ZMod.castHom hNM (ZMod N)) ((g i j : ℤ) : ZMod M) = ((g i j : ℤ) : ZMod N)
  exact map_intCast _ _

end ModularForm
