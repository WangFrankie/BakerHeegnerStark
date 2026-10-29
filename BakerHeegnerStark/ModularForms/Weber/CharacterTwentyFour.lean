import BakerHeegnerStark.ModularForms.Eta.CharacterTwelve
/-!
# Finite Weber-Square Multipliers at Level Twenty-Four

Canonical integer representatives define the integral half-period conjugate
modulo twelve. The difference of its eta exponent and the original exponent
is the finite Weber-square multiplier exponent.

A CM unit matrix is normalized to determinant one by an inverse of its norm.
For parameter residues eleven and nineteen modulo twenty-four, every such
matrix has zero Weber exponent. All finite cases are checked by the kernel;
these are residue classes, not a table of class-number-one primes.
No arithmetic statement about CM evaluations is assumed or proved here.
-/

open scoped MatrixGroups
namespace ModularForm

/-- The integer numerator of the half-integral upper-right entry, using canonical residues. -/
def weberThetaNumeratorTwentyFour (g : SL(2, ZMod 24)) : ℤ :=
  ((g 0 1).val : ℤ) + ((g 1 1).val : ℤ) - ((g 0 0).val : ℤ) - ((g 1 0).val : ℤ)

private theorem weber_reduce_twentyFour_twelve_val (x : ZMod 24) :
    ZMod.castHom (by decide : 12 ∣ 24) (ZMod 12) x = (x.val : ZMod 12) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The half-period conjugate reduced modulo twelve on the theta stabilizer. -/
def weberThetaConjugateTwelve (g : SL(2, ZMod 24))
    (hg : Even (weberThetaNumeratorTwentyFour g)) : SL(2, ZMod 12) :=
  ⟨!![((g 0 0).val : ZMod 12) + ((g 1 0).val : ZMod 12),
      ((weberThetaNumeratorTwentyFour g / 2 : ℤ) : ZMod 12);
      2 * ((g 1 0).val : ZMod 12), ((g 1 1).val : ZMod 12) - ((g 1 0).val : ZMod 12)], by
    have hdet : ((g 0 0).val : ZMod 12) * ((g 1 1).val : ZMod 12) -
        ((g 0 1).val : ZMod 12) * ((g 1 0).val : ZMod 12) = 1 := by
      simpa only [Matrix.det_fin_two, Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply, Matrix.map_apply, weber_reduce_twentyFour_twelve_val] using
        (Matrix.SpecialLinearGroup.map (ZMod.castHom (by decide : 12 ∣ 24) (ZMod 12)) g).property
    have hhalf : 2 * (weberThetaNumeratorTwentyFour g / 2) = weberThetaNumeratorTwentyFour g := by
      obtain ⟨k, hk⟩ := hg
      omega
    have hhalf12 : (2 : ZMod 12) * ((weberThetaNumeratorTwentyFour g / 2 : ℤ) : ZMod 12) =
        ((g 0 1).val : ZMod 12) + ((g 1 1).val : ZMod 12) -
          ((g 0 0).val : ZMod 12) - ((g 1 0).val : ZMod 12) := by
      simpa [weberThetaNumeratorTwentyFour] using congrArg (Int.castRingHom (ZMod 12)) hhalf
    simp only [Matrix.det_fin_two]
    dsimp
    linear_combination hdet - ((g 1 0).val : ZMod 12) * hhalf12⟩

/-- The finite eta-exponent difference for the actual Weber-square multiplier. -/
def weberExponentTwentyFour (g : SL(2, ZMod 24))
    (hg : Even (weberThetaNumeratorTwentyFour g)) : ZMod 12 :=
  etaExponentTwelveMod (weberThetaConjugateTwelve g hg) -
    etaExponentTwelveMod
      (Matrix.SpecialLinearGroup.map (ZMod.castHom (by decide : 12 ∣ 24) (ZMod 12)) g)

/-- Right normalization of a CM multiplication matrix by an inverse of its norm. -/
def weberCMUnitMatrixTwentyFour (m a b r : ZMod 24)
    (h : (a ^ 2 + m * b ^ 2) * r = 1) : SL(2, ZMod 24) :=
  ⟨!![a, -m * b * r; b, a * r], by
    simp only [Matrix.det_fin_two]
    dsimp
    linear_combination h⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Every relevant normalized CM unit preserves the theta branch modulo two. -/
theorem weberCMUnitMatrixTwentyFour_parity (m a b r : ZMod 24)
    (h : (a ^ 2 + m * b ^ 2) * r = 1) (hm : m = 11 ∨ m = 19) :
    Even (weberThetaNumeratorTwentyFour (weberCMUnitMatrixTwentyFour m a b r h)) := by
  rcases hm with rfl | rfl
  all_goals revert a b r h
  all_goals decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- The finite Weber exponent vanishes on every normalized CM unit in these residue classes. -/
theorem weberExponentTwentyFour_cmUnitMatrix (m a b r : ZMod 24)
    (h : (a ^ 2 + m * b ^ 2) * r = 1) (hm : m = 11 ∨ m = 19) :
    weberExponentTwentyFour (weberCMUnitMatrixTwentyFour m a b r h)
      (weberCMUnitMatrixTwentyFour_parity m a b r h hm) = 0 := by
  rcases hm with rfl | rfl
  all_goals revert a b r h
  all_goals decide +kernel

end ModularForm
