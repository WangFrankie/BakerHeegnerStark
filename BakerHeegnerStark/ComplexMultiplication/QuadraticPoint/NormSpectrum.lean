/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.NormMinimum

/-!
# Recognition from primitive quadratic norm spectra

The primitive values greater than one determine the coefficient of an odd
canonical norm and distinguish odd canonical norms from even canonical norms.
The unit cases are separated by their small primitive values.
-/

namespace BakerHeegnerStark

/-- The primitive odd norm spectrum above one determines its coefficient. -/
theorem primitiveOddNormValue_spectrum_injective {c d : ℤ} (hc : 1 ≤ c)
    (hd : 1 ≤ d)
    (h : ∀ n : ℤ, 1 < n → (PrimitiveOddNormValue c n ↔ PrimitiveOddNormValue d n)) :
    c = d := by
  by_cases hc1 : c = 1
  · subst c
    by_cases hd1 : d = 1
    · exact hd1.symm
    · have hd2 : 2 ≤ d := by omega
      have hdthree : PrimitiveOddNormValue d 3 :=
        (h 3 (by omega)).mp (primitiveOddNormValue_c_add_two 1)
      have hdle : d ≤ 3 := primitiveOddNormValue_ge hd2 (by omega) hdthree
      have honed : PrimitiveOddNormValue 1 d :=
        (h d (by omega)).mpr (primitiveOddNormValue_c d)
      have hdge : 3 ≤ d := primitiveOddNormValue_one_ge_three (by omega) honed
      have hd3 : d = 3 := by omega
      subst d
      exfalso
      exact not_primitiveOddNormValue_one_five
        ((h 5 (by omega)).mpr (primitiveOddNormValue_c_add_two 3))
  · have hc2 : 2 ≤ c := by omega
    by_cases hd1 : d = 1
    · subst d
      have hcthree : PrimitiveOddNormValue c 3 :=
        (h 3 (by omega)).mpr (primitiveOddNormValue_c_add_two 1)
      have hcle : c ≤ 3 := primitiveOddNormValue_ge hc2 (by omega) hcthree
      have honec : PrimitiveOddNormValue 1 c :=
        (h c (by omega)).mp (primitiveOddNormValue_c c)
      have hcge : 3 ≤ c := primitiveOddNormValue_one_ge_three (by omega) honec
      have hc3 : c = 3 := by omega
      subst c
      exfalso
      exact not_primitiveOddNormValue_one_five
        ((h 5 (by omega)).mp (primitiveOddNormValue_c_add_two 3))
    · have hd2 : 2 ≤ d := by omega
      have hcd : c ≤ d := primitiveOddNormValue_ge hc2 (by omega)
        ((h d (by omega)).mpr (primitiveOddNormValue_c d))
      have hdc : d ≤ c := primitiveOddNormValue_ge hd2 (by omega)
        ((h c (by omega)).mp (primitiveOddNormValue_c c))
      omega

/-- Primitive odd and even norm spectra above one are distinct. -/
theorem primitiveOddEvenNormValue_spectra_ne {c d : ℤ} (hc : 1 ≤ c)
    (hd : 1 ≤ d) :
    ¬ (∀ n : ℤ, 1 < n → (PrimitiveOddNormValue c n ↔ PrimitiveEvenNormValue d n)) := by
  intro h
  by_cases hc1 : c = 1
  · subst c
    by_cases hd1 : d = 1
    · subst d
      exact not_primitiveOddNormValue_one_two
        ((h 2 (by omega)).mpr (primitiveEvenNormValue_c_add_one 1))
    · have hd2 : 2 ≤ d := by omega
      have hdthree : PrimitiveEvenNormValue d 3 :=
        (h 3 (by omega)).mp (primitiveOddNormValue_c_add_two 1)
      have hdle : d ≤ 3 := primitiveEvenNormValue_ge hd2 (by omega) hdthree
      have honed : PrimitiveOddNormValue 1 d :=
        (h d (by omega)).mpr (primitiveEvenNormValue_c d)
      have hdge : 3 ≤ d := primitiveOddNormValue_one_ge_three (by omega) honed
      have hd3 : d = 3 := by omega
      subst d
      exact not_primitiveOddNormValue_one_four
        ((h 4 (by omega)).mpr (primitiveEvenNormValue_c_add_one 3))
  · have hc2 : 2 ≤ c := by omega
    by_cases hd1 : d = 1
    · subst d
      have hctwo : PrimitiveOddNormValue c 2 :=
        (h 2 (by omega)).mpr (primitiveEvenNormValue_c_add_one 1)
      have hcle : c ≤ 2 := primitiveOddNormValue_ge hc2 (by omega) hctwo
      have hc_eq_two : c = 2 := by omega
      subst c
      exact not_primitiveEvenNormValue_one_four
        ((h 4 (by omega)).mp (primitiveOddNormValue_c_add_two 2))
    · have hd2 : 2 ≤ d := by omega
      have hcd : c ≤ d := primitiveOddNormValue_ge hc2 (by omega)
        ((h d (by omega)).mpr (primitiveEvenNormValue_c d))
      have hdc : d ≤ c := primitiveEvenNormValue_ge hd2 (by omega)
        ((h c (by omega)).mp (primitiveOddNormValue_c c))
      have hcd_eq : c = d := by omega
      subst d
      exact not_primitiveOddNormValue_c_add_one hc
        ((h (c + 1) (by omega)).mpr (primitiveEvenNormValue_c_add_one c))

end BakerHeegnerStark
