/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Module.Torsion.Basic

namespace AddEquiv

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- An additive isomorphism restricts to the corresponding integer-torsion subgroups. -/
def torsionByEquiv (e : A ≃+ B) (n : ℤ) :
    AddSubgroup.torsionBy A n ≃+ AddSubgroup.torsionBy B n where
  toFun P := ⟨e P, by
    have h : n • (P : A) = 0 := P.property
    change n • e P = 0
    rw [← map_zsmul, h, map_zero]⟩
  invFun Q := ⟨e.symm Q, by
    have h : n • (Q : B) = 0 := Q.property
    change n • e.symm Q = 0
    rw [← map_zsmul, h, map_zero]⟩
  left_inv P := Subtype.ext (e.symm_apply_apply P)
  right_inv Q := Subtype.ext (e.apply_symm_apply Q)
  map_add' P Q := Subtype.ext (e.map_add P Q)

@[simp]
theorem torsionByEquiv_val (e : A ≃+ B) (n : ℤ) (P : AddSubgroup.torsionBy A n) :
    (e.torsionByEquiv n P : B) = e P := rfl

end AddEquiv
