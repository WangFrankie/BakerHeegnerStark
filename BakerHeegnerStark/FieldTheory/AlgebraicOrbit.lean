/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Algebraicity from finite orbits and descent from fixed elements

A transcendental element of an algebraically closed extension can be
translated by every base-field scalar: extend it to a transcendence basis,
translate one polynomial coordinate, pass to the fraction field, and extend
the resulting automorphism to the algebraic closure.

Over an infinite base field these translates form an infinite orbit.
Consequently a finite orbit forces algebraicity, without assuming the
entire extension is algebraic or Galois over its original base.

In characteristic zero, an element fixed by every base-field automorphism
therefore belongs to the base field. To descend it, work in the actual
relative algebraic closure and extend its automorphisms to the ambient
field by acting on the coefficients of a transcendence basis.
-/

namespace BakerHeegnerStark

private noncomputable def translateCoordinate {ι R : Type*} [CommRing R]
    (i₀ : ι) (a : R) : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R := by
  classical
  let f : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i + if i = i₀ then MvPolynomial.C a else 0)
  let g : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i + if i = i₀ then MvPolynomial.C (-a) else 0)
  have hgf : g.comp f = AlgHom.id R (MvPolynomial ι R) := by
    ext i
    by_cases hi : i = i₀ <;> simp [f, g, hi]
  have hfg : f.comp g = AlgHom.id R (MvPolynomial ι R) := by
    ext i
    by_cases hi : i = i₀ <;> simp [f, g, hi]
  exact
    { __ := f
      invFun := g
      left_inv := fun p => DFunLike.congr_fun hgf p
      right_inv := fun p => DFunLike.congr_fun hfg p }

private theorem translateCoordinate_X_self {ι R : Type*} [CommRing R] (i₀ : ι) (a : R) :
    translateCoordinate i₀ a (MvPolynomial.X i₀) = MvPolynomial.X i₀ + MvPolynomial.C a := by
  classical
  simp [translateCoordinate]

/-- A transcendental element in an algebraically closed field can be translated by
any base-field scalar by an actual base-field automorphism. -/
theorem exists_algEquiv_apply_eq_add_of_transcendental
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    {x : L} (hx : Transcendental K x) (a : K) :
    ∃ σ : L ≃ₐ[K] L, σ x = x + algebraMap K L a := by
  classical
  have hs : AlgebraicIndepOn K id ({x} : Set L) := by
    change AlgebraicIndependent K (fun b : ({x} : Set L) => (b : L))
    exact (algebraicIndependent_singleton_iff (R := K) ⟨x, by simp⟩).mpr hx
  obtain ⟨t, hxt, ht⟩ := exists_isTranscendenceBasis_superset hs
  let v : t → L := fun i => i
  let i₀ : t := ⟨x, hxt (by simp)⟩
  have hv : IsTranscendenceBasis K v := ht
  let B := IntermediateField.adjoin K (Set.range v)
  let e : FractionRing (MvPolynomial t K) ≃ₐ[K] B := hv.1.aevalEquivField
  let f : FractionRing (MvPolynomial t K) ≃ₐ[K] FractionRing (MvPolynomial t K) :=
    IsFractionRing.algEquivOfAlgEquiv (translateCoordinate i₀ a)
  let b : B ≃ₐ[K] B := e.symm.trans (f.trans e)
  let b₀ : B := e (algebraMap (MvPolynomial t K) (FractionRing (MvPolynomial t K))
    (MvPolynomial.X i₀))
  have hb₀ : (b₀ : L) = x := by
    dsimp only [b₀, e]
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    simp only [MvPolynomial.aeval_X, v, i₀]
  have hb : (b b₀ : L) = x + algebraMap K L a := by
    dsimp only [b, b₀, AlgEquiv.trans_apply]
    rw [e.symm_apply_apply]
    dsimp only [f]
    rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    dsimp only [e]
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe,
      translateCoordinate_X_self]
    simp only [map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_C, v, i₀]
  let : IsAlgClosure B L := ⟨inferInstance, hv.isAlgebraic_field⟩
  let r : L ≃+* L := IsAlgClosure.equivOfEquiv L L b.toRingEquiv
  have hfix : ∀ c : K, r (algebraMap K L c) = algebraMap K L c := by
    intro c
    have h := IsAlgClosure.equivOfEquiv_algebraMap L L b.toRingEquiv (algebraMap K B c)
    change r (algebraMap B L (algebraMap K B c)) =
      algebraMap B L (b (algebraMap K B c)) at h
    rw [b.commutes] at h
    exact h
  refine ⟨AlgEquiv.ofRingEquiv (f := r) hfix, ?_⟩
  change r x = x + algebraMap K L a
  have h := IsAlgClosure.equivOfEquiv_algebraMap L L b.toRingEquiv b₀
  change r (b₀ : L) = (b b₀ : L) at h
  simpa only [hb₀, hb] using h

/-- A finite orbit under actual base-field automorphisms forces algebraicity;
the algebraically closed extension need not be algebraic or Galois over its base. -/
theorem isAlgebraic_of_finite_algEquiv_orbit
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K L] [IsAlgClosed L]
    (x : L) (hfinite : (Set.range (fun σ : L ≃ₐ[K] L => σ x)).Finite) :
    IsAlgebraic K x := by
  by_contra hx
  have hsub : Set.range (fun a : K => x + algebraMap K L a) ⊆
      Set.range (fun σ : L ≃ₐ[K] L => σ x) := by
    rintro y ⟨a, rfl⟩
    exact exists_algEquiv_apply_eq_add_of_transcendental hx a
  have hfin := hfinite.subset hsub
  have hinj : Function.Injective (fun a : K => x + algebraMap K L a) := by
    intro a b h
    exact (algebraMap K L).injective (add_left_cancel h)
  exact (Set.infinite_range_of_injective hinj).not_finite hfin

/-- Every base-field automorphism of an intermediate field extends to an
automorphism of an algebraically closed overfield. Neither extension in the
tower is required to be algebraic. -/
theorem exists_algEquiv_extend
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [IsAlgClosed L] (σ : M ≃ₐ[K] M) :
    ∃ τ : L ≃ₐ[K] L,
      ∀ a : M, τ (algebraMap M L a) = algebraMap M L (σ a) := by
  classical
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis M L
  let v : t → L := fun i => i
  have hv : IsTranscendenceBasis M v := ht
  let B := IntermediateField.adjoin M (Set.range v)
  let e : FractionRing (MvPolynomial t M) ≃ₐ[M] B := hv.1.aevalEquivField
  let eK := e.restrictScalars K
  let f : FractionRing (MvPolynomial t M) ≃ₐ[K] FractionRing (MvPolynomial t M) :=
    IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.mapAlgEquiv t σ)
  let b : B ≃ₐ[K] B := eK.symm.trans (f.trans eK)
  have hb (a : M) : b (algebraMap M B a) = algebraMap M B (σ a) := by
    change e (f (e.symm (algebraMap M B a))) = algebraMap M B (σ a)
    rw [← e.commutes, e.symm_apply_apply]
    rw [IsScalarTower.algebraMap_apply M (MvPolynomial t M) (FractionRing (MvPolynomial t M)),
      IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    simp only [MvPolynomial.algebraMap_eq, MvPolynomial.mapAlgEquiv_apply, MvPolynomial.map_C]
    change e (algebraMap (MvPolynomial t M) (FractionRing (MvPolynomial t M))
      (algebraMap M (MvPolynomial t M) (σ a))) = _
    rw [← IsScalarTower.algebraMap_apply M (MvPolynomial t M) (FractionRing (MvPolynomial t M)),
      e.commutes]
  let : IsAlgClosure B L := ⟨inferInstance, hv.isAlgebraic_field⟩
  let r : L ≃+* L := IsAlgClosure.equivOfEquiv L L b.toRingEquiv
  have hr (a : M) : r (algebraMap M L a) = algebraMap M L (σ a) := by
    have h := IsAlgClosure.equivOfEquiv_algebraMap L L b.toRingEquiv (algebraMap M B a)
    change r (algebraMap B L (algebraMap M B a)) =
      algebraMap B L (b (algebraMap M B a)) at h
    rw [hb] at h
    simpa only [← IsScalarTower.algebraMap_apply] using h
  have hfix (a : K) : r (algebraMap K L a) = algebraMap K L a := by
    rw [IsScalarTower.algebraMap_apply K M L, hr, σ.commutes,
      ← IsScalarTower.algebraMap_apply K M L]
  exact ⟨AlgEquiv.ofRingEquiv (f := r) hfix, hr⟩

/-- Over a characteristic-zero field, the elements of an algebraically closed
extension fixed by every base-field automorphism are exactly the elements of the
base field. The ambient extension need not be algebraic or Galois. -/
theorem exists_algebraMap_eq_iff_forall_algEquiv
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (x : L) :
    (∃ a : K, algebraMap K L a = x) ↔ ∀ σ : L ≃ₐ[K] L, σ x = x := by
  constructor
  · rintro ⟨a, rfl⟩ σ
    exact σ.commutes a
  · intro hfix
    have hfinite : (Set.range (fun σ : L ≃ₐ[K] L => σ x)).Finite := by
      apply (Set.finite_singleton x).subset
      rintro y ⟨σ, rfl⟩
      exact Set.mem_singleton_iff.mpr (hfix σ)
    have hx := isAlgebraic_of_finite_algEquiv_orbit x hfinite
    let B := algebraicClosure K L
    let xB : B := ⟨x, mem_algebraicClosure_iff.mpr hx⟩
    let : IsGalois K B := ⟨⟩
    have hB : ∀ σ : B ≃ₐ[K] B, σ xB = xB := by
      intro σ
      obtain ⟨τ, hτ⟩ := exists_algEquiv_extend (L := L) σ
      apply Subtype.val_injective
      calc
        (σ xB : L) = τ (xB : L) := (hτ xB).symm
        _ = (xB : L) := hfix τ
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) xB).mpr hB
    exact ⟨a, congrArg (algebraMap B L) ha⟩

end BakerHeegnerStark
