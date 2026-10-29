/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.ComplexMultiplication.Weber.JointOrbit
import BakerHeegnerStark.ModularForms.Weber.Growth
import BakerHeegnerStark.ModularForms.JInvariant.JointPolynomial

/-!
# The actual complex Weber joint polynomial

A single finite product retains the Weber branch value and a weighted tuple of
all actual level-three/eight neighboring j-values. Its two scalar coefficient
indices are holomorphic, modular invariant, and bounded by `j ^ (8 * d)`,
where `d` is the actual joint orbit cardinality. Consequently the full formal
auxiliary-variable product is a trivariate complex polynomial in `j`, with
innermost degree at most `8 * d`. No rationality or CM-evaluation statement is
used or asserted.
-/

open UpperHalfPlane Filter Asymptotics Polynomial BakerHeegnerStark
open scoped Topology Manifold MatrixGroups

noncomputable section
namespace ModularForm

/-- The actual joint root product, with a formal auxiliary variable separating
its two coordinates. The outer variable records the roots. -/
def weberJointPolynomial (a : ℕ) (τ : UpperHalfPlane) : ℂ[X][X] :=
  jointOrbitPolynomial
    (fun p : weberJointIndex => (weberJointBranch p : UpperHalfPlane → ℂ) τ)
    (fun p : weberJointIndex => cyclicNeighborWeighted a (weberJointMatrix p) τ)

/-- The actual joint product is monic, with repeated pairs retained. -/
theorem monic_weberJointPolynomial (a : ℕ) (τ : UpperHalfPlane) :
    (weberJointPolynomial a τ).Monic :=
  monic_jointOrbitPolynomial _ _

/-- Its exact outer degree is the cardinality of the actual finite joint index. -/
theorem natDegree_weberJointPolynomial (a : ℕ) (τ : UpperHalfPlane) :
    (weberJointPolynomial a τ).natDegree = Fintype.card weberJointIndex :=
  natDegree_jointOrbitPolynomial _ _

/-- The same permutation reindexes both coordinates, so the full formal joint
product is invariant under every integral modular substitution. -/
theorem weberJointPolynomial_smul (a : ℕ) (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    weberJointPolynomial a (g • τ) = weberJointPolynomial a τ := by
  obtain ⟨e, he⟩ := exists_weberJoint_modular_reindex g
  have hv : (fun p : weberJointIndex =>
      (weberJointBranch p : UpperHalfPlane → ℂ) (g • τ)) =
      (fun p : weberJointIndex => (weberJointBranch p : UpperHalfPlane → ℂ) τ) ∘ e := by
    funext p
    exact (he p).1 τ
  have hw : (fun p : weberJointIndex => cyclicNeighborWeighted a (weberJointMatrix p) (g • τ)) =
      (fun p : weberJointIndex => cyclicNeighborWeighted a (weberJointMatrix p) τ) ∘ e := by
    funext p
    unfold cyclicNeighborWeighted
    rw [(he p).2.1 τ]
    rfl
  unfold weberJointPolynomial
  rw [hv, hw]
  exact jointOrbitPolynomial_reindex e
    (fun p : weberJointIndex => (weberJointBranch p : UpperHalfPlane → ℂ) τ)
    (fun p : weberJointIndex => cyclicNeighborWeighted a (weberJointMatrix p) τ)

private theorem mdifferentiable_neighborRoot {N : ℕ} (hN : 0 < N)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    MDiff (fun τ => jInvariant (cyclicSublatticePoint t.val τ)) := by
  have had := ((mem_cyclicSublatticeTriples hN).mp t.property).1
  have ha : 0 < t.val.1 := by
    by_contra h
    have hz : t.val.1 = 0 := by omega
    simp [hz] at had
    omega
  have hd : 0 < t.val.2.2 := by
    by_contra h
    have hz : t.val.2.2 = 0 := by omega
    simp [hz] at had
    omega
  exact mdifferentiable_jInvariant_cyclicSublatticePoint ha hd

/-- Every coordinate of the actual neighboring tuple is holomorphic. -/
theorem mdifferentiable_cyclicNeighborData (A : GL (Fin 2) (ZMod 24))
    (i : cyclicNeighborIndex) : MDiff (fun τ => cyclicNeighborData A τ i) := by
  rcases i with t | t
  · exact mdifferentiable_neighborRoot (by decide : 0 < 3)
      (cyclicNeighborPerm (Or.inl rfl) A t)
  · exact mdifferentiable_neighborRoot (by decide : 0 < 8)
      (cyclicNeighborPerm (Or.inr rfl) A t)

/-- The actual finite weighted neighboring value is holomorphic for every weight. -/
theorem mdifferentiable_cyclicNeighborWeighted (a : ℕ) (A : GL (Fin 2) (ZMod 24)) :
    MDiff (cyclicNeighborWeighted a A) := by
  classical
  have ht (k : Fin (Fintype.card cyclicNeighborIndex)) : MDiff (fun τ =>
      cyclicNeighborData A τ ((Fintype.equivFin cyclicNeighborIndex).symm k) *
        (a : ℂ) ^ k.val) :=
    (mdifferentiable_cyclicNeighborData A _).mul mdifferentiable_const
  convert (MDifferentiable.sum (t := Finset.univ) (fun k _ => ht k)) using 1
  funext τ
  simp only [cyclicNeighborWeighted, Finset.sum_apply]

private theorem isBigO_jInvariant_pow_of_le {m n : ℕ} (hmn : m ≤ n) :
    (fun τ : UpperHalfPlane => jInvariant τ ^ m)
      =O[atImInfty] (fun τ : UpperHalfPlane => jInvariant τ ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_one_le_norm_jInvariant] with τ hτ
  simp only [norm_pow, one_mul]
  exact pow_le_pow_right₀ hτ hmn

/-- The full actual neighboring tuple has the uniform exponent eight. -/
theorem isBigO_cyclicNeighborData_jInvariant (A : GL (Fin 2) (ZMod 24))
    (i : cyclicNeighborIndex) :
    (fun τ => cyclicNeighborData A τ i)
      =O[atImInfty] (fun τ => jInvariant τ ^ 8) := by
  rcases i with t | t
  · exact (isBigO_jInvariant_of_mem_cyclicSublatticeTriples (by decide : 0 < 3)
      (cyclicNeighborPerm (Or.inl rfl) A t).property).trans
        (isBigO_jInvariant_pow_of_le (by decide : 3 ≤ 8))
  · exact isBigO_jInvariant_of_mem_cyclicSublatticeTriples (by decide : 0 < 8)
      (cyclicNeighborPerm (Or.inr rfl) A t).property

/-- Every actual finite weighting is `O(j^8)`; the weight need not separate tuples. -/
theorem isBigO_cyclicNeighborWeighted_jInvariant (a : ℕ)
    (A : GL (Fin 2) (ZMod 24)) : cyclicNeighborWeighted a A
      =O[atImInfty] (fun τ => jInvariant τ ^ 8) := by
  classical
  have ht (k : Fin (Fintype.card cyclicNeighborIndex)) : (fun τ =>
      cyclicNeighborData A τ ((Fintype.equivFin cyclicNeighborIndex).symm k) *
        (a : ℂ) ^ k.val) =O[atImInfty] (fun τ => jInvariant τ ^ 8) := by
    simpa only [mul_comm] using
      (isBigO_cyclicNeighborData_jInvariant A
        ((Fintype.equivFin cyclicNeighborIndex).symm k)).const_mul_left ((a : ℂ) ^ k.val)
  convert (IsBigO.sum (s := Finset.univ) (fun k _ => ht k)) using 1
  funext τ
  simp only [cyclicNeighborWeighted, Finset.sum_apply]

private theorem mdifferentiable_weberJointLinear_coeff (a : ℕ) (p : weberJointIndex)
    (l : ℕ) : MDiff (fun τ => (jointOrbitLinearPolynomial
      ((weberJointBranch p : UpperHalfPlane → ℂ) τ)
      (cyclicNeighborWeighted a (weberJointMatrix p) τ)).coeff l) := by
  cases l with
  | zero =>
      simpa [jointOrbitLinearPolynomial] using mdifferentiable_weberBranchSpace (weberJointBranch p)
  | succ l =>
      cases l with
      | zero =>
          simpa [jointOrbitLinearPolynomial] using mdifferentiable_cyclicNeighborWeighted a (weberJointMatrix p)
      | succ l =>
          simpa [jointOrbitLinearPolynomial] using
            (mdifferentiable_const : MDiff (fun _ : UpperHalfPlane => (0 : ℂ)))

private theorem isBigO_weberJointLinear_coeff (a : ℕ) (p : weberJointIndex)
    (l : ℕ) : (fun τ => (jointOrbitLinearPolynomial
      ((weberJointBranch p : UpperHalfPlane → ℂ) τ)
      (cyclicNeighborWeighted a (weberJointMatrix p) τ)).coeff l)
      =O[atImInfty] (fun τ => jInvariant τ ^ 8) := by
  cases l with
  | zero =>
      have hw : (weberJointBranch p : UpperHalfPlane → ℂ)
          =O[atImInfty] (fun τ => jInvariant τ ^ 1) := by
        simpa only [pow_one] using isBigO_weberBranchSpace_jInvariant (weberJointBranch p)
      simpa [jointOrbitLinearPolynomial] using
        hw.trans (isBigO_jInvariant_pow_of_le (by decide : 1 ≤ 8))
  | succ l =>
      cases l with
      | zero =>
          simpa [jointOrbitLinearPolynomial] using
            isBigO_cyclicNeighborWeighted_jInvariant a (weberJointMatrix p)
      | succ l =>
          simpa [jointOrbitLinearPolynomial] using
            (isBigO_zero _ _ : (fun _ : UpperHalfPlane => (0 : ℂ))
              =O[atImInfty] (fun τ => jInvariant τ ^ 8))

/-- Every scalar coefficient, with both formal polynomial variables retained,
is holomorphic without any analytic hypothesis on the caller. -/
theorem mdifferentiable_weberJointPolynomial_coeff_coeff (a k l : ℕ) :
    MDiff (fun τ => ((weberJointPolynomial a τ).coeff k).coeff l) := by
  classical
  exact mdifferentiable_prod_X_sub_C_coeff_coeff Finset.univ
    (fun p τ => jointOrbitLinearPolynomial
      ((weberJointBranch p : UpperHalfPlane → ℂ) τ)
      (cyclicNeighborWeighted a (weberJointMatrix p) τ))
    (fun p _ l => mdifferentiable_weberJointLinear_coeff a p l) k l

/-- All scalar joint coefficients have the uniform growth exponent required for
finite discriminant regularization. -/
theorem isBigO_weberJointPolynomial_coeff_coeff (a k l : ℕ) :
    (fun τ => ((weberJointPolynomial a τ).coeff k).coeff l)
      =O[atImInfty] (fun τ => jInvariant τ ^ (8 * Fintype.card weberJointIndex)) := by
  classical
  exact isBigO_prod_X_sub_C_coeff_coeff Finset.univ
    (fun p τ => jointOrbitLinearPolynomial
      ((weberJointBranch p : UpperHalfPlane → ℂ) τ)
      (cyclicNeighborWeighted a (weberJointMatrix p) τ)) jInvariant 8
    eventually_one_le_norm_jInvariant
    (fun p _ l => isBigO_weberJointLinear_coeff a p l) k l

/-- Every inner coefficient polynomial has degree bounded by the actual orbit size. -/
theorem natDegree_weberJointPolynomial_coeff_le (a : ℕ) (τ : UpperHalfPlane) (k : ℕ) :
    ((weberJointPolynomial a τ).coeff k).natDegree ≤ Fintype.card weberJointIndex :=
  natDegree_jointOrbitPolynomial_coeff_le _ _ k

/-- The two coefficient indices have finite rectangular support. -/
theorem weberJointPolynomial_coeff_coeff_eq_zero (a : ℕ) (τ : UpperHalfPlane) (k l : ℕ)
    (h : Fintype.card weberJointIndex < k ∨ Fintype.card weberJointIndex < l) :
    ((weberJointPolynomial a τ).coeff k).coeff l = 0 := by
  rcases h with hk | hl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := weberJointPolynomial a τ) (by
      rw [natDegree_weberJointPolynomial]
      exact hk)]
    exact Polynomial.coeff_zero l
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((natDegree_weberJointPolynomial_coeff_le a τ k).trans_lt hl)

/-- The actual full joint product is a complex trivariate polynomial in `j`.
Every innermost coefficient polynomial has degree at most eight times the
actual joint orbit size; neither the auxiliary variable nor either coefficient
index has been specialized away. -/
theorem exists_complex_weberJointPolynomial (a : ℕ) :
    ∃ Φ : ℂ[X][X][X],
      (∀ τ : UpperHalfPlane,
        Φ.map (Polynomial.mapRingHom (Polynomial.evalRingHom (jInvariant τ))) =
          weberJointPolynomial a τ) ∧
      ∀ k l, ((Φ.coeff k).coeff l).natDegree ≤ 8 * Fintype.card weberJointIndex := by
  exact exists_trivariate_polynomial_jInvariant_of_isBigO (weberJointPolynomial a)
    (Fintype.card weberJointIndex) (8 * Fintype.card weberJointIndex)
    (weberJointPolynomial_coeff_coeff_eq_zero a)
    (mdifferentiable_weberJointPolynomial_coeff_coeff a)
    (isBigO_weberJointPolynomial_coeff_coeff a)
    (weberJointPolynomial_smul a)

end ModularForm
