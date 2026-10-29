/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticCurves.CyclicIsogeny.Basic
import BakerHeegnerStark.LinearAlgebra.Matrix.CyclicLines
import BakerHeegnerStark.EllipticCurves.JInvariant.Galois

/-!
# Residue-coordinate action on actual cyclic isogeny kernels

The finite rectangular kernels are the specified coordinates of the actual
j-model kernels. At levels three and eight they are precisely the primitive
cyclic lines. Matrix relabeling therefore gives an actual permutation of the
Hermite labels, with scalar projective kernel, and identifies the neighboring
j-value under the genuine coefficient Galois representation.
-/

open scoped Matrix MatrixGroups IntermediateField

namespace BakerHeegnerStark

/-- The rectangular kernel in the fixed ordered division-point coordinates. -/
def cyclicResidueKernel (N : ℕ) (t : ℕ × ℕ × ℕ) : Finset (Fin 2 → ZMod N) :=
  ((Finset.range t.1) ×ˢ (Finset.range t.2.2)).image fun p =>
    ![((t.2.2 * p.1 + t.2.1 * p.2 : ℕ) : ZMod N), ((t.1 * p.2 : ℕ) : ZMod N)]

/-- These are coordinates of the entire actual kernel, not an auxiliary subgroup. -/
theorem cyclicIsogenyKernel_eq_coordinates_image [DecidableEq ℂ]
    {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicSublatticeTriples N) (τ : UpperHalfPlane) :
    cyclicIsogenyKernel t τ = (cyclicResidueKernel N t).image
      (fun v => (jInvariantCurveTorsionCoordinatesEquiv τ N hN v :
        ((jInvariantCurve τ).baseChange ℂ).toAffine.Point)) := by
  classical
  simp only [cyclicIsogenyKernel, cyclicIsogenyRepresentatives, cyclicResidueKernel,
    Finset.image_image]
  congr 1
  funext p
  exact (cyclicIsogenyRepresentative_coordinates hN ht τ p.1 p.2).symm

private def residueLine (N : ℕ) [NeZero N] (v : Fin 2 → ZMod N) :
    Finset (Fin 2 → ZMod N) :=
  Finset.univ.image fun c : ZMod N => c • v

private def residuePrimitive (N : ℕ) (v : Fin 2 → ZMod N) : Prop :=
  ∀ c : ZMod N, c • v = 0 → c = 0

private instance (N : ℕ) [NeZero N] (v : Fin 2 → ZMod N) :
    Decidable (residuePrimitive N v) :=
  inferInstanceAs (Decidable (∀ c : ZMod N, c • v = 0 → c = 0))

private def residueGenerator (N : ℕ) (t : ℕ × ℕ × ℕ) : Fin 2 → ZMod N :=
  if t.2.2 = 1 then ![1, 0] else ![(t.2.1 : ZMod N), (t.1 : ZMod N)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem residueKernel_three_generators :
    ∀ t ∈ cyclicSublatticeTriples 3,
      cyclicResidueKernel 3 t = residueLine 3 (residueGenerator 3 t) ∧
        residuePrimitive 3 (residueGenerator 3 t) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem residueKernel_eight_generators :
    ∀ t ∈ cyclicSublatticeTriples 8,
      cyclicResidueKernel 8 t = residueLine 8 (residueGenerator 8 t) ∧
        residuePrimitive 8 (residueGenerator 8 t) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem residueKernel_three_classification :
    ∀ v : Fin 2 → ZMod 3, residuePrimitive 3 v →
      ∃ t ∈ cyclicSublatticeTriples 3, cyclicResidueKernel 3 t = residueLine 3 v := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem residueKernel_eight_classification :
    ∀ v : Fin 2 → ZMod 8, residuePrimitive 8 v →
      ∃ t ∈ cyclicSublatticeTriples 8, cyclicResidueKernel 8 t = residueLine 8 v := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem residueKernel_three_injective :
    ∀ t ∈ cyclicSublatticeTriples 3, ∀ u ∈ cyclicSublatticeTriples 3,
      cyclicResidueKernel 3 t = cyclicResidueKernel 3 u → t = u := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem residueKernel_eight_injective :
    ∀ t ∈ cyclicSublatticeTriples 8, ∀ u ∈ cyclicSublatticeTriples 8,
      cyclicResidueKernel 8 t = cyclicResidueKernel 8 u → t = u := by
  decide

private theorem residue_mulVec_injective {N : ℕ} (A : GL (Fin 2) (ZMod N)) :
    Function.Injective (A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec := by
  intro v w h
  have hi : ((A⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *
      (A : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 :=
    congrArg (fun B : GL (Fin 2) (ZMod N) =>
      (B : Matrix (Fin 2) (Fin 2) (ZMod N))) (inv_mul_cancel A)
  have hh := congrArg
    ((A⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec h
  simpa only [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec] using hh

private theorem residuePrimitive_mulVec {N : ℕ} (A : GL (Fin 2) (ZMod N))
    {v : Fin 2 → ZMod N} (hv : residuePrimitive N v) :
    residuePrimitive N ((A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v) := by
  intro c hc
  apply hv c
  apply residue_mulVec_injective A
  rw [Matrix.mulVec_smul, hc, Matrix.mulVec_zero]

private theorem residueLine_image {N : ℕ} [NeZero N]
    (A : GL (Fin 2) (ZMod N)) (v : Fin 2 → ZMod N) :
    (residueLine N v).image (A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec =
      residueLine N ((A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v) := by
  simp only [residueLine, Finset.image_image, Function.comp_def, Matrix.mulVec_smul]

/-- At levels three and eight the actual rectangular kernels have distinct labels. -/
theorem cyclicResidueKernel_injective {N : ℕ} (hN : N = 3 ∨ N = 8) :
    Function.Injective (fun t : {t // t ∈ cyclicSublatticeTriples N} =>
      cyclicResidueKernel N t.val) := by
  intro t u h
  apply Subtype.ext
  rcases hN with rfl | rfl
  · exact residueKernel_three_injective t.val t.property u.val u.property h
  · exact residueKernel_eight_injective t.val t.property u.val u.property h

/-- Every invertible residue matrix relabels the entire actual kernel uniquely.
Only the primitive vectors, not the general linear group, are finitely classified. -/
theorem cyclicResidueKernel_existsUnique {N : ℕ} (hN : N = 3 ∨ N = 8)
    (A : GL (Fin 2) (ZMod N)) (t : {t // t ∈ cyclicSublatticeTriples N}) :
    ∃! u : {t // t ∈ cyclicSublatticeTriples N},
      (cyclicResidueKernel N t.val).image
        (A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec =
          cyclicResidueKernel N u.val := by
  have : NeZero N := ⟨by rcases hN with rfl | rfl <;> decide⟩
  have hg : cyclicResidueKernel N t.val = residueLine N (residueGenerator N t.val) ∧
      residuePrimitive N (residueGenerator N t.val) := by
    rcases hN with rfl | rfl
    · exact residueKernel_three_generators t.val t.property
    · exact residueKernel_eight_generators t.val t.property
  have hp := residuePrimitive_mulVec A hg.2
  obtain ⟨u, hu, he⟩ : ∃ u ∈ cyclicSublatticeTriples N,
      cyclicResidueKernel N u =
        residueLine N ((A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec
          (residueGenerator N t.val)) := by
    rcases hN with rfl | rfl
    · exact residueKernel_three_classification _ hp
    · exact residueKernel_eight_classification _ hp
  have heq : (cyclicResidueKernel N t.val).image
      (A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec = cyclicResidueKernel N u := by
    rw [hg.1, residueLine_image, he]
  refine ⟨⟨u, hu⟩, heq, ?_⟩
  intro v hv
  exact cyclicResidueKernel_injective hN (hv.symm.trans heq)

/-- The specified label of the transformed rectangular kernel. -/
noncomputable def cyclicKernelRelabel {N : ℕ} (hN : N = 3 ∨ N = 8)
    (A : GL (Fin 2) (ZMod N)) (t : {t // t ∈ cyclicSublatticeTriples N}) :
    {t // t ∈ cyclicSublatticeTriples N} :=
  Classical.choose (cyclicResidueKernel_existsUnique hN A t)

/-- The relabeling is specified by equality of the full coordinate kernels. -/
theorem cyclicKernelRelabel_spec {N : ℕ} (hN : N = 3 ∨ N = 8)
    (A : GL (Fin 2) (ZMod N)) (t : {t // t ∈ cyclicSublatticeTriples N}) :
    (cyclicResidueKernel N t.val).image
      (A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec =
        cyclicResidueKernel N (cyclicKernelRelabel hN A t).val :=
  (Classical.choose_spec (cyclicResidueKernel_existsUnique hN A t)).1

@[simp]
theorem cyclicKernelRelabel_one {N : ℕ} (hN : N = 3 ∨ N = 8)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    cyclicKernelRelabel hN 1 t = t := by
  apply cyclicResidueKernel_injective hN
  have hi : (1 : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec = id :=
    funext Matrix.one_mulVec
  simpa only [Matrix.GeneralLinearGroup.coe_one, hi, Finset.image_id] using
    (cyclicKernelRelabel_spec hN 1 t).symm

/-- Matrix multiplication acts in its actual left-action order. -/
theorem cyclicKernelRelabel_mul {N : ℕ} (hN : N = 3 ∨ N = 8)
    (A B : GL (Fin 2) (ZMod N)) (t : {t // t ∈ cyclicSublatticeTriples N}) :
    cyclicKernelRelabel hN (A * B) t =
      cyclicKernelRelabel hN A (cyclicKernelRelabel hN B t) := by
  apply cyclicResidueKernel_injective hN
  change cyclicResidueKernel N (cyclicKernelRelabel hN (A * B) t).val =
    cyclicResidueKernel N (cyclicKernelRelabel hN A (cyclicKernelRelabel hN B t)).val
  rw [← cyclicKernelRelabel_spec hN (A * B) t,
    ← cyclicKernelRelabel_spec hN A (cyclicKernelRelabel hN B t),
    ← cyclicKernelRelabel_spec hN B t, Finset.image_image]
  congr 1
  funext v
  exact (Matrix.mulVec_mulVec v _ _).symm

/-- The true permutation of `C(N)` induced by an arbitrary invertible matrix. -/
noncomputable def cyclicKernelPerm {N : ℕ} (hN : N = 3 ∨ N = 8)
    (A : GL (Fin 2) (ZMod N)) : Equiv.Perm {t // t ∈ cyclicSublatticeTriples N} where
  toFun := cyclicKernelRelabel hN A
  invFun := cyclicKernelRelabel hN A⁻¹
  left_inv t := by rw [← cyclicKernelRelabel_mul, inv_mul_cancel, cyclicKernelRelabel_one]
  right_inv t := by rw [← cyclicKernelRelabel_mul, mul_inv_cancel, cyclicKernelRelabel_one]

/-- The full general linear group acts on the actual cyclic-kernel labels. -/
noncomputable def cyclicKernelAction {N : ℕ} (hN : N = 3 ∨ N = 8) :
    GL (Fin 2) (ZMod N) →* Equiv.Perm {t // t ∈ cyclicSublatticeTriples N} where
  toFun := cyclicKernelPerm hN
  map_one' := Equiv.ext (cyclicKernelRelabel_one hN)
  map_mul' A B := Equiv.ext (cyclicKernelRelabel_mul hN A B)

private def residueTestTriple (N : ℕ) (i : Fin 3) : ℕ × ℕ × ℕ :=
  ![(N, 0, 1), (1, 0, N), (1, 1, N)] i

private def residueTestVector (N : ℕ) (i : Fin 3) : Fin 2 → ZMod N :=
  ![![1, 0], ![0, 1], ![1, 1]] i

set_option maxRecDepth 100000 in
private theorem residue_three_test_lines :
    ∀ i : Fin 3, residueTestTriple 3 i ∈ cyclicSublatticeTriples 3 ∧
      cyclicResidueKernel 3 (residueTestTriple 3 i) = residueLine 3 (residueTestVector 3 i) := by
  decide

set_option maxRecDepth 100000 in
private theorem residue_eight_test_lines :
    ∀ i : Fin 3, residueTestTriple 8 i ∈ cyclicSublatticeTriples 8 ∧
      cyclicResidueKernel 8 (residueTestTriple 8 i) = residueLine 8 (residueTestVector 8 i) := by
  decide

set_option maxRecDepth 100000 in
private theorem residue_test_lines {N : ℕ} [NeZero N] (hN : N = 3 ∨ N = 8) :
    ∀ i : Fin 3, residueTestTriple N i ∈ cyclicSublatticeTriples N ∧
      cyclicResidueKernel N (residueTestTriple N i) = residueLine N (residueTestVector N i) := by
  rcases hN with rfl | rfl
  · exact residue_three_test_lines
  · exact residue_eight_test_lines

private theorem residueLine_mem_span {N : ℕ} [NeZero N]
    {v w : Fin 2 → ZMod N} (h : w ∈ residueLine N v) :
    w ∈ Submodule.span (ZMod N) {v} := by
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp h
  exact Submodule.mem_span_singleton.mpr ⟨c, hc⟩

/-- Equal kernel permutations determine the invertible matrix up to a unit scalar.
The scalar-kernel argument is the existing three-line theorem over arbitrary rings. -/
theorem cyclicKernelPerm_eq_imp_unit_smul {N : ℕ} (hN : N = 3 ∨ N = 8)
    (A B : GL (Fin 2) (ZMod N)) (h : cyclicKernelPerm hN A = cyclicKernelPerm hN B) :
    ∃ u : (ZMod N)ˣ, (A : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      (u : ZMod N) • (B : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  have : NeZero N := ⟨by rcases hN with rfl | rfl <;> decide⟩
  have hab : cyclicKernelAction hN A = cyclicKernelAction hN B := h
  have hr : cyclicKernelAction hN (B⁻¹ * A) = 1 := by
    rw [map_mul, map_inv, hab, inv_mul_cancel]
  have hl (i : Fin 3) :
      ((B⁻¹ * A : GL (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec (residueTestVector N i) ∈
          Submodule.span (ZMod N) {residueTestVector N i} := by
    obtain ⟨ht, he⟩ := residue_test_lines hN i
    let t : {t // t ∈ cyclicSublatticeTriples N} := ⟨residueTestTriple N i, ht⟩
    have hv : residueTestVector N i ∈ cyclicResidueKernel N t.val := by
      rw [show t.val = residueTestTriple N i from rfl, he]
      exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, one_smul _ _⟩
    have hp : cyclicKernelRelabel hN (B⁻¹ * A) t = t :=
      congrArg (fun p : Equiv.Perm {t // t ∈ cyclicSublatticeTriples N} => p t) hr
    have hm : ((B⁻¹ * A : GL (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec (residueTestVector N i) ∈
          (cyclicResidueKernel N t.val).image
            ((B⁻¹ * A : GL (Fin 2) (ZMod N)) :
              Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec :=
      Finset.mem_image.mpr ⟨residueTestVector N i, hv, rfl⟩
    rw [cyclicKernelRelabel_spec hN (B⁻¹ * A) t, hp] at hm
    apply residueLine_mem_span
    simpa only [show t.val = residueTestTriple N i from rfl, he] using hm
  exact generalLinearGroup_eq_unit_smul_of_inv_mul_preserves_three_lines A B
    (hl 0) (hl 1) (hl 2)

/-- The group action is characterized by the complete residue kernels. -/
theorem cyclicKernelAction_spec {N : ℕ} (hN : N = 3 ∨ N = 8)
    (A : GL (Fin 2) (ZMod N)) (t : {t // t ∈ cyclicSublatticeTriples N}) :
    (cyclicResidueKernel N t.val).image
      (A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec =
        cyclicResidueKernel N (cyclicKernelAction hN A t).val :=
  cyclicKernelRelabel_spec hN A t

private theorem cyclicKernelLevel_pos {N : ℕ} (hN : N = 3 ∨ N = 8) : 0 < N := by
  rcases hN with rfl | rfl <;> decide

/-- The specified permutation representation of actual coefficient automorphisms.
It is the composite of the genuine j-model torsion matrix and the kernel action. -/
noncomputable def cyclicKernelGaloisAction [DecidableEq ℂ] {N : ℕ}
    (hN : N = 3 ∨ N = 8) (τ : UpperHalfPlane) :
    (ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ) →*
      Equiv.Perm {t // t ∈ cyclicSublatticeTriples N} :=
  (cyclicKernelAction hN).comp
    (jInvariantCurveTorsionGaloisMatrix τ N (cyclicKernelLevel_pos hN))

/-- The label is determined by the actual Galois matrix in the fixed coordinates. -/
theorem cyclicKernelGaloisAction_apply [DecidableEq ℂ] {N : ℕ}
    (hN : N = 3 ∨ N = 8) (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    cyclicKernelGaloisAction hN τ σ t =
      cyclicKernelAction hN
        (jInvariantCurveTorsionGaloisMatrix τ N (cyclicKernelLevel_pos hN) σ) t := rfl

/-- Actual coefficient conjugation carries the entire isogeny kernel to the
kernel specified by its true torsion matrix, at either level three or eight. -/
theorem cyclicIsogenyKernel_galois [DecidableEq ℂ] {N : ℕ}
    (hN : N = 3 ∨ N = 8) (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    (cyclicIsogenyKernel t.val τ).image
      (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd =
        cyclicIsogenyKernel (cyclicKernelGaloisAction hN τ σ t).val τ := by
  classical
  let hpos := cyclicKernelLevel_pos hN
  let ρ := jInvariantCurveTorsionGaloisMatrix τ N hpos σ
  change (cyclicIsogenyKernel t.val τ).image
    (weierstrassPointGaloisAut (jInvariantCurve τ).toAffine σ).toAdd =
      cyclicIsogenyKernel (cyclicKernelRelabel hN ρ t).val τ
  rw [cyclicIsogenyKernel_eq_coordinates_image hpos t.property τ,
    cyclicIsogenyKernel_eq_coordinates_image hpos
      (cyclicKernelRelabel hN ρ t).property τ,
    ← cyclicKernelRelabel_spec hN ρ t, Finset.image_image, Finset.image_image]
  congr 1
  funext v
  have hv :
      jInvariantCurveTorsionCoordinatesEquiv τ N hpos
          ((ρ : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v) =
        (weierstrassTorsionGaloisAut (jInvariantCurve τ).toAffine N σ).toAdd
          (jInvariantCurveTorsionCoordinatesEquiv τ N hpos v) := by
    rw [jInvariantCurveTorsionGaloisMatrix_mulVec, AddEquiv.apply_symm_apply]
  exact (congrArg Subtype.val hv).symm

/-- The true torsion representation specifies coefficient conjugation of every
cyclic neighbor j-value. No CM, class-number, or continuity hypothesis is used. -/
theorem jInvariant_cyclicSublatticePoint_galois [DecidableEq ℂ] {N : ℕ}
    (hN : N = 3 ∨ N = 8) (τ : UpperHalfPlane)
    (σ : ℂ ≃ₐ[ℚ⟮ModularForm.jInvariant τ⟯] ℂ)
    (t : {t // t ∈ cyclicSublatticeTriples N}) :
    σ (ModularForm.jInvariant (cyclicSublatticePoint t.val τ)) =
      ModularForm.jInvariant
        (cyclicSublatticePoint (cyclicKernelGaloisAction hN τ σ t).val τ) := by
  rw [← cyclicIsogenyKernel_jInvariant (cyclicKernelLevel_pos hN) t.property τ,
    jInvariantKernelJ_galois, cyclicIsogenyKernel_galois hN τ σ t,
    cyclicIsogenyKernel_jInvariant (cyclicKernelLevel_pos hN)
      (cyclicKernelGaloisAction hN τ σ t).property τ]

end BakerHeegnerStark
