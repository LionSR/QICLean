/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OrthogonalProjection
import QICLean.Representation.SymmetricProjection

/-!
# An isometric coordinate representation of simultaneous symmetric copies

The simultaneous symmetric subspace of the five factors Q, Y, V, C and R
admits an isometric coordinate representation. Its range projection is the
actual average of the simultaneous copy-permutation operators, with the same
permutation acting on all five factors. The coordinate dimension may be zero.
The middle physical factor Y is retained.

The construction reindexes the projection to a finite coordinate space and
uses its orthonormal eigenvectors with eigenvalue one.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `05-replicas.tex`, lines 15–20: the simultaneous symmetric
  replica space.
* The same paper, `07-comparators.tex`, lines 23, 103–110 and 427–439,
  comparator:defect-mass: the physical factors Q, Y and V, both auxiliary
  factors, and the simultaneous symmetric restriction, at manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped Matrix

namespace TensorPower

/-- There exists a rectangular isometry onto the actual simultaneous symmetric
range of all five factors. Zero copies, empty coordinate factors and a zero
range dimension are included. OpenAI, `05-replicas.tex`, lines 15–20, and
`07-comparators.tex`, lines 427–439. -/
theorem exists_symmetricSubspace_isometry
    (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (k : ℕ) :
    let S := symProj (copyPerm ((f : Fin 5) → ι f) k)
    ∃ (n : ℕ) (J : Matrix (Config k ι) (Fin n) ℂ),
      Jᴴ * J = 1 ∧ J * Jᴴ = S := by
  let e : Config k ι ≃ Fin (Fintype.card (Config k ι)) :=
    Fintype.equivFin (Config k ι)
  have hS := PermutationRepresentation.isStarProjection_symProj
    (copyPerm ((f : Fin 5) → ι f) k)
  have hP : IsOrthogonalProjection
      ((symProj (copyPerm ((f : Fin 5) → ι f) k)).submatrix e.symm e.symm) :=
    ⟨hS.isSelfAdjoint.isHermitian.submatrix e.symm, by
      rw [Matrix.submatrix_mul_equiv, hS.isIdempotentElem.eq]⟩
  obtain ⟨n, V, hV, hVS⟩ := hP.exists_range_isometry
  refine ⟨n, V.submatrix e (Equiv.refl (Fin n)), ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hV,
      Matrix.submatrix_one_equiv]
  · simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hVS,
      Matrix.submatrix_submatrix, Function.comp_def, Equiv.symm_apply_apply]
    rfl

end TensorPower
