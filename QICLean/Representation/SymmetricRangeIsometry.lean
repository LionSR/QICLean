/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OrthogonalProjection
import QICLean.Representation.SymmetricProjection

/-!
# Isometric coordinates for a finite permutation-invariant subspace

The invariant subspace of a finite permutation representation has an
isometric coordinate representation whose range projection is the actual
group average. The coordinate set may be empty.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, 05-replicas.tex, lines 15–20, and 07-comparators.tex,
  lines 427–439, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.

The finite-group statement is auxiliary to the simultaneous symmetric
subspaces in the manuscript and permits an arbitrary finite site family.
-/

noncomputable section
open Matrix
open scoped Matrix

namespace PermutationRepresentation

/-- An actual finite permutation-group average is the range projection of a
rectangular isometry. Auxiliary to OpenAI's area-law manuscript,
05-replicas.tex, lines 15–20, and 07-comparators.tex, lines 427–439,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Empty coordinate sets and zero range dimensions are included. -/
theorem exists_symProj_isometry
    {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    (φ : G →* Equiv.Perm X) :
    ∃ (n : ℕ) (J : Matrix X (Fin n) ℂ),
      Jᴴ * J = 1 ∧ J * Jᴴ = symProj φ := by
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  have hS := isStarProjection_symProj φ
  have hP : IsOrthogonalProjection ((symProj φ).submatrix e.symm e.symm) :=
    ⟨hS.isSelfAdjoint.isHermitian.submatrix e.symm, by
      rw [Matrix.submatrix_mul_equiv, hS.isIdempotentElem.eq]⟩
  obtain ⟨n, V, hV, hVS⟩ := hP.exists_range_isometry
  refine ⟨n, V.submatrix e (Equiv.refl (Fin n)), ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hV,
      Matrix.submatrix_one_equiv]
  · simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hVS,
      Matrix.submatrix_submatrix, Function.comp_def, Equiv.symm_apply_apply]
    rfl

end PermutationRepresentation
