/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OrthogonalProjection

/-!
# Isometric coordinates for an orthogonal projection

An orthogonal projection on an arbitrary finite coordinate space is the
range projection of a rectangular isometry. The result includes the zero
projection and the empty ambient coordinate space. It is obtained by
transporting the existing finite-dimensional construction along a finite
coordinate equivalence.

This is the auxiliary coordinate construction for the symmetric restrictions
in the area-law manuscript, `07-comparators.tex`, lines 80–110 and 370–381,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix

/-- An orthogonal projection on any finite complex coordinate space is the
range projection of an isometry from a finite coordinate space, including
zero-dimensional cases. Auxiliary to the restricted operators in the
area-law manuscript, `07-comparators.tex`, lines 80–110 and 370–381. -/
theorem IsStarProjection.exists_matrix_range_isometry
    {m : Type*} [Fintype m] {P : Matrix m m ℂ} (hP : IsStarProjection P) :
    ∃ (n : ℕ) (Z : Matrix m (Fin n) ℂ), Zᴴ * Z = 1 ∧ Z * Zᴴ = P := by
  classical
  have hFin : IsOrthogonalProjection
      (P.submatrix (Fintype.equivFin m).symm (Fintype.equivFin m).symm) :=
    ⟨hP.isSelfAdjoint.isHermitian.submatrix _,
      (hP.isIdempotentElem.map (Matrix.reindexRingEquiv ℂ (Fintype.equivFin m))).eq⟩
  obtain ⟨n, V, hV, hVV⟩ := hFin.exists_range_isometry
  refine ⟨n, V.submatrix (Fintype.equivFin m) id, ?_, ?_⟩
  case refine_2 =>
    simpa only [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv V Vᴴ (Fintype.equivFin m)
        (Equiv.refl (Fin n)) (Fintype.equivFin m),
      Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] using
      congrArg (fun A : Matrix (Fin (Fintype.card m)) (Fin (Fintype.card m)) ℂ ↦
        A.submatrix (Fintype.equivFin m) (Fintype.equivFin m)) hVV
  done
