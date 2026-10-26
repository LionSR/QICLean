/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.GroupTheory.Perm.Fin
import QICLean.Algebra.PermutationMatrixUnitary

/-!
# A unitary with zero trace pairing against a Hermitian matrix

Every complex Hermitian matrix of dimension at least two has zero trace pairing with some unitary
matrix. In an orthonormal eigenbasis, a cyclic permutation has zero diagonal.
-/

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n]

open scoped Classical in
/-- A complex Hermitian matrix in dimension at least two has zero trace pairing with a unitary
matrix. -/
theorem exists_unitary_trace_mul_eq_zero {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hn : 2 ≤ Fintype.card n) :
    ∃ U : Matrix.unitaryGroup n ℂ, (A * (U : Matrix n n ℂ)).trace = 0 := by
  classical
  let e := Fintype.equivFin n
  let σ : Equiv.Perm n := (e.trans (finRotate (Fintype.card n))).trans e.symm
  have hσ (i : n) : σ i ≠ i := by
    have h := Equiv.Perm.mem_support.mp (show e i ∈ (finRotate (Fintype.card n)).support by
      rw [support_finRotate_of_le hn]
      exact Finset.mem_univ _)
    simpa only [σ, Equiv.trans_apply, ne_eq, Equiv.symm_apply_eq] using h
  let P : Matrix.unitaryGroup n ℂ := ⟨σ.permMatrix ℂ, σ.permMatrix_mem_unitaryGroup⟩
  refine ⟨hA.eigenvectorUnitary * P * star hA.eigenvectorUnitary, ?_⟩
  change (A * ((hA.eigenvectorUnitary : Matrix n n ℂ) * P *
    (star hA.eigenvectorUnitary : Matrix n n ℂ))).trace = 0
  rw [trace_mul_cycle', ← mul_assoc, ← mul_assoc,
    ← Unitary.conjStarAlgAut_star_apply (S := ℂ) hA.eigenvectorUnitary A,
    hA.conjStarAlgAut_star_eigenvectorUnitary]
  simp [Matrix.trace, P, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, hσ]

end Matrix.IsHermitian
