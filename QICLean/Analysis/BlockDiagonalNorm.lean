/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.DependentBlockDiagonal
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Operator norm of a finite dependent block diagonal

The Hilbert-space operator norm is the maximum of the block norms. The
finite supremum in `ℝ≥0` also handles the empty family, whose norm is zero.
This supplies the direct-sum step in Wolf, Chapter 8, lines 1252--1267 of
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {dim : ι → Type*} [∀ i, Fintype (dim i)] [∀ i, DecidableEq (dim i)]

/-- The dependent block-diagonal inclusion as a star algebra homomorphism. -/
noncomputable def blockDiagonal'StarAlgHom :
    (∀ i, Matrix (dim i) (dim i) ℂ) →⋆ₙₐ[ℂ]
      Matrix (Σ i, dim i) (Σ i, dim i) ℂ :=
  { (blockDiagonal'RingHom dim ℂ).toNonUnitalRingHom with
    map_smul' := blockDiagonal'_smul
    map_star' := fun B ↦ (blockDiagonal'_conjTranspose B).symm }

/-- The block-diagonal inclusion preserves the norm of the finite product. -/
theorem l2_opNorm_blockDiagonal' (B : ∀ i, Matrix (dim i) (dim i) ℂ) :
    ‖blockDiagonal' B‖ = ‖B‖ :=
  NonUnitalStarAlgHom.norm_map (blockDiagonal'StarAlgHom (dim := dim))
    blockDiagonal'_injective B

/-- Exact finite maximum formula, with value zero for an empty family. -/
theorem l2_opNNNorm_blockDiagonal' (B : ∀ i, Matrix (dim i) (dim i) ℂ) :
    ‖blockDiagonal' B‖₊ = Finset.univ.sup (fun i ↦ ‖B i‖₊) := by
  have h : ‖blockDiagonal' B‖₊ = ‖B‖₊ := NNReal.eq (l2_opNorm_blockDiagonal' B)
  rw [h, Pi.nnnorm_def]

/-- Every block norm is bounded by the norm of the direct sum. -/
theorem l2_opNorm_block_le_blockDiagonal'
    (B : ∀ i, Matrix (dim i) (dim i) ℂ) (i : ι) :
    ‖B i‖ ≤ ‖blockDiagonal' B‖ := by
  rw [l2_opNorm_blockDiagonal']
  exact norm_le_pi_norm B i

/-- A block attaining all block norms realizes the direct-sum norm. -/
theorem l2_opNorm_blockDiagonal'_eq_of_max
    (B : ∀ i, Matrix (dim i) (dim i) ℂ) (i : ι)
    (h : ∀ j, ‖B j‖ ≤ ‖B i‖) :
    ‖blockDiagonal' B‖ = ‖B i‖ := by
  apply le_antisymm
  · rw [l2_opNorm_blockDiagonal']
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr h
  · exact l2_opNorm_block_le_blockDiagonal' B i

/-- For a nonempty family the finite maximum is attained by an actual block. -/
theorem exists_l2_opNorm_blockDiagonal'_eq [Nonempty ι]
    (B : ∀ i, Matrix (dim i) (dim i) ℂ) : ∃ i, ‖blockDiagonal' B‖ = ‖B i‖ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i ↦ ‖B i‖)
    Finset.univ_nonempty
  exact ⟨i, l2_opNorm_blockDiagonal'_eq_of_max B i (fun j ↦ hi j (Finset.mem_univ j))⟩

/-- An empty family has norm zero; there is no selected maximizing block. -/
theorem l2_opNorm_blockDiagonal'_of_isEmpty [IsEmpty ι]
    (B : ∀ i, Matrix (dim i) (dim i) ℂ) : ‖blockDiagonal' B‖ = 0 := by
  rw [l2_opNorm_blockDiagonal', Pi.norm_def]
  simp

end Matrix
