/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Word

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Block

/-!
# Word evaluation of block-diagonal families

For a family of block-diagonal matrices (`Matrix.blockDiagonal'`, with blocks indexed by a
finite type and an arbitrary finite basis for each block), word evaluation acts blockwise: the
evaluated word is the block diagonal of the evaluated words of the blocks, with an optional
scalar factor on each block.
-/

open scoped Matrix BigOperators

namespace Kraus

variable {ι o : Type*} [Fintype o] [DecidableEq o] {m : o → Type*}
  [∀ k, Fintype (m k)] [∀ k, DecidableEq (m k)]

/-- `evalWord` of a block-diagonal family is the block diagonal of the component
evaluations. -/
lemma evalWord_blockDiagonal'
    (blocks : (k : o) → (ι → Matrix (m k) (m k) ℂ)) :
    ∀ w : List ι,
      evalWord (fun i => Matrix.blockDiagonal' (fun k => blocks k i)) w =
        Matrix.blockDiagonal' (fun k => evalWord (blocks k) w) := by
  intro w; induction w with
  | nil =>
      simp only [evalWord]
      change (1 : Matrix ((k : o) × m k) _ ℂ) = Matrix.blockDiagonal' 1
      simp
  | cons _ _ ih => simp [evalWord, ih]

/-- Variant of `evalWord_blockDiagonal'` with a per-block scalar factor `μ k`.

Each block picks up a factor `(μ k) ^ w.length`. -/
lemma evalWord_blockDiagonal'_smul
    (μ : o → ℂ) (A : (k : o) → (ι → Matrix (m k) (m k) ℂ)) :
    ∀ w : List ι,
      evalWord (fun i => Matrix.blockDiagonal' (fun k => μ k • A k i)) w =
        Matrix.blockDiagonal' (fun k => (μ k) ^ w.length • evalWord (A k) w) := by
  intro w; induction w with
  | nil =>
      simp only [List.length_nil, pow_zero, one_smul]
      change (1 : Matrix ((k : o) × m k) _ ℂ) = Matrix.blockDiagonal' 1
      simp
  | cons i w ih =>
      simp only [List.length_cons, pow_succ', evalWord, ih]
      rw [show Matrix.blockDiagonal' (fun k => μ k • A k i) *
              Matrix.blockDiagonal' (fun k => (μ k) ^ w.length • evalWord (A k) w) =
            Matrix.blockDiagonal'
              (fun k => (μ k • A k i) * ((μ k) ^ w.length • evalWord (A k) w)) from by
        simpa using (Matrix.blockDiagonal'_mul (M := fun k => μ k • A k i)
          (N := fun k => (μ k) ^ w.length • evalWord (A k) w)).symm]
      simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, mul_comm]

end Kraus
