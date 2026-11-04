/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixReindex
import QICLean.Algebra.OperatorBlock
import QICLean.Algebra.SkolemNoetherUnitary
import QICLean.Analysis.CfcConjugation
import QICLean.Channel.TensorMap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Reindexing, its two coefficient orientations, and the migrated consumers. -/

open Matrix

section

variable {m n o : Type*} [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n] [Fintype o] [DecidableEq o]

-- The homomorphism is obtained from the equivalence and evaluates by inverse indices.
example (e : m ≃ n) (X : Matrix m m ℂ) (i j : n) :
    (reindexStarAlgEquiv e).toStarAlgHom X i j = X (e.symm i) (e.symm j) := by
  simp

-- Successive changes of coordinates and inverse cancellation use the bundled API.
example (e : m ≃ n) (f : n ≃ o) :
    ((reindexStarAlgEquiv e).trans (reindexStarAlgEquiv f)).symm =
      reindexStarAlgEquiv (f.symm.trans e.symm) := by
  simp

example (e : m ≃ n) (X : Matrix n n ℂ) :
    reindexStarAlgEquiv e (reindexStarAlgEquiv e.symm X) = X := by
  exact (reindexStarAlgEquiv e).apply_symm_apply X

-- The downstream name remains definitionally equal to the canonical equivalence.
example (e : m ≃ n) : matrixReindexStarAlgEquiv e = reindexStarAlgEquiv e := rfl

end

-- Empty index types are allowed, including an empty unfixed coefficient factor.
example (X : Matrix (Fin 0 × Fin 2) (Fin 0 × Fin 2) ℂ) (i j : Fin 2) :
    bipartiteSlice
        (reindexStarAlgEquiv ((Equiv.refl (Fin 0)).prodCongr (Equiv.swap 0 1)) X) i j =
      bipartiteSlice X ((Equiv.swap 0 1) i) ((Equiv.swap 0 1) j) := by
  simp only [reindexStarAlgEquiv_apply, bipartiteSlice_reindex_prod,
    Equiv.symm_swap, reindex_refl_refl]

-- Operator blocks are defined over any coefficient type and need no finite index types.
example {R m n m' n' : Type*} (em : m ≃ m') (en : n ≃ n')
    (X : Matrix (m × n) (m × n) R) (i j : m') (k l : n') :
    operatorBlock (reindex (em.prodCongr en) (em.prodCongr en) X) i j k l =
      X (em.symm i, en.symm k) (em.symm j, en.symm l) := by
  simp

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.reindexStarAlgEquiv, ``Matrix.reindexStarAlgEquiv_apply,
    ``Matrix.symm_reindexStarAlgEquiv,
    ``Matrix.reindexStarAlgEquiv_trans_reindexStarAlgEquiv,
    ``Matrix.bipartiteSlice_reindex_prod, ``Matrix.operatorBlock_reindex_prod,
    ``Matrix.matrixReindexStarAlgEquiv, ``Matrix.cfc_submatrix_equiv,
    ``Matrix.exists_unitary_block_implementers_of_starAlgEquiv_pi_matrix]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
