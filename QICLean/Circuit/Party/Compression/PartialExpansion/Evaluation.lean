/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Choices

/-!
# The weighted sum of a partial expansion

The weighted sum of the branches of the partial expansion of a source circuit along affected
parties (`SourceCircuit.expandedEval`) is the operator of the circuit read on the affected parties
and the exterior party (`SourceCircuit.expandedEval_eq_reindex_op`, a reading of
`SourceCircuit.sum_coefficient_smul_op_partialWord`). Independent choices at the two parts of a
composition multiply the sums, and spectator factors stay untouched.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.expandedEval`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.expandedEval_comp`,
  `QuantumCircuit.Party.SourceCircuit.expandedEval_frame`,
  `QuantumCircuit.Party.SourceCircuit.expandedEval_eq_reindex_op`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 351–417.

Adapted from TNLean, `TNLean/Lattice/Compression/PartialSourceEvaluation.lean` at commit
`a05f5d6d0a` (Apache-2.0). Changes: the identity of the whole sum is
`SourceCircuit.sum_coefficient_smul_op_partialWord` of `Source/PreparedGate`; the gate case is
its gate case.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

namespace SourceCircuit

variable (A : P → Bool) {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The weighted sum of the branches of the partial expansion. Source: Theorem 5.2,
`04-compression.tex`, lines 351–417. -/
noncomputable def expandedEval (w : SourceCircuit X Y) :
    Matrix (Config (blockSystem (affectedOwner A) Y))
      (Config (blockSystem (affectedOwner A) X)) ℂ :=
  ∑ ξ, coefficient A w ξ • Word.op (partialWord A w ξ)

/-- Independent choices at the two parts of a composition multiply the weighted sums.
Source: Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem expandedEval_comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (w : SourceCircuit X Y)
    (w' : SourceCircuit Y Z) :
    expandedEval A (PartyCircuit.comp w w') = expandedEval A w' * expandedEval A w := by
  simp only [expandedEval, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Finset.smul_sum, smul_smul]
  refine (Fintype.sum_prod_type _).trans
    (Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ξ' _ ↦ ?_)
  exact congrArg ((coefficient A w ξ * coefficient A w' ξ') • ·) (Word.op_comp _ _)

/-- Spectator factors are untouched by the partial expansion. Source: Theorem 5.2,
`04-compression.tex`, lines 383–417. -/
theorem expandedEval_frame (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]
    (w : SourceCircuit X Y) :
    expandedEval A (w.frame W) =
      reindex (blockConfigProdEquiv (affectedOwner A) W Y).symm
        (blockConfigProdEquiv (affectedOwner A) W X).symm
        ((1 : Matrix (Config (blockSystem (affectedOwner A) W))
          (Config (blockSystem (affectedOwner A) W)) ℂ) ⊗ₖ expandedEval A w) := by
  unfold expandedEval
  refine (Fintype.sum_equiv (choicesFrameEquiv A W w) _
    (fun ξ ↦ coefficient A w ξ • reindex (blockConfigProdEquiv (affectedOwner A) W Y).symm
      (blockConfigProdEquiv (affectedOwner A) W X).symm
      ((1 : Matrix (Config (blockSystem (affectedOwner A) W))
        (Config (blockSystem (affectedOwner A) W)) ℂ) ⊗ₖ Word.op (partialWord A w ξ)))
    fun ξ ↦ by rw [coefficient_frame, op_partialWord_frame]).trans ?_
  ext y x
  simp only [reindex_apply, submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
    kroneckerMap_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

/-- **The partial expansion sums to the circuit**, read on the affected parties and the
exterior party; no norm condition is needed. Source: Theorem 5.2, `04-compression.tex`,
lines 351–417. -/
theorem expandedEval_eq_reindex_op (w : SourceCircuit X Y) :
    expandedEval A w =
      reindex (blockConfigEquiv (affectedOwner A) Y).symm
        (blockConfigEquiv (affectedOwner A) X).symm w.op :=
  sum_coefficient_smul_op_partialWord A w

end SourceCircuit

end QuantumCircuit.Party
