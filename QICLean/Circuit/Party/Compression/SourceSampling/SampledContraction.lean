/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.EndpointWord
import QICLean.Circuit.Party.Compression.SourceReplacement.Columns

/-!
# Contraction of columns against averages of endpoint operators

For each slot, expand its matrix as a finite combination of products of
two endpoint operators. Contracting these matrices against the ket and bra
columns of the prepared source words is a sum over one choice per slot.
In each summand the contraction factors as a product of local matrices.

Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 409–434 and
565–588. Adapted from TNLean, `TNLean/Lattice/Compression/ActualSampledPartyContraction.lean`
at `2417e0a2e4d8a1dc2db0a14e0c9cae4ca735829e`, with arbitrary finite slot averages.
-/

open Matrix ManyBody
open scoped Kronecker ComplexConjugate

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type}
  [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
  (w : SourceCircuit X Y)

local notation "R" => partialSlots (fun _ ↦ true) w
local notation "B" => partialSlotBases (fun _ ↦ true) w
local notation "Z" => blockSystem (affectedOwner (fun _ : P ↦ true)) (fun _ ↦ Unit)

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
private theorem slotColumnEquiv_allSourceColumnEquiv (a : ∀ i, (B).left i × (B).right i) :
    SourceInventory.slotColumnEquiv R B Z (allSourceColumnEquiv w a) =
      (a, default) := by
  change SourceInventory.slotColumnEquiv R B Z
      ((SourceInventory.slotColumnEquiv R B Z).symm ((Equiv.prodUnique _ _).symm a)) = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem weightedSum_contraction {I U V W : Type} [Fintype I] [Fintype U] [Fintype V]
    (c : I → ℂ) (L : Matrix W U ℂ) (A : I → Matrix U V ℂ) (N : Matrix V W ℂ) :
    L * (∑ a, c a • A a) * N = ∑ a, c a • (L * A a * N) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The contraction of the ket and bra columns against independent averages at the slots
is a weighted sum of products of the local ket, endpoint, and bra matrices.
The weights and the sample labels may depend on the slot. -/
theorem partialSourceGlobalMatrix_mixed_endpointAverage
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ ζ : Choices (fun _ ↦ true) w)
    {J : Fin (R).length → Type} [∀ i, Fintype (J i)] (c : ∀ i, J i → ℂ)
    (L : ∀ i, J i → Matrix ((B).left i) ((B).left i) ℂ)
    (M : ∀ i, J i → Matrix ((B).right i) ((B).right i) ℂ) :
    partialSourceGlobalMatrix w φ ξ *
      piKronecker (fun i ↦ ∑ j, c i j • (L i j ⊗ₖ M i j)) *
      (partialSourceGlobalMatrix w φ ζ)ᴴ =
      ∑ a : ∀ i, J i, (∏ i, c i (a i)) • piKronecker (fun p ↦
        PartyCircuit.partyOp (partialSourceWord w φ ξ) p *
          PartyCircuit.partyOp (SourceInventory.endpointWord Z R B
            (fun i ↦ L i (a i)) (fun i ↦ M i (a i))) p *
          (PartyCircuit.partyOp (partialSourceWord w φ ζ) p)ᴴ) := by
  have hav := SourceInventory.sum_op_endpointWord Z R B c L M
  have hprod : (reindex (SourceInventory.slotColumnEquiv R B Z).symm
      (SourceInventory.slotColumnEquiv R B Z).symm
      (piKronecker (fun i ↦ ∑ j, c i j • (L i j ⊗ₖ M i j)) ⊗ₖ
        (1 : Matrix (Config Z) (Config Z) ℂ))).submatrix (allSourceColumnEquiv w)
        (allSourceColumnEquiv w) = piKronecker (fun i ↦ ∑ j, c i j • (L i j ⊗ₖ M i j)) := by
    ext a b
    simp [reindex_apply, submatrix_apply, slotColumnEquiv_allSourceColumnEquiv,
      kroneckerMap_apply]
  rw [← hprod, ← hav, Matrix.submatrix_sum]
  simp only [Matrix.submatrix_smul]
  refine (weightedSum_contraction _ _ _ _).trans ?_
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  refine congrArg ((∏ i, c i (a i)) • ·) ?_
  exact partialSourceGlobalMatrix_mixed_word w φ ξ ζ _
    (SourceInventory.sources_endpointWord Z R B _ _)

end QuantumCircuit.Party.SourceCircuit
