/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.PartialTrace
import QICLean.Channel.PartialTrace.TensorPowerPartialTrace
import QICLean.Circuit.Party.Compression.SourceSampling.SampledContraction

/-!
# Physical traces of sampled column contractions

For a product readout, the partial trace of each sampled column contraction
factors over the parties. At each party one traces only its local discarded
basis. The finite sum retains the original weights of the endpoint choices.

Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

open Matrix ManyBody
open scoped Kronecker ComplexConjugate

namespace QuantumCircuit.Party

/-- The partial trace of a product readout of a weighted sum of product matrices is the weighted
sum of the products of the local partial traces. -/
private theorem partialTraceRight_weighted_readout
    {J P : Type} [Fintype J] [Fintype P] [DecidableEq P]
    {Phys Env X : P → Type} [∀ p, Fintype (Env p)] [∀ p, Fintype (X p)]
    (c : J → ℂ) (K : ∀ p, Matrix (Phys p × Env p) (X p) ℂ)
    (A : J → ∀ p, Matrix (X p) (X p) ℂ) :
    let e := Equiv.arrowProdEquivProdArrow P Phys Env
    partialTraceRight (reindex e e
      (piKronecker K * (∑ j, c j • piKronecker (A j)) * (piKronecker K)ᴴ)) =
      ∑ j, c j • piKronecker (fun p ↦ partialTraceRight (K p * A j p * (K p)ᴴ)) := by
  let e := Equiv.arrowProdEquivProdArrow P Phys Env
  let f := partialTraceRightLM ∘ₗ (reindexLinearEquiv ℂ ℂ e e).toLinearMap
  change f _ = _
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, map_sum, map_smul]
  refine Finset.sum_congr rfl fun j _ ↦ congrArg (c j • ·) ?_
  simp only [conjTranspose_piKronecker, piKronecker_mul]
  exact partialTraceRight_piKronecker_submatrix _

namespace SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type}
  [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
  (w : SourceCircuit X Y)

local notation "Parties" => Option {_p : P // true = true}
local notation "R" => partialSlots (fun _ ↦ true) w
local notation "B" => partialSlotBases (fun _ ↦ true) w
local notation "Z" => blockSystem (affectedOwner (fun _ : P ↦ true)) (fun _ ↦ Unit)

/-- The physical partial trace after contracting finite endpoint averages and
applying a product readout. Each summand is the product of the physical
partial traces at the individual parties. Source:
Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem partialTraceRight_mixed_endpointAverage
    {Phys Env : Parties → Type} [∀ p, Fintype (Env p)]
    (K : ∀ p, Matrix (Phys p × Env p) (blockSystem (affectedOwner (fun _ ↦ true)) Y p) ℂ)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ ζ : Choices (fun _ ↦ true) w)
    {J : Fin (R).length → Type} [∀ i, Fintype (J i)] (c : ∀ i, J i → ℂ)
    (L : ∀ i, J i → Matrix ((B).left i) ((B).left i) ℂ)
    (M : ∀ i, J i → Matrix ((B).right i) ((B).right i) ℂ) :
    let e := Equiv.arrowProdEquivProdArrow Parties Phys Env
    partialTraceRight (reindex e e
      (piKronecker K * (w.partialSourceGlobalMatrix φ ξ *
        piKronecker (fun i ↦ ∑ j, c i j • (L i j ⊗ₖ M i j)) *
        (w.partialSourceGlobalMatrix φ ζ)ᴴ) * (piKronecker K)ᴴ)) =
      ∑ a : ∀ i, J i, (∏ i, c i (a i)) • piKronecker (fun p ↦ partialTraceRight
        (K p * (PartyCircuit.partyOp (partialSourceWord w φ ξ) p *
          PartyCircuit.partyOp (SourceInventory.endpointWord Z R B
            (fun i ↦ L i (a i)) (fun i ↦ M i (a i))) p *
          (PartyCircuit.partyOp (partialSourceWord w φ ζ) p)ᴴ) * (K p)ᴴ)) := by
  dsimp only
  rw [partialSourceGlobalMatrix_mixed_endpointAverage]
  exact partialTraceRight_weighted_readout _ K _

end SourceCircuit

end QuantumCircuit.Party
