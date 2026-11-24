/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.PhysicalSum
import QICLean.Circuit.Party.Compression.SourceSampling.Samples

/-!
# Physical traces for a fixed array of samples

At fixed labels of the ket and bra, the sampled density is a sum over the
sample choices at the retained slots. The coefficient is the product of one
factor (1/k) per slot. Each summand is the product of the local physical
matrices of the parties.

Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

open Matrix ManyBody
open scoped Kronecker ComplexConjugate

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type}
  [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
  (w : SourceCircuit X Y)

local notation "A" => fun _ : P ↦ true
local notation "Parties" => Option {_p : P // true = true}
local notation "R" => partialSlots A w
local notation "B" => partialSlotBases A w
local notation "Z" => blockSystem (affectedOwner A) (fun _ ↦ Unit)

/-- A constant product weight leaves the sum and contributes its `n`-th power. -/
private theorem endpointAverage_constWeight {n : ℕ} {J V : Type} [Fintype J]
    [AddCommMonoid V] [Module ℂ V] (c : ℂ) (f : (Fin n → J) → V) :
    (∑ a : Fin n → J, (∏ _i : Fin n, c) • f a) = c ^ n • ∑ a, f a := by
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.smul_sum]

set_option maxHeartbeats 500000 in
-- Matching the sampled factors with the dependent slot bases takes additional elaboration.
/-- The sampled column contraction with product readout and local partial
traces, at one ket and one bra branch, in the bases of the affected parties. Source:
Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem partialTraceRight_mixed_sampledSourceMatrix
    {Phys Env : Parties → Type} [∀ p, Fintype (Env p)]
    (K : ∀ p, Matrix (Phys p × Env p) (blockSystem (affectedOwner A) Y p) ℂ)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ ζ : Choices A w)
    (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (ω : SourceGaussianSamples w k) :
    let e := Equiv.arrowProdEquivProdArrow Parties Phys Env
    let s := fun i ↦ (partialSlotEquiv A w i).1
    let labels := fun i ↦ (partialSlotChoice A w ξ i, partialSlotChoice A w ζ i)
    let L := fun i j ↦ sampledEndpointLeft w k lam E (s i) (labels i) j ω
    let M := fun i j ↦ sampledEndpointRight w k lam F (s i) (labels i) j ω
    partialTraceRight (reindex e e
      (piKronecker K * (w.partialSourceGlobalMatrix φ ξ *
        (piKronecker (fun i ↦ sampledSourceMatrix w k lam E F (s i) (labels i).1 (labels i).2 ω) :
          Matrix (∀ i, (B).left i × (B).right i) (∀ i, (B).left i × (B).right i) ℂ) *
        (w.partialSourceGlobalMatrix φ ζ)ᴴ) * (piKronecker K)ᴴ)) =
      ((k : ℂ)⁻¹ ^ (R).length) • ∑ a : Fin (R).length → Fin k,
        piKronecker (fun p ↦ partialTraceRight
          (K p * (PartyCircuit.partyOp (partialSourceWord w φ ξ) p *
            PartyCircuit.partyOp (SourceInventory.endpointWord Z R B
              (fun i ↦ L i (a i)) (fun i ↦ M i (a i))) p *
            (PartyCircuit.partyOp (partialSourceWord w φ ζ) p)ᴴ) * (K p)ᴴ)) := by
  intro e s labels L M
  have hslot (i : Fin (R).length) :
      sampledSourceMatrix w k lam E F (s i) (labels i).1 (labels i).2 ω =
        ∑ j, (k : ℂ)⁻¹ • (L i j ⊗ₖ M i j) := by
    rw [sampledSourceMatrix_eq_endpoint_average, Finset.smul_sum]
  have hsum := partialTraceRight_mixed_endpointAverage w K φ ξ ζ
    (J := fun _ ↦ Fin k) (fun _ _ ↦ (k : ℂ)⁻¹) L M
  let C := ∀ i, (B).left i × (B).right i
  let read := fun T : Matrix C C ℂ ↦ partialTraceRight (reindex e e
    (piKronecker K * (w.partialSourceGlobalMatrix φ ξ * T *
      (w.partialSourceGlobalMatrix φ ζ)ᴴ) * (piKronecker K)ᴴ))
  have hm := congrArg (fun v : ∀ i : Fin (R).length,
      Matrix ((B).left i × (B).right i) ((B).left i × (B).right i) ℂ ↦
    read (piKronecker v)) (funext hslot)
  exact hm.trans (hsum.trans (endpointAverage_constWeight _ _))

end QuantumCircuit.Party.SourceCircuit
