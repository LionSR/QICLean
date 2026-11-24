/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.SampledPhysicalSum

/-!
# The sampled physical density on a product input

For a fixed sample and product readout, sum over the ket and bra branches
with their original coefficients. For each pair of branches, sum over the
sample labels of the sources. Each summand is a product of local matrices.

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

private theorem submatrix_sandwich {C C' D H H' : Type} [Fintype C] [Fintype C'] [Fintype D]
    (e : H' ≃ H) (b : C' ≃ C) (K : Matrix H C ℂ) (L N : Matrix C D ℂ) (M : Matrix D D ℂ) :
    K.submatrix e b * L.submatrix b id * M * (K.submatrix e b * N.submatrix b id)ᴴ =
      (K * (L * M * Nᴴ) * Kᴴ).submatrix e e := by
  rw [submatrix_mul_equiv K L e b id, submatrix_mul_equiv K N e b id, conjTranspose_submatrix]
  have h : (K * L).submatrix e id * M = (K * L * M).submatrix e id :=
    submatrix_mul_equiv (K * L) M e (Equiv.refl D) id
  rw [h]
  refine (submatrix_mul_equiv (K * L * M) (K * N)ᴴ e (Equiv.refl D) e).trans ?_
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- For each fixed array of Gaussian samples, the physical density of the
source-replaced circuit on a product input is a weighted sum of products
of the local physical matrices. The coefficient of each endpoint sample
choice is `(1/k)^n`, where `n` is the number of source slots. -/
theorem physicalSourceReplacedDensity_sampled_eq_sum
    {Phys Env : Parties → Type} [∀ p, Fintype (Env p)]
    (K : ∀ p, Matrix (Phys p × Env p) (blockSystem (affectedOwner A) Y p) ℂ)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (ω : SourceGaussianSamples w k) :
    let e := Equiv.arrowProdEquivProdArrow Parties Phys Env
    let b := blockConfigEquiv (affectedOwner A) Y
    let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun p x ↦ φ p x)
    let s := fun i ↦ (partialSlotEquiv A w i).1
    physicalSourceReplacedDensity w (fun s ξ ζ ↦ sampledSourceMatrix w k lam E F s ξ ζ ω)
      ((piKronecker K).submatrix e.symm b.symm) (euclideanOuterProduct ψ ψ) =
      ((k : ℂ)⁻¹ ^ (R).length) • ∑ ξ : Choices A w, ∑ ζ : Choices A w,
        (coefficient A w ξ * conj (coefficient A w ζ)) •
          ∑ a : Fin (R).length → Fin k,
            piKronecker (fun p ↦
              let label := fun i ↦ (partialSlotChoice A w ξ i, partialSlotChoice A w ζ i)
              let L := fun i ↦ sampledEndpointLeft w k lam E (s i) (label i) (a i) ω
              let M := fun i ↦ sampledEndpointRight w k lam F (s i) (label i) (a i) ω
              partialTraceRight (K p * (PartyCircuit.partyOp (partialSourceWord w φ ξ) p *
                PartyCircuit.partyOp (SourceInventory.endpointWord Z R B L M) p *
                (PartyCircuit.partyOp (partialSourceWord w φ ζ) p)ᴴ) * (K p)ᴴ)) := by
  intro e b ψ s
  dsimp only [ψ]
  rw [physicalSourceReplacedDensity_pure_eq_sum_actualColumnTraces]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ξ _ ↦ ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [submatrix_sandwich _ _ _ _ _ _]
  have h := partialTraceRight_mixed_sampledSourceMatrix w K φ ξ ζ k lam E F ω
  exact (congrArg ((coefficient A w ξ * conj (coefficient A w ζ)) • ·) h).trans
    (smul_comm _ _ _)

end QuantumCircuit.Party.SourceCircuit
