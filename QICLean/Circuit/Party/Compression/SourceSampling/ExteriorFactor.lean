/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.ExteriorScalar
import QICLean.Circuit.Party.Compression.SourceSampling.PhysicalDensity

/-!
# The exterior factor of the sampled physical sum

When every party is affected, the exterior party holds no register: its bases have one
configuration, the prepared source words act there by the exterior scalar
`SourceCircuit.emptyGateScalar`, and every endpoint word acts there as the identity. The local
physical matrix of the exterior party is therefore the squared modulus of the exterior scalar
times the partial trace of the exterior readout, whatever the ket and bra branches and the
endpoint operators. This common factor leaves the sum over the sample choices and the sum over
the branches: the sampled physical density is `(1/k)^n |emptyGateScalar|²` times the sum of the
products of the local physical matrices of the parties, the exterior one replaced by the partial
trace of its readout. No scalar is divided out; the scalar may vanish.

## Main results

In the namespace `QuantumCircuit.Party.SourceCircuit`:

* `partialSourceWord_sampled_none_partialTrace_eq_scalar`,
  `partialSourceWord_sampled_none_partialTrace_eq_scalar_smul_one`.
* `partialSourceGlobalMatrix_sampled_partialTrace_eq_scalar_smul_physicalSum`.
* `physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_physicalSum`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 137–139, 246–267, 279–355, 409–434 and 565–588 (especially 574–579).
-/

open Matrix ManyBody
open scoped Kronecker ComplexConjugate

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace SourceCircuit

variable [Fintype P] {X Y : P → Type}
  [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
  (w : SourceCircuit X Y)

local notation "A" => fun _ : P ↦ true
local notation "Parties" => Option {_p : P // true = true}
local notation "R" => partialSlots A w
local notation "B" => partialSlotBases A w
local notation "Z" => blockSystem (affectedOwner A) (fun _ ↦ Unit)

/-- **The exterior factor of a sampled local trace is the squared modulus of the exterior
scalar times the partial trace of the exterior readout.** The ket and bra branches, the endpoint
operators and the readout are arbitrary; no normalization or nonvanishing is required. Source:
Theorem 5.2, `04-compression.tex`, lines 137–139, 246–267 and 565–588. -/
theorem partialSourceWord_sampled_none_partialTrace_eq_scalar
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ ζ : Choices A w)
    (L : ∀ i, Matrix ((B).left i) ((B).left i) ℂ) (M : ∀ i, Matrix ((B).right i) ((B).right i) ℂ)
    {Phys Env : Type} [Fintype Env]
    (K : Matrix (Phys × Env) (blockSystem (affectedOwner A) Y none) ℂ) :
    partialTraceRight (K * (PartyCircuit.partyOp (partialSourceWord w φ ξ) none *
        PartyCircuit.partyOp (SourceInventory.endpointWord Z R B L M) none *
        (PartyCircuit.partyOp (partialSourceWord w φ ζ) none)ᴴ) * Kᴴ) =
      (w.emptyGateScalar * conj w.emptyGateScalar) • partialTraceRight (K * Kᴴ) := by
  have hE : PartyCircuit.partyOp (SourceInventory.endpointWord Z R B L M) none = 1 :=
    SourceInventory.partyOp_endpointWord_eq_one Z R B L M none
      (fun i h ↦ ((partialSlots_all_ne_none w i).1 h).elim)
      (fun i h ↦ ((partialSlots_all_ne_none w i).2 h).elim)
  let _ : Unique (Z none) := uniqueBlockSystemNone fun _ ↦ Unit
  let _ : Unique (allSourceSystem w none) :=
    (Equiv.cast (SourceInventory.slotSystem_eq_of_forall_ne Z none R B
      (partialSlots_all_ne_none w))).unique
  let _ : Unique (blockSystem (affectedOwner A) Y none) := uniqueBlockSystemNone Y
  have hmid : PartyCircuit.partyOp (partialSourceWord w φ ξ) none *
      (PartyCircuit.partyOp (partialSourceWord w φ ζ) none)ᴴ =
      (w.emptyGateScalar * conj w.emptyGateScalar) • 1 := by
    ext y y'
    rw [mul_apply, Fintype.sum_unique, conjTranspose_apply,
      partyOp_partialSourceWord_none_apply, partyOp_partialSourceWord_none_apply,
      Matrix.smul_apply, one_apply, ite_eq_left (Subsingleton.elim y y'), smul_eq_mul, mul_one]
    rfl
  rw [hE, Matrix.mul_one, hmid, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    partialTraceRight_smul]

/-- The exterior factor for an isometric readout into a one-element physical basis: the
squared modulus of the exterior scalar. This is the case of an orthonormal basis of the
exterior output, and the value does not depend on the isometry. Source: Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–267 and 565–588. -/
theorem partialSourceWord_sampled_none_partialTrace_eq_scalar_smul_one
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ ζ : Choices A w)
    (L : ∀ i, Matrix ((B).left i) ((B).left i) ℂ) (M : ∀ i, Matrix ((B).right i) ((B).right i) ℂ)
    {Phys Env : Type} [Unique Phys] [DecidableEq Phys] [Fintype Env]
    (K : Matrix (Phys × Env) (blockSystem (affectedOwner A) Y none) ℂ) (hK : Kᴴ * K = 1) :
    partialTraceRight (K * (PartyCircuit.partyOp (partialSourceWord w φ ξ) none *
        PartyCircuit.partyOp (SourceInventory.endpointWord Z R B L M) none *
        (PartyCircuit.partyOp (partialSourceWord w φ ζ) none)ᴴ) * Kᴴ) =
      (w.emptyGateScalar * conj w.emptyGateScalar) • (1 : Matrix Phys Phys ℂ) := by
  rw [partialSourceWord_sampled_none_partialTrace_eq_scalar]
  congr 1
  let _ : Unique (blockSystem (affectedOwner A) Y none) := uniqueBlockSystemNone Y
  ext i j
  have ht : (partialTraceRight (K * Kᴴ)).trace = 1 := by
    rw [trace_partialTraceRight, Matrix.trace_mul_comm, hK, Matrix.trace_one,
      Fintype.card_unique, Nat.cast_one]
  rw [Matrix.trace, Fintype.sum_unique, Matrix.diag_apply] at ht
  rw [Subsingleton.elim i default, Subsingleton.elim j default, ht, one_apply_eq]

/-- A product of local matrices whose exterior factor is the exterior scalar factor: the
scalar leaves the product, the partial trace of the exterior readout stays. -/
private theorem piKronecker_sampledFactors_eq_smul
    {Phys Env : Parties → Type} [∀ p, Fintype (Env p)]
    (K : ∀ p, Matrix (Phys p × Env p) (blockSystem (affectedOwner A) Y p) ℂ)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ ζ : Choices A w)
    (L : ∀ i, Matrix ((B).left i) ((B).left i) ℂ)
    (M : ∀ i, Matrix ((B).right i) ((B).right i) ℂ) :
    piKronecker (fun p ↦ partialTraceRight
        (K p * (PartyCircuit.partyOp (partialSourceWord w φ ξ) p *
          PartyCircuit.partyOp (SourceInventory.endpointWord Z R B L M) p *
          (PartyCircuit.partyOp (partialSourceWord w φ ζ) p)ᴴ) * (K p)ᴴ)) =
      (w.emptyGateScalar * conj w.emptyGateScalar) •
        piKronecker (Function.update (fun p ↦ partialTraceRight
          (K p * (PartyCircuit.partyOp (partialSourceWord w φ ξ) p *
            PartyCircuit.partyOp (SourceInventory.endpointWord Z R B L M) p *
            (PartyCircuit.partyOp (partialSourceWord w φ ζ) p)ᴴ) * (K p)ᴴ)) none
          (partialTraceRight (K none * (K none)ᴴ))) := by
  rw [← piKronecker_update_smul, Function.update_self, Function.update_idem,
    ← partialSourceWord_sampled_none_partialTrace_eq_scalar w φ ξ ζ L M (K none),
    Function.update_eq_self]

set_option maxHeartbeats 500000 in
-- Matching the sampled factors with the dependent slot bases takes additional elaboration.
/-- **The sampled column contraction is the exterior scalar factor times the sum of the
products of the local physical matrices.** At one ket and one bra branch, the common factor
`(1/k)^n |emptyGateScalar|²` stands outside the sum over the sample choices; in each product the
exterior factor is the partial trace of the exterior readout. No exterior coefficient or
factorization is supplied as a hypothesis. Source: Theorem 5.2, `04-compression.tex`,
lines 565–588. -/
theorem partialSourceGlobalMatrix_sampled_partialTrace_eq_scalar_smul_physicalSum
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
      (((k : ℂ)⁻¹ ^ (R).length) * (w.emptyGateScalar * conj w.emptyGateScalar)) •
        ∑ a : Fin (R).length → Fin k,
          piKronecker (Function.update (fun p ↦ partialTraceRight
            (K p * (PartyCircuit.partyOp (partialSourceWord w φ ξ) p *
              PartyCircuit.partyOp (SourceInventory.endpointWord Z R B
                (fun i ↦ L i (a i)) (fun i ↦ M i (a i))) p *
              (PartyCircuit.partyOp (partialSourceWord w φ ζ) p)ᴴ) * (K p)ᴴ)) none
            (partialTraceRight (K none * (K none)ᴴ))) := by
  intro e s labels L M
  refine (partialTraceRight_mixed_sampledSourceMatrix w K φ ξ ζ k lam E F ω).trans ?_
  rw [← smul_smul, Finset.smul_sum (r := w.emptyGateScalar * conj w.emptyGateScalar)]
  refine congrArg (((k : ℂ)⁻¹ ^ (R).length) • ·) (Finset.sum_congr rfl fun a _ ↦ ?_)
  exact piKronecker_sampledFactors_eq_smul w K φ ξ ζ _ _

/-- **The sampled physical density on a product input is the exterior scalar factor times the
double branch sum of the sampled products of local physical matrices.** For each fixed array of
Gaussian samples the common factor `(1/k)^n |emptyGateScalar|²`, with `n` the number of source
slots, stands outside the sums over the ket and bra branches and over the sample choices; the
exterior scalar is retained multiplicatively, without cancellation, and in each product the
exterior factor is the partial trace of the exterior readout. No positivity, normalization or
factorization is assumed. Source: Theorem 5.2, `04-compression.tex`, lines 279–355, 409–434 and
565–588. -/
theorem physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_physicalSum
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
      (((k : ℂ)⁻¹ ^ (R).length) * (w.emptyGateScalar * conj w.emptyGateScalar)) •
        ∑ ξ : Choices A w, ∑ ζ : Choices A w,
          (coefficient A w ξ * conj (coefficient A w ζ)) •
            ∑ a : Fin (R).length → Fin k,
              piKronecker (Function.update (fun p ↦
                let label := fun i ↦ (partialSlotChoice A w ξ i, partialSlotChoice A w ζ i)
                let L := fun i ↦ sampledEndpointLeft w k lam E (s i) (label i) (a i) ω
                let M := fun i ↦ sampledEndpointRight w k lam F (s i) (label i) (a i) ω
                partialTraceRight (K p * (PartyCircuit.partyOp (partialSourceWord w φ ξ) p *
                  PartyCircuit.partyOp (SourceInventory.endpointWord Z R B L M) p *
                  (PartyCircuit.partyOp (partialSourceWord w φ ζ) p)ᴴ) * (K p)ᴴ)) none
                (partialTraceRight (K none * (K none)ᴴ))) := by
  intro e b ψ s
  refine (physicalSourceReplacedDensity_sampled_eq_sum w K φ k lam E F ω).trans ?_
  rw [← smul_smul]
  refine congrArg (((k : ℂ)⁻¹ ^ (R).length) • ·) ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ξ _ ↦ ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [smul_comm, Finset.smul_sum (r := w.emptyGateScalar * conj w.emptyGateScalar)]
  refine congrArg ((coefficient A w ξ * conj (coefficient A w ζ)) • ·)
    (Finset.sum_congr rfl fun a _ ↦ ?_)
  exact piKronecker_sampledFactors_eq_smul w K φ ξ ζ _ _

end SourceCircuit

end QuantumCircuit.Party
