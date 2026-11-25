/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceNorm.OptimizedPureStateTraceError
import QICLean.Circuit.Party.Compression.GateExpansion.DensityError

/-!
# Distributed constructions

A distributed construction (Theorem 5.2) consists of the parties `P`, the basis `X p` of the
whole initial memory of every party with a unit vector `φ p` in it (the input is their product),
and a chronological original circuit whose output at every party is one physical register of
dimension `d p` in front of a discarded register `G p` (`physicalSystem d G`). The discarded
registers are kept until the end; the physical density is the partial trace over all of them of
the pure output, with no division by the output norm. It is positive semidefinite and has trace
at most one. The input data are shared with constructions that prescribe one gate map at every
gate occurrence of an effect circuit (`GateMapConstruction`), whose expansions may be chosen
later at any accuracy.

The private registers are finite basis types without any bound on their size.

Remark 5.3: when the physical density `ρ` is within `η` of a pure state `|Ω⟩⟨Ω|`, an operator
within `κ` of `ρ` is within `κ + η` of `|Ω⟩⟨Ω|`, and `1 - η ≤ Re Tr ρ ≤ 1`
(`rectangularTraceNorm_compression_sub_pure_le`).

**Local fix (nonempty parties):** the party set of a distributed construction is nonempty
(`DistributedConstructionData.nonemptyParties`). The scalar absorption in the proof of
Theorem 5.2 places an exterior scalar in the tensor of an existing party; with no party the
empty contraction is one, whereas a gate on the empty cell can change the output scalar. The
convention is recorded in `docs/paper-gaps/polypeps_nonempty_parties.tex`. The circuits
themselves keep their gates on the empty cell.

## Main definitions

* `QuantumCircuit.Party.DistributedConstructionData`, `DistributedConstructionData.input`.
* `QuantumCircuit.Party.DistributedConstruction`, `DistributedConstruction.physicalDensity`.
* `QuantumCircuit.Party.GateMapConstruction`, `GateMapConstruction.physicalDensity`.

## Main results

* `QuantumCircuit.Party.DistributedConstruction.physicalDensity_posSemidef`,
  `trace_physicalDensity_le_one`, `rectangularTraceNorm_compression_sub_pure_le`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 17–43, 137–153, 565–578 and 590–598; Remark 5.3 (`rem:compression-retained-norm`),
  lines 602–611; `01-preliminaries.tex`, lines 5–7.
-/

noncomputable section

open Matrix ManyBody
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

/-- The input data of a distributed construction on a finite nonempty party set: a unit vector in
the whole initial memory of every party. There is no bound on the private dimensions. Source:
Theorem 5.2, `04-compression.tex`, lines 17–30 and 137–151. -/
structure DistributedConstructionData (P : Type) [Fintype P] (X : P → Type)
    [∀ p, Fintype (X p)] where
  /-- An existing party at which scalar factors can be absorbed. Source: `04-compression.tex`,
  lines 565–578; the **Local fix** of the module docstring. -/
  nonemptyParties : Nonempty P
  /-- The initial vector of every party. Source: `04-compression.tex`, lines 137–139. -/
  initialVector : ∀ p, EuclideanSpace ℂ (X p)
  /-- The input is a product of unit vectors. Source: `04-compression.tex`, lines 137–139. -/
  norm_initialVector : ∀ p, ‖initialVector p‖ = 1

namespace DistributedConstructionData

variable {P : Type} [Fintype P] [DecidableEq P] {X : P → Type} [∀ p, Fintype (X p)]

/-- The product input of a distributed construction. Source: Theorem 5.2, `04-compression.tex`,
lines 137–139. -/
def input (C : DistributedConstructionData P X) : EuclideanSpace ℂ (Config X) :=
  WithLp.toLp 2 (productVector fun p x ↦ C.initialVector p x)

/-- The product input is a unit vector. -/
theorem norm_input (C : DistributedConstructionData P X) : ‖C.input‖ = 1 :=
  norm_toLp_productVector_eq_one C.initialVector C.norm_initialVector

end DistributedConstructionData

variable {P : Type} [Fintype P] [DecidableEq P]

/-- A distributed construction: the input data and an original circuit from the initial memories
to one physical register of dimension `d p` and a discarded register `G p` at every party. Source:
Theorem 5.2, `04-compression.tex`, lines 17–43 and 137–151. -/
structure DistributedConstruction (P : Type) [Fintype P] [DecidableEq P] (X : P → Type)
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (d : P → ℕ) (G : P → Type)
    [∀ p, Fintype (G p)] [∀ p, DecidableEq (G p)] extends DistributedConstructionData P X where
  /-- The original circuit, with its gate expansions. Source: `04-compression.tex`, lines 23–43
  and 137–151. -/
  circuit : OriginalCircuit X (physicalSystem d G)

namespace DistributedConstruction

variable {X : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] {d : P → ℕ}
  {G : P → Type} [∀ p, Fintype (G p)] [∀ p, DecidableEq (G p)]

/-- The physical density of the original circuit on the product input: the discarded registers
traced out, the subnormalization kept. Source: Theorem 5.2, `04-compression.tex`, lines 150–153.
-/
def physicalDensity (C : DistributedConstruction P X d G) :
    Matrix ((p : P) → Fin (d p)) ((p : P) → Fin (d p)) ℂ :=
  C.circuit.physicalDensity (physicalReadout d G) C.input

/-- The physical density is positive semidefinite. Source: Theorem 5.2, `04-compression.tex`,
lines 152–153. -/
theorem physicalDensity_posSemidef (C : DistributedConstruction P X d G) :
    C.physicalDensity.PosSemidef := by
  rw [physicalDensity, OriginalCircuit.physicalDensity_eq]
  exact (posSemidef_vecMulVec_self_star _).partialTraceRight

/-- **The physical density has trace at most one**; the output need not be normalized. Source:
Theorem 5.2, `04-compression.tex`, lines 152–153. -/
theorem trace_physicalDensity_le_one (C : DistributedConstruction P X d G) :
    C.physicalDensity.trace ≤ 1 := by
  rw [physicalDensity, OriginalCircuit.physicalDensity_eq, trace_partialTraceRight,
    trace_euclideanOuterProduct_self]
  have h2 : ‖Matrix.toEuclideanLin (physicalReadout d G)
      (Matrix.toEuclideanLin C.circuit.op C.input)‖ ≤ 1 :=
    (Matrix.norm_toEuclideanLin_apply_le_of_norm_le_one (norm_physicalReadout_le_one d G) _).trans
      ((Matrix.norm_toEuclideanLin_apply_le_of_norm_le_one C.circuit.norm_op_le_one _).trans
        C.norm_input.le)
  norm_cast
  exact pow_le_one₀ (norm_nonneg _) h2

/-- **Remark 5.3 for a distributed construction.** Let `ρ` be the physical density, which is not
normalized, and `σ` any operator with `‖σ - ρ‖₁ ≤ κ`, as produced by the compression theorem. If
`ρ` lies within `η` of the pure state of a unit vector `Ω`, then `‖σ - |Ω⟩⟨Ω|‖₁ ≤ κ + η` and
`1 - η ≤ Re Tr ρ ≤ 1`. Neither positivity nor hermiticity of `σ` is assumed, nor a bound on the
private dimensions or Schmidt ranks. Source: Remark 5.3 (`rem:compression-retained-norm`),
`04-compression.tex`, lines 602–611. -/
theorem rectangularTraceNorm_compression_sub_pure_le (C : DistributedConstruction P X d G)
    (σ : Matrix ((p : P) → Fin (d p)) ((p : P) → Fin (d p)) ℂ)
    (Ω : EuclideanSpace ℂ ((p : P) → Fin (d p))) (hΩ : ‖Ω‖ = 1) {κ η : ℝ}
    (hcompression : rectangularTraceNorm (σ - C.physicalDensity) ≤ κ)
    (hpure : rectangularTraceNorm (C.physicalDensity - euclideanOuterProduct Ω Ω) ≤ η) :
    rectangularTraceNorm (σ - euclideanOuterProduct Ω Ω) ≤ κ + η ∧
      1 - η ≤ C.physicalDensity.trace.re ∧ C.physicalDensity.trace.re ≤ 1 := by
  obtain ⟨hσ, htrace⟩ :=
    rectangularTraceNorm_sub_pure_le_of_retained_density σ C.physicalDensity Ω hΩ hcompression
      hpure
  refine ⟨hσ, ?_, ?_⟩
  · have hre := (Complex.abs_re_le_norm (C.physicalDensity.trace - 1)).trans htrace
    rw [Complex.sub_re, Complex.one_re] at hre
    linarith [neg_abs_le (C.physicalDensity.trace.re - 1)]
  · have h := (Complex.le_def.mp C.trace_physicalDensity_le_one).1
    rwa [Complex.one_re] at h

end DistributedConstruction

/-- A construction with prescribed gate maps: the input data, an effect circuit fixing the
chronology (local operations, cells and gates), and one gate map at every gate occurrence. The
expansions of the circuit are unrestricted: neither exactness nor allowedness is required.
Source: Theorem 5.2, `04-compression.tex`, lines 21–43, 137–151 and 590–598. -/
structure GateMapConstruction (P : Type) [Fintype P] [DecidableEq P] (X : P → Type)
    [∀ p, Fintype (X p)] (d : P → ℕ) (G : P → Type) extends DistributedConstructionData P X where
  /-- The private operations, the cells and the chronology. Source: `04-compression.tex`,
  lines 21–43 and 137–151. -/
  circuit : EffectCircuit X (physicalSystem d G)
  /-- The gate map at every gate occurrence. Source: `04-compression.tex`, lines 21–43 and
  590–598. -/
  gateMaps : circuit.GateMaps

namespace GateMapConstruction

variable {X : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] {d : P → ℕ}
  {G : P → Type} [∀ p, Fintype (G p)] [∀ p, DecidableEq (G p)]

/-- The physical density of the prescribed gate maps on the product input, the discarded registers
traced out, with no division by the output norm. Source: Theorem 5.2, `04-compression.tex`,
lines 150–153 and 590–598. -/
def physicalDensity (C : GateMapConstruction P X d G) :
    Matrix ((p : P) → Fin (d p)) ((p : P) → Fin (d p)) ℂ :=
  C.circuit.physicalDensityWithGateMaps C.gateMaps (physicalReadout d G) C.input

end GateMapConstruction

end QuantumCircuit.Party
