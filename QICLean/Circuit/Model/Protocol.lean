/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core
import QICLean.ManyBody.Sites.Block

/-!
# Protocols

A protocol of depth at most `T` on a geometry `Γ` realising a linear map `Φ` is a circuit of
plain gates whose gates and onsite families are trace-preserving, of depth at most `T`, with map
`Φ`. The classes below are restrictions of `Circuit`, not new kinds of circuit: an adaptive
protocol may branch, a protocol is unbranched, and a bounded protocol in addition has every basis
along it of size between `1` and `B`. An exact conversion of `ρ` into `σ` is a protocol mapping
`ρ` to `σ`.

On a geometry whose cells all have positive cost, the trace-pairing adjoint `Φ*` of a protocol
of depth `T` maps an operator on a region `R` to an operator on the `T`-fold neighbourhood of
`R`, and is multiplicative on operators whose `T`-fold neighbourhoods are disjoint; from a
product input, expectations of such operators factorize. The same holds for a protocol on the
blocks of a map of sites, read on the sites.

## Main definitions

* `QuantumCircuit.IsAdaptiveProtocol`, `QuantumCircuit.IsProtocol`,
  `QuantumCircuit.IsBoundedProtocol` — the three classes of protocols.
* `QuantumCircuit.IsConversion` — exact conversion of one matrix into another.

## Main results

* `QuantumCircuit.IsProtocol.comp`, `QuantumCircuit.IsAdaptiveProtocol.comp`,
  `QuantumCircuit.IsBoundedProtocol.comp` — composition, with additive depth.
* `QuantumCircuit.IsBoundedProtocol.dimension_bounds`,
  `QuantumCircuit.IsProtocol.exists_dimension_bound` — the bounds of a bounded protocol, and a
  bound for every protocol on nonempty bases.
* `QuantumCircuit.IsProtocol.traceAdjointMap_mem_supportedOperators`,
  `QuantumCircuit.IsProtocol.traceAdjointMap_mul` — the light cone of a protocol.
* `QuantumCircuit.IsConversion.trace_mul_mul_eq` — factorization of expectations after a
  conversion of a product input.
* `QuantumCircuit.IsProtocol.traceAdjointMap_comp_block_mem_supportedOperators`,
  `QuantumCircuit.IsProtocol.traceAdjointMap_comp_block_mul` — the light cone of a protocol on
  blocks of sites.

The declarations restate, as restrictions of `Circuit`, the protocol classes and their light-cone
and dimension lemmas of `TNLean/Circuit/Channel/Conversion.lean`,
`TNLean/Circuit/Channel/Layer.lean`, `TNLean/Circuit/Channel/SiteBlocking.lean`,
`TNLean/Circuit/Channel/DimensionBoundedConversion.lean` and
`TNLean/Circuit/Measurement/AdaptiveConversion.lean` at commit
`75fc22288234ef66239cb4c2fa0b22914cfa5c6b` (Apache-2.0). The changes: the classes are
existentials over circuits of plain gates, on any geometry, instead of inductive families of ring
or port layers; the existential dual is replaced by the trace-pairing adjoint `traceAdjointMap`;
the light-cone statements take positivity of the costs of the cells for the ring's bonds of cost
`1`; `IsBlockedLocalChannelConversion` and `IsBondChannelPreparedInDepth` are not carried (the
blocked state is written out, and the second is a conversion of a product input).
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S]

section Classes

variable (Γ : Geometry S) {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Z s)]

/-- An adaptive protocol of depth at most `T` realising `Φ`: a circuit of plain gates whose
gates and onsite families are trace-preserving, with depth at most `T` and map `Φ`; later
layers may depend on the outcomes of earlier ones. -/
def IsAdaptiveProtocol (T : ℕ)
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X Z, c.Forall KrausGate.ev KrausFamily.IsTP ∧ c.depth ≤ T ∧
    c.map KrausGate.ev = Φ

/-- A protocol of depth at most `T` realising `Φ`: an adaptive protocol whose circuit is
unbranched. -/
def IsProtocol (T : ℕ)
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X Z, c.Forall KrausGate.ev KrausFamily.IsTP ∧ c.depth ≤ T ∧
    c.map KrausGate.ev = Φ ∧ c.IsUnbranched

/-- A protocol every basis along which has between `1` and `B` elements. -/
def IsBoundedProtocol (B T : ℕ)
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X Z, c.Forall KrausGate.ev KrausFamily.IsTP ∧ c.depth ≤ T ∧
    c.map KrausGate.ev = Φ ∧ c.IsUnbranched ∧ c.IsDimBounded B

/-- An exact conversion of `ρ` into `σ` by a protocol of depth at most `T`. -/
def IsConversion (T : ℕ) (ρ : Matrix (Config X) (Config X) ℂ)
    (σ : Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ Φ, IsProtocol Γ T Φ ∧ Φ ρ = σ

end Classes

variable {Γ : Geometry S} {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)]

/-! ### Composition -/

/-- A protocol is adaptive. -/
theorem IsProtocol.adaptive {T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Φ) : IsAdaptiveProtocol Γ T Φ :=
  let ⟨c, hTP, hd, hm, _⟩ := h
  ⟨c, hTP, hd, hm⟩

/-- A bounded protocol is a protocol. -/
theorem IsBoundedProtocol.isProtocol {B T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol Γ B T Φ) : IsProtocol Γ T Φ :=
  let ⟨c, hTP, hd, hm, hc, _⟩ := h
  ⟨c, hTP, hd, hm, hc⟩

/-- Adaptive protocols compose, with additive depth. -/
theorem IsAdaptiveProtocol.comp {T T' : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Y) (Config Y) ℂ}
    {Ψ : Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (hΦ : IsAdaptiveProtocol Γ T Φ) (hΨ : IsAdaptiveProtocol Γ T' Ψ) :
    IsAdaptiveProtocol Γ (T + T') (Ψ ∘ₗ Φ) := by
  obtain ⟨c, hcTP, hcd, rfl⟩ := hΦ
  obtain ⟨c', hc'TP, hc'd, rfl⟩ := hΨ
  exact ⟨c.comp c', hcTP.comp _ hc'TP,
    (Circuit.depth_comp c c').trans (Nat.add_le_add hcd hc'd), Circuit.map_comp _ c c'⟩

/-- Protocols compose, with additive depth. -/
theorem IsProtocol.comp {T T' : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Y) (Config Y) ℂ}
    {Ψ : Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (hΦ : IsProtocol Γ T Φ) (hΨ : IsProtocol Γ T' Ψ) : IsProtocol Γ (T + T') (Ψ ∘ₗ Φ) := by
  obtain ⟨c, hcTP, hcd, rfl, hc⟩ := hΦ
  obtain ⟨c', hc'TP, hc'd, rfl, hc'⟩ := hΨ
  exact ⟨c.comp c', hcTP.comp _ hc'TP,
    (Circuit.depth_comp c c').trans (Nat.add_le_add hcd hc'd), Circuit.map_comp _ c c',
    hc.comp hc'⟩

/-- Bounded protocols compose with the same bound, with additive depth. -/
theorem IsBoundedProtocol.comp {B T T' : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Y) (Config Y) ℂ}
    {Ψ : Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (hΦ : IsBoundedProtocol Γ B T Φ) (hΨ : IsBoundedProtocol Γ B T' Ψ) :
    IsBoundedProtocol Γ B (T + T') (Ψ ∘ₗ Φ) := by
  obtain ⟨c, hcTP, hcd, rfl, hc, hcB⟩ := hΦ
  obtain ⟨c', hc'TP, hc'd, rfl, hc', hc'B⟩ := hΨ
  exact ⟨c.comp c', hcTP.comp _ hc'TP,
    (Circuit.depth_comp c c').trans (Nat.add_le_add hcd hc'd), Circuit.map_comp _ c c',
    hc.comp hc', hcB.comp hc'B⟩

/-! ### Dimension bounds -/

/-- The input and output bases of a bounded protocol have between `1` and `B` elements. -/
theorem IsBoundedProtocol.dimension_bounds {B T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol Γ B T Φ) :
    (∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B) ∧
      ∀ s, 0 < Nat.card (Z s) ∧ Nat.card (Z s) ≤ B := by
  obtain ⟨c, hTP, -, -, -, hB⟩ := h
  have := fun s ↦ (Nat.card_pos_iff.mp (hB.input s).1).1
  obtain ⟨p⟩ := (c.isTP_krausFamily _ hTP).nonempty_index
  exact ⟨hB.input, hB.output p⟩

/-- A larger bound keeps a bounded protocol bounded. -/
theorem IsBoundedProtocol.mono_bound {B C T : ℕ} (hBC : B ≤ C)
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol Γ B T Φ) : IsBoundedProtocol Γ C T Φ :=
  let ⟨c, hTP, hd, hm, hc, hB⟩ := h
  ⟨c, hTP, hd, hm, hc, hB.mono hBC⟩

/-- A protocol on nonempty input bases is bounded by some `B`. The bound
depends on the protocol. -/
theorem IsProtocol.exists_dimension_bound [∀ s, Nonempty (X s)] {T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Φ) : ∃ B, IsBoundedProtocol Γ B T Φ :=
  let ⟨c, hTP, hd, hm, hc⟩ := h
  let ⟨B, hB⟩ := Circuit.exists_isDimBounded (ev := KrausGate.ev) c hTP
  ⟨B, c, hTP, hd, hm, hc, hB⟩

/-! ### Light cones -/

variable [∀ s, DecidableEq (Z s)] [Fintype Γ.Cell]

omit [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Z s)] in
/-- The circuit of a protocol, with its light cones inside the `T`-fold neighbourhoods. -/
private theorem IsProtocol.exists_circuit (hpos : ∀ b, 0 < Γ.cost b) {T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Φ) :
    ∃ c : Circuit Γ KrausGate X Z, c.Forall KrausGate.ev KrausFamily.IsTP ∧
      c.map KrausGate.ev = Φ ∧ c.IsUnbranched ∧
      ∀ R, c.lightCone R ⊆ Γ.neighbourhood^[T] R := by
  obtain ⟨c, hTP, hd, hm, hc⟩ := h
  exact ⟨c, hTP, hm, hc, fun R ↦
    (c.lightCone_subset_neighbourhood hpos R).trans (Γ.iterate_neighbourhood_mono hd le_rfl)⟩

omit [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Y s)] in
/-- On a geometry whose cells have positive cost, the trace-pairing adjoint of a protocol of
depth `T` maps an operator on `R` to an operator on the `T`-fold neighbourhood of `R`. -/
theorem IsProtocol.traceAdjointMap_mem_supportedOperators (hpos : ∀ b, 0 < Γ.cost b) {T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Φ) {R : Finset S} {A : Matrix (Config Z) (Config Z) ℂ}
    (hA : A ∈ supportedOperators Z R) :
    traceAdjointMap Φ A ∈ supportedOperators X (Γ.neighbourhood^[T] R) := by
  obtain ⟨c, hTP, rfl, hc, hR⟩ := h.exists_circuit hpos
  rw [c.traceAdjointMap_map]
  exact supportedOperators_mono (hR R) (c.dual_mem_supportedOperators_lightCone _ hc hTP hA)

omit [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Y s)] in
/-- On a geometry whose cells have positive cost, the trace-pairing adjoint of a protocol of
depth `T` is multiplicative on operators whose `T`-fold neighbourhoods are disjoint. -/
theorem IsProtocol.traceAdjointMap_mul (hpos : ∀ b, 0 < Γ.cost b) {T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Φ) {R R' : Finset S}
    (hRR' : Disjoint (Γ.neighbourhood^[T] R) (Γ.neighbourhood^[T] R'))
    {A B : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R)
    (hB : B ∈ supportedOperators Z R') :
    traceAdjointMap Φ (A * B) = traceAdjointMap Φ A * traceAdjointMap Φ B := by
  obtain ⟨c, hTP, rfl, hc, hR⟩ := h.exists_circuit hpos
  simp only [c.traceAdjointMap_map]
  exact c.dual_mul_of_disjoint_lightCone _ hc hTP (hRR'.mono (hR R) (hR R')) hA hB

omit [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Y s)] in
/-- On a geometry whose cells have positive cost, an exact conversion of depth `T` of a product
input with unit-trace factors gives an output on which the expectations of operators with
disjoint `T`-fold neighbourhoods factorize. -/
theorem IsConversion.trace_mul_mul_eq (hpos : ∀ b, 0 < Γ.cost b) {T : ℕ}
    {σ₀ : (s : S) → Matrix (X s) (X s) ℂ} (hσ₀ : ∀ s, (σ₀ s).trace = 1)
    {σ : Matrix (Config Z) (Config Z) ℂ} (h : IsConversion Γ T (prodOp σ₀) σ) {R R' : Finset S}
    (hRR' : Disjoint (Γ.neighbourhood^[T] R) (Γ.neighbourhood^[T] R'))
    {A B : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R)
    (hB : B ∈ supportedOperators Z R') :
    (σ * (A * B)).trace = (σ * A).trace * (σ * B).trace := by
  obtain ⟨_, hΦ, rfl⟩ := h
  obtain ⟨c, hTP, rfl, hc, hR⟩ := hΦ.exists_circuit hpos
  exact c.trace_map_prodOp_mul_mul _ hc hTP σ₀ hσ₀ (hRR'.mono (hR R) (hR R')) hA hB

/-! ### Blocks of sites -/

section Block

variable {S' : Type} [Fintype S'] [DecidableEq S'] (f : S → S') {Γ' : Geometry S'}
  [Fintype Γ'.Cell] {Z' : S' → Type} [∀ s, Fintype (Z' s)] [∀ s, DecidableEq (Z' s)]

omit [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Y s)] [∀ s, Fintype (Z s)]
  [∀ s, DecidableEq (Z s)] [Fintype Γ.Cell] in
/-- On a geometry of blocks whose cells have positive cost, a protocol of depth `T` on the
blocks of `f`, read on the sites, has trace-pairing adjoint mapping an operator on a region `R`
of blocks to an operator on the sites of the `T`-fold neighbourhood of `R`. -/
theorem IsProtocol.traceAdjointMap_comp_block_mem_supportedOperators
    (hpos : ∀ b, 0 < Γ'.cost b) {T : ℕ}
    {Φ : Matrix (Config (blockSystem f X)) (Config (blockSystem f X)) ℂ →ₗ[ℂ]
      Matrix (Config Z') (Config Z') ℂ}
    (h : IsProtocol Γ' T Φ) {R : Finset S'} {A : Matrix (Config Z') (Config Z') ℂ}
    (hA : A ∈ supportedOperators Z' R) :
    traceAdjointMap (Φ ∘ₗ (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X).symm).toLinearMap) A ∈
      supportedOperators X (blockPreimage f (Γ'.neighbourhood^[T] R)) := by
  rw [traceAdjointMap_comp_reindexAlgEquiv]
  obtain ⟨K, hK⟩ := exists_eq_place_of_mem_supportedOperators
    (h.traceAdjointMap_mem_supportedOperators hpos hA)
  rw [hK, coe_reindexAlgEquiv, reindex_blockConfigEquiv_place]
  exact place_mem_supportedOperators _

omit [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Y s)] [∀ s, Fintype (Z s)]
  [∀ s, DecidableEq (Z s)] [Fintype Γ.Cell] in
/-- On a geometry of blocks whose cells have positive cost, a protocol of depth `T` on the
blocks of `f`, read on the sites, has trace-pairing adjoint multiplicative on operators whose
`T`-fold neighbourhoods are disjoint. -/
theorem IsProtocol.traceAdjointMap_comp_block_mul (hpos : ∀ b, 0 < Γ'.cost b) {T : ℕ}
    {Φ : Matrix (Config (blockSystem f X)) (Config (blockSystem f X)) ℂ →ₗ[ℂ]
      Matrix (Config Z') (Config Z') ℂ}
    (h : IsProtocol Γ' T Φ) {R R' : Finset S'}
    (hRR' : Disjoint (Γ'.neighbourhood^[T] R) (Γ'.neighbourhood^[T] R'))
    {A B : Matrix (Config Z') (Config Z') ℂ} (hA : A ∈ supportedOperators Z' R)
    (hB : B ∈ supportedOperators Z' R') :
    traceAdjointMap (Φ ∘ₗ (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X).symm).toLinearMap)
        (A * B) =
      traceAdjointMap (Φ ∘ₗ (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X).symm).toLinearMap) A *
        traceAdjointMap (Φ ∘ₗ (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X).symm).toLinearMap)
          B := by
  simp only [traceAdjointMap_comp_reindexAlgEquiv, h.traceAdjointMap_mul hpos hRR' hA hB, map_mul]

end Block

end QuantumCircuit
