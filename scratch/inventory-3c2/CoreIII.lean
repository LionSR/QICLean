import QICLean

/-!
# Core III: statements (scratch, `sorry`)

Each item names, in its docstring, the 3C.2 restatements (files `Restate_{A,B,C,D}.lean` on
`inventory/3c2-restatements`) that use it.
-/

open Matrix ManyBody
open scoped Kronecker

/-! ### Sites: blocking (`ManyBody/Sites/Block.lean`) -/

namespace ManyBody

variable {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']

/-- The system on `S'` whose basis at `s'` is the configurations of the fibre of `f` over `s'`.
Used by: A `IsBlockedConversion`, `IsProtocol.exists_dual_comp_block`; B
`reindex_blockConfigEquiv_place`; D `exists_blocked`, `exists_regrouped(_bounded)`. -/
abbrev blockSystem (f : S → S') (X : S → Type) : S' → Type :=
  fun s' ↦ (s : {s // f s = s'}) → X s

/-- The configurations of the blocked system are those of the system. -/
def blockConfigEquiv (f : S → S') (X : S → Type) : Config (blockSystem f X) ≃ Config X :=
  sorry

/-- The configurations of a region `D'` of the blocked system are those of its preimage. -/
def blockRegionConfigEquiv (f : S → S') (X : S → Type) (D' : Finset S') :
    RegionConfig (blockSystem f X) D' ≃ RegionConfig X (Finset.univ.filter fun s ↦ f s ∈ D') :=
  sorry

/-- Blocking commutes with placement: an operator placed on `D'` of the blocked system is, read
on the system, the same operator placed on the preimage of `D'`. Used by: B
`reindex_blockConfigEquiv_place` (item 6, `dataOperator_embedOp`); D `exists_blocked`. -/
theorem reindex_blockConfigEquiv_place (f : S → S') {X : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] (D' : Finset S')
    (K : Matrix (RegionConfig (blockSystem f X) D') (RegionConfig (blockSystem f X) D') ℂ) :
    reindex (blockConfigEquiv f X) (blockConfigEquiv f X) (place D' K) =
      place (Finset.univ.filter fun s ↦ f s ∈ D')
        (reindex (blockRegionConfigEquiv f X D') (blockRegionConfigEquiv f X D') K) :=
  sorry

end ManyBody

/-! ### Kraus families: preparation and discard (`Channel/KrausFamily.lean`) -/

namespace KrausFamily

/-- The preparation of the basis vector `b` from the one-point basis. Used by: C
`freshInput` (fresh wires as onsite layers `PUnit → Fin d`), `exists_appended_unitary_dilation`,
`exists_physicalPortIO`; D `appendEnvironmentInput`. -/
def prepare {β : Type} [DecidableEq β] (b : β) : KrausFamily PUnit β :=
  single fun b' _ ↦ if b' = b then 1 else 0

/-- The discard of a basis: the partial trace onto the one-point basis. Used by: C
`discardEnvironment`, `exists_appended_unitary_dilation`; D `discardAppendedEnvironment`. -/
def discard (α : Type) [Fintype α] [DecidableEq α] : KrausFamily α PUnit :=
  ⟨α, fun a _ a' ↦ if a' = a then 1 else 0⟩

theorem isTP_prepare {β : Type} [Fintype β] [DecidableEq β] (b : β) : (prepare b).IsTP :=
  sorry

theorem isTP_discard (α : Type) [Fintype α] [DecidableEq α] : (discard α).IsTP :=
  sorry

theorem map_prepare {β : Type} [Fintype β] [DecidableEq β] (b : β)
    (ρ : Matrix PUnit PUnit ℂ) : (prepare b).map ρ = ρ () () • Matrix.single b b 1 :=
  sorry

theorem map_discard (α : Type) [Fintype α] [DecidableEq α] (ρ : Matrix α α ℂ) :
    (discard α).map ρ = fun _ _ ↦ ρ.trace :=
  sorry

end KrausFamily

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {ev : Interpretation G}

/-! ### Onsite layers and one-layer circuits (`Core/Parallel.lean`) -/

/-- The layer with no cells and the onsite family `o s` at every site (TNLean's
`OnsiteChannel`, the local basis may change). Used by: A `wholeSite_onsiteChannel`,
`map_onsiteEmbedding_comp`, `Layer.dual_mul_of_cells_eq_empty`; B `encodeCircuit`,
`decodeCircuit`, `Layer.exists_encoded` (case without cells); C `freshInput`,
`discardEnvironment`; D the `.onsite` constructor of `AdaptiveRound`. -/
def Layer.ofOnsite {X Y : S → Type} (o : (s : S) → KrausFamily (X s) (Y s)) : Layer Γ G X Y where
  cells := ∅
  pairwiseDisjoint := by simp
  gate b := absurd b.2 (Finset.notMem_empty _)
  onsite s := o s.1

/-- The Kraus operators of an onsite layer: the Kronecker product of one operator per site. -/
theorem Layer.kraus_ofOnsite {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (o : (s : S) → KrausFamily (X s) (Y s))
    (i : (Layer.ofOnsite (Γ := Γ) (G := G) o).Index) :
    (Layer.ofOnsite (Γ := Γ) (G := G) o).kraus ev i =
      prodOp fun s ↦ (o s).op (i.2 ⟨s, by simp [Layer.ofOnsite]⟩) :=
  sorry

/-- The circuit of one layer. Used by: B `encodeCircuit`, `decodeCircuit`,
`map_encodeCircuit_comp_decodeCircuit`; the substitution theorem below. -/
def Circuit.ofLayer {X Y : S → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (L : Layer Γ G X Y) : Circuit Γ G X Y :=
  .step L fun _ ↦ .done Y

theorem Circuit.map_ofLayer {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) :
    (Circuit.ofLayer L).map ev = (L.krausFamily ev).map :=
  sorry

/-! ### The Schrödinger picture layer by layer (`Core/Circuit.lean`) -/

namespace Circuit

variable {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]

/-- Used by: A `IsBoundedProtocol.comp` (through `map_comp`), the factorization proof; D the
feedforward of `AdaptiveRound` (`Circuit.step` with an outcome-dependent continuation). -/
theorem map_step (L : Layer Γ G X Y) (next : L.Index → Circuit Γ G Y Z)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    (step L next).map ev ρ = ∑ i, (next i).map ev (L.kraus ev i * ρ * (L.kraus ev i)ᴴ) :=
  sorry

/-- Used by: D `IsAdaptiveProtocol` composition (`AdaptiveConversion.comp`), C the dilation
(`prep`, unitary, `discard` as appended circuits). -/
theorem map_append (c : Circuit Γ G X Y) (k : c.Index → Circuit Γ G Y Z)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    (c.append k).map ev ρ = ∑ p, (k p).map ev (c.kraus ev p * ρ * (c.kraus ev p)ᴴ) :=
  sorry

/-- Trace duality of the two pictures. Used by: the factorization below; A
`IsConversion.trace_mul_mul_eq`. -/
theorem trace_map_mul (c : Circuit Γ G X Z) (ρ : Matrix (Config X) (Config X) ℂ)
    (A : Matrix (Config Z) (Config Z) ℂ) :
    (c.map ev ρ * A).trace = (ρ * c.dual ev A).trace :=
  sorry

end Circuit

/-! ### Bounded intermediate bases (`Core/Cost.lean` or a new `Core/Dimension.lean`) -/

/-- Every basis of every system along every branch has between `1` and `B` elements. Used by:
A `IsBoundedProtocol` and its `comp`, `mono_bound`, `dimension_bounds`,
`IsProtocol.exists_dimension_bound`; B `Circuit.exists_encoded_of_isDimBounded`; C
`exists_physicalPortIO`, `exists_physicalPortUnitaryIO`; D `exists_blocked`,
`exists_physicalPortSimulation`, the `BoundedPort*` theorems. -/
def Circuit.IsDimBounded (B : ℕ) : {X Z : S → Type} → Circuit Γ G X Z → Prop
  | X, _, Circuit.done _ => ∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B
  | X, _, Circuit.step _ next => (∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B) ∧
      ∀ i, (next i).IsDimBounded B

namespace Circuit

variable {X Y Z : S → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

theorem IsDimBounded.mono {B C : ℕ} (hBC : B ≤ C) {c : Circuit Γ G X Z}
    (h : c.IsDimBounded B) : c.IsDimBounded C :=
  sorry

theorem IsDimBounded.comp {B : ℕ} {c : Circuit Γ G X Y} {c' : Circuit Γ G Y Z}
    (h : c.IsDimBounded B) (h' : c'.IsDimBounded B) : (c.comp c').IsDimBounded B :=
  sorry

theorem IsDimBounded.input {B : ℕ} {c : Circuit Γ G X Z} (h : c.IsDimBounded B) (s : S) :
    0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B :=
  sorry

/-- The output bound needs a branch; a circuit without branches does not reach its output. -/
theorem IsDimBounded.output {B : ℕ} {c : Circuit Γ G X Z} (h : c.IsDimBounded B)
    (p : c.Index) (s : S) : 0 < Nat.card (Z s) ∧ Nat.card (Z s) ≤ B :=
  sorry

/-- Every circuit with nonempty finite bases is bounded by the largest of them. Used by: A
`IsProtocol.exists_dimension_bound`. -/
theorem exists_isDimBounded [∀ s, Fintype (X s)] [∀ s, Nonempty (X s)] (c : Circuit Γ G X Z) :
    ∃ B, c.IsDimBounded B :=
  sorry

end Circuit

/-! ### Moving to other sites, at the level of maps (`Core/Map.lean`) -/

section MapSites

variable {S' R : Type} [Fintype S'] [DecidableEq S'] [Fintype R] (e : S' ≃ S ⊕ R) (W : R → Type)
  [∀ r, Fintype (W r)] [∀ r, DecidableEq (W r)]
  {G' : Finset S' → (S' → Type) → (S' → Type) → Type 1} [GateFamily G'] {ev' : Interpretation G'}
  {Γ' : Geometry S'} (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')

/-- Moving commutes with composition. Used by: C `exists_appended_unitary_dilation`
(environment appended to a composite); D `register_matching` (a product of moved layers). -/
theorem Circuit.mapSites_comp {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (c : Circuit Γ G X Y) (c' : Circuit Γ G Y Z) :
    (c.comp c').mapSites e W h φ = (c.mapSites e W h φ).comp (c'.mapSites e W h φ) :=
  sorry

/-- The map of the moved circuit is that of the circuit tensored with the identity on the idle
sites. Used by: C `exists_appended_unitary_dilation`, `exists_selected_onsite_dilation`; D
`selected_layer`, `of_register_routing`; B `PhysicalRegisterEncoding` (b items). -/
theorem Circuit.map_mapSites {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] (hφ : φ.IsCompatible e W ev ev')
    (c : Circuit Γ G X Z) (ρ : Matrix (Config X) (Config X) ℂ)
    (ω : Matrix ((r : R) → W r) ((r : R) → W r) ℂ) :
    (c.mapSites e W h φ).map ev'
        ((ρ ⊗ₖ ω).submatrix (extendConfigEquiv e W X) (extendConfigEquiv e W X)) =
      (c.map ev ρ ⊗ₖ ω).submatrix (extendConfigEquiv e W Z) (extendConfigEquiv e W Z) :=
  sorry

end MapSites

/-! ### Substitution of circuits for layers (`Core/Substitute.lean`) -/

/-- A map of systems from the sites `S` to the sites `S'`, keeping finiteness and decidable
equality (the system part of `LayerMap`). -/
structure SystemMap (S S' : Type) where
  /-- The image of a system. -/
  system : (S → Type) → (S' → Type)
  /-- The image of a finite system is finite. -/
  fintype : ∀ (X : S → Type) [∀ s, Fintype (X s)], ∀ s', Fintype (system X s')
  /-- The image of a system with decidable equality has decidable equality. -/
  decidableEq : ∀ (X : S → Type) [∀ s, DecidableEq (X s)], ∀ s', DecidableEq (system X s')

attribute [instance] SystemMap.fintype SystemMap.decidableEq

/-- **Unbranched substitution.** If every layer of trace-preserving local families is realised,
through encodings `ι X` of the matrices of each system, by an unbranched circuit of
trace-preserving local families on other sites of depth at most `K` times its own, then so is
every unbranched circuit. Used by: D `exists_blocked` (`K = 2` or `3`, `ι` the blocking),
`exists_physicalPortSimulation` (`K = 2 k`, `ι` the port encoding); C `exists_physicalPortIO`;
A `IsProtocol.exists_dual_comp_block`. -/
theorem Circuit.exists_substitute {S' : Type} [Fintype S'] [DecidableEq S'] {Γ' : Geometry S'}
    {G' : Finset S' → (S' → Type) → (S' → Type) → Type 1} [GateFamily G']
    {ev' : Interpretation G'} (Ψ : SystemMap S S')
    (ι : ∀ (X : S → Type) [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)],
      Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config (Ψ.system X)) (Config (Ψ.system X)) ℂ)
    (K : ℕ)
    (hL : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y),
      L.Forall ev KrausFamily.IsTP →
        ∃ c' : Circuit Γ' G' (Ψ.system X) (Ψ.system Y), c'.IsUnbranched ∧
          c'.Forall ev' KrausFamily.IsTP ∧ c'.depth ≤ K * L.depth ∧
          c'.map ev' ∘ₗ ι X = ι Y ∘ₗ (Circuit.ofLayer L).map ev)
    {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)]
    [∀ s, DecidableEq (Z s)] (c : Circuit Γ G X Z) (hc : c.IsUnbranched)
    (hTP : c.Forall ev KrausFamily.IsTP) :
    ∃ c' : Circuit Γ' G' (Ψ.system X) (Ψ.system Z), c'.IsUnbranched ∧
      c'.Forall ev' KrausFamily.IsTP ∧ c'.depth ≤ K * c.depth ∧
      c'.map ev' ∘ₗ ι X = ι Z ∘ₗ c.map ev :=
  sorry

/-! ### Light cones and product inputs (`Core/LightCone.lean`) -/

/-- The Heisenberg picture of a layer with trace-preserving gates and onsite families is
multiplicative on operators whose light cones through the layer are disjoint. Used by: A
`Layer.dual_mul_of_disjoint_lightCone` (TNLean `BondChannelLayer.dual_mul`,
`OnsiteChannel.dual_mul`); the circuit form below. -/
theorem Layer.dual_mul_of_disjoint_lightCone {X Y : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (L : Layer Γ G X Y) (hL : L.Forall ev KrausFamily.IsTP) {R R' : Finset S}
    (hRR' : Disjoint (L.lightCone R) (L.lightCone R'))
    {A B : Matrix (Config Y) (Config Y) ℂ} (hA : A ∈ supportedOperators Y R)
    (hB : B ∈ supportedOperators Y R') :
    L.dual ev (A * B) = L.dual ev A * L.dual ev B :=
  sorry

/-- The same for an unbranched circuit and its backward light cones. Used by: A
`Circuit.dual_mul_of_disjoint_lightCone` (TNLean `channelCircuitDual_mul_of_disjoint_lightCone`),
`IsProtocol.exists_dual`, `IsProtocol.exists_dual_comp_block`. -/
theorem Circuit.dual_mul_of_disjoint_lightCone {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (c : Circuit Γ G X Z) (hc : c.IsUnbranched) (hTP : c.Forall ev KrausFamily.IsTP)
    {R R' : Finset S} (hRR' : Disjoint (c.lightCone R) (c.lightCone R'))
    {A B : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R)
    (hB : B ∈ supportedOperators Z R') :
    c.dual ev (A * B) = c.dual ev A * c.dual ev B :=
  sorry

/-- **The light-cone factorization.** For an unbranched circuit with trace-preserving gates and
onsite families on a product input `⊗ₛ σₛ` with `tr σₛ = 1`, the expectations of operators with
disjoint backward light cones factorize. The unitary case on a pure product vector is proved
directly in the 3C.3 unitary model. Used by: A `Circuit.trace_map_prodOp_mul_mul`,
`IsConversion.trace_mul_mul_eq`, `trace_mul_mul_eq_of_isConversion_ring`,
`trace_mul_mul_eq_of_isBlockedConversion_ring`. -/
theorem Circuit.trace_map_prodOp_mul_mul {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (c : Circuit Γ G X Z) (hc : c.IsUnbranched) (hTP : c.Forall ev KrausFamily.IsTP)
    (σ : (s : S) → Matrix (X s) (X s) ℂ) (hσ : ∀ s, (σ s).trace = 1)
    {R R' : Finset S} (hRR' : Disjoint (c.lightCone R) (c.lightCone R'))
    {A B : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R)
    (hB : B ∈ supportedOperators Z R') :
    (c.map ev (prodOp σ) * (A * B)).trace =
      (c.map ev (prodOp σ) * A).trace * (c.map ev (prodOp σ) * B).trace :=
  sorry

end QuantumCircuit
