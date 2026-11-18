import QICLean

/-!
# 3C.2 inventory: the missing core notions, as statements

Scratch definitions (some `sorry`) that the restated (c) theorems need. Each corresponds to a
core gap of the inventory; none of this is meant to be merged as written.
-/

open Matrix ManyBody QuantumCircuit

namespace Inventory

/-! ### Uniform systems (proposal: `ManyBody/Sites`, `abbrev Qudits`) -/

/-- The system with basis `Fin d` at every site of `V`. -/
abbrev Qudits (V : Type) (d : ℕ) : V → Type := fun _ ↦ Fin d

/-- Placement along an embedding: the configurations of the image of `e` are those of `X ∘ e`
(coordinator: one `ManyBody/Sites` identification). -/
noncomputable def regionConfigMapEquiv {V V' : Type} [Fintype V] (X : V' → Type) (e : V ↪ V') :
    RegionConfig X (Finset.univ.map e) ≃ Config (X ∘ e) := sorry

/-! ### Local properties used as predicates -/

/-- Every family is unitary (a local property). -/
abbrev IsUnitaryLocal {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (K : KrausFamily α β) : Prop :=
  K.IsUnitary

/-- Every family is trace-preserving (a local property). -/
abbrev IsTPLocal {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (K : KrausFamily α β) : Prop :=
  K.IsTP

/-! ### Geometries (gap: `Circuit/Geometry`) -/

/-- The ring on `Fin N`: bonds `{k, k + 1}` of cost `1`. -/
def ring (N : ℕ) [NeZero N] : Geometry (Fin N) where
  Cell := Fin N
  cell k := {k, k + 1}
  cost _ := 1

instance (N : ℕ) [NeZero N] : Fintype (ring N).Cell := inferInstanceAs (Fintype (Fin N))

/-- TNLean's layout of wires on sites, verbatim. -/
structure PhysicalPortLayout (N W : ℕ) where
  site : Fin W → Fin N
  port : Fin N ↪ Fin W
  site_port : ∀ i, site (port i) = i

/-- The port geometry on the wires: every set of wires inside one site at cost `0`, the bonds of
the ring between consecutive ports at cost `1`. -/
def portGeometry {N W : ℕ} [NeZero N] (P : PhysicalPortLayout N W) : Geometry (Fin W) where
  Cell := {D : Finset (Fin W) // ∃ i, ∀ w ∈ D, P.site w = i} ⊕ Fin N
  cell
    | .inl D => D.1
    | .inr k => {P.port k, P.port (k + 1)}
  cost
    | .inl _ => 0
    | .inr _ => 1

/-! ### Circuit classes (restrictions of `Circuit`) -/

end Inventory

namespace QuantumCircuit.Circuit

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Every intermediate basis has between `1` and `B` elements (gap: dimension bound). -/
def IsDimBounded {Γ : Geometry S} {G : Finset S → (S → Type) → (S → Type) → Type 1}
    [GateFamily G] (B : ℕ) : {X Z : S → Type} → Circuit Γ G X Z → Prop
  | X, _, done _ => ∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B
  | X, _, step _ next => (∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B) ∧
      ∀ i, (next i).IsDimBounded B

end QuantumCircuit.Circuit

namespace Inventory

variable {S : Type} [Fintype S] [DecidableEq S]


/-- An unbranched circuit of plain gates with trace-preserving local families, of depth at
most `T`, realising the channel `Φ` (TNLean's `IsLocalChannelProtocol` on the ring when
`Γ = ring N` and the end systems are uniform; `IsPhysicalPortProtocol` when
`Γ = portGeometry P`). -/
def IsProtocol (Γ : Geometry S) (T : ℕ) {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X Z, c.IsUnbranched ∧ c.Forall KrausGate.ev IsTPLocal ∧
    c.depth ≤ T ∧ c.map KrausGate.ev = Φ

/-- The same with every local family unitary and the unique Kraus operator `U`
(`IsPhysicalPortUnitary` when `Γ = portGeometry P`). -/
def IsUnitaryCircuit (Γ : Geometry S) (T : ℕ) {X : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] (U : Matrix (Config X) (Config X) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X X, c.IsUnbranched ∧ c.Forall KrausGate.ev IsUnitaryLocal ∧
    c.depth ≤ T ∧ ∀ p, c.kraus KrausGate.ev p = U

/-- A dimension-bounded protocol (`IsDimensionBoundedLocalChannelProtocol B`). -/
def IsBoundedProtocol (Γ : Geometry S) (B T : ℕ) {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X Z, c.IsUnbranched ∧ c.Forall KrausGate.ev IsTPLocal ∧
    c.depth ≤ T ∧ c.IsDimBounded B ∧ c.map KrausGate.ev = Φ

/-- An adaptive protocol: branching allowed, every local family a component of an instrument,
so the Kraus family of the circuit is trace-preserving (`IsAdaptiveChannelProtocol`). -/
def IsAdaptiveProtocol (Γ : Geometry S) (T : ℕ) {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X Z, c.Forall KrausGate.ev IsTPLocal ∧ c.depth ≤ T ∧
    c.map KrausGate.ev = Φ

/-! ### Blocking (gap) -/

/-- The system on `S'` whose basis at `s'` is the configurations of the fibre of `f`. -/
abbrev blockSystem {S' : Type} (f : S → S') (X : S → Type) : S' → Type :=
  fun s' ↦ (s : {s // f s = s'}) → X s

/-- The configurations of the blocked system are those of the system. -/
noncomputable def blockConfigEquiv {S' : Type} (f : S → S') (X : S → Type) :
    Config (blockSystem f X) ≃ Config X := sorry

end Inventory

/-! # Group D: routing and compilation (restated (c) theorems) -/

namespace Inventory.D

/-! ### Gaps -/

section Gaps

/-- Gap (open-chain geometry): cells on the neighbouring pairs `{p, p'}` with `p' = p + 1` of an
open chain, each of cost `1`. TNLean's `IsNeighbourGate` is a unitary gate on such a cell. -/
def chain (N : ℕ) : Geometry (Fin N) where
  Cell := {p : Fin N × Fin N // p.2.val = p.1.val + 1}
  cell p := {p.1.1, p.1.2}
  cost _ := 1

instance (N : ℕ) : Fintype (chain N).Cell :=
  inferInstanceAs (Fintype {p : Fin N × Fin N // p.2.val = p.1.val + 1})

/-- Gap 3 (relabelling operator of a site permutation on a uniform system): TNLean's
`permOp σ`, entry `1` at `(x, y)` when `y = x ∘ σ`. The core has `siteConfigurationEquiv` but no
operator on configurations, and no swap gate for a general system. -/
def relabelOp {V : Type} [Fintype V] [DecidableEq V] (d : ℕ) (σ : Equiv.Perm V) :
    Matrix (Config (Qudits V d)) (Config (Qudits V d)) ℂ :=
  Matrix.of fun x y ↦ if y = x ∘ σ then 1 else 0

/-- Gap (gate-count class): the gate-count analogue of `IsUnitaryCircuit`; on `chain n` it is
TNLean's `IsPairProduct d n K U`. -/
def IsUnitaryGateCircuit {S : Type} [Fintype S] [DecidableEq S] (Γ : Geometry S) (K : ℕ)
    {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (U : Matrix (Config X) (Config X) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X X, c.IsUnbranched ∧ c.Forall KrausGate.ev IsUnitaryLocal ∧
    c.gateCount ≤ K ∧ ∀ p, c.kraus KrausGate.ev p = U

/-- Gap 8 (operator moved along an embedding of sites of a uniform system): TNLean's
`embedOp e A`, the placement on the image of `e`. The core moves operators only through
`mapSites`, whose system `extendSystem e W X` is not definitionally `Qudits V' d`. -/
noncomputable def embedAlong {V V' : Type} [Fintype V] [Fintype V'] [DecidableEq V'] (d : ℕ)
    (e : V ↪ V') (A : Matrix (Config (Qudits V d)) (Config (Qudits V d)) ℂ) :
    Matrix (Config (Qudits V' d)) (Config (Qudits V' d)) ℂ :=
  place (Finset.univ.map e)
    (A.submatrix (regionConfigMapEquiv (Qudits V' d) e) (regionConfigMapEquiv (Qudits V' d) e))

/-- Gap 8: a Kraus family moved along an embedding of sites (TNLean's
`fun j ↦ embedOp e (K j)`). -/
noncomputable def placeAlongFamily {V V' : Type} [Fintype V] [Fintype V'] [DecidableEq V']
    (d : ℕ) (e : V ↪ V') (K : KrausFamily (Config (Qudits V d)) (Config (Qudits V d))) :
    KrausFamily (Config (Qudits V' d)) (Config (Qudits V' d)) :=
  ⟨K.Index, fun j ↦ embedAlong d e (K.op j)⟩

/-- Gap 8: conjugation of a map by the relabelling of a site permutation, TNLean's
`routingChannelConj σ` (`Φ ↦ U Φ(U† · U) U†`). -/
noncomputable def relabelConj {V : Type} [Fintype V] [DecidableEq V] (d : ℕ)
    (σ : Equiv.Perm V)
    (Φ : Module.End ℂ (Matrix (Config (Qudits V d)) (Config (Qudits V d)) ℂ)) :
    Module.End ℂ (Matrix (Config (Qudits V d)) (Config (Qudits V d)) ℂ) :=
  singleKrausMap (relabelOp d σ) ∘ₗ Φ ∘ₗ singleKrausMap (relabelOp d σ)ᴴ

/-- Gap 9 (register layout): TNLean's `PortRegisters.layout N k`; site `i` owns the wires
`(i, s)`, `s : Fin (1 + k + k)` (port `s = 0`, data `1 ≤ s ≤ k`, scratch). -/
def portLayout (N k : ℕ) : PhysicalPortLayout N (N * (1 + k + k)) where
  site w := (finProdFinEquiv.symm w).1
  port := ⟨fun i ↦ finProdFinEquiv (i, ⟨0, by omega⟩), fun _ _ _ ↦ sorry⟩
  site_port _ := sorry

/-- Gap 9: the `k` data wires of the site `i` in `portLayout N k`. -/
def dataWires (N k : ℕ) (i : Fin N) : Finset (Fin (N * (1 + k + k))) :=
  Finset.univ.image fun t : Fin k ↦ finProdFinEquiv (i, ⟨1 + t.val, by omega⟩)

/-- Gap 1 + 9 (ring of registers): the ring on `Fin N` whose cell `i` is the data registers of
the sites `i` and `i + 1`, at cost `1` (the cells of TNLean's `PortRegisters.pairChannel`). -/
def registerRing (N k : ℕ) [NeZero N] : Geometry (Fin (N * (1 + k + k))) where
  Cell := Fin N
  cell i := dataWires N k i ∪ dataWires N k (i + 1)
  cost _ := 1

instance (N k : ℕ) [NeZero N] : Fintype (registerRing N k).Cell :=
  inferInstanceAs (Fintype (Fin N))

/-- Gap 9: TNLean's `DataReference N k d`, the configurations of the port and scratch wires. -/
abbrev DataReference (N k d : ℕ) : Type :=
  {w : Fin (N * (1 + k + k)) // w ∉ Finset.univ.biUnion (dataWires N k)} → Fin d

/-- Gap 9 (register encoding with reference): TNLean's
`PortRegisters.physicalEncoding (OnsiteChannel.encodeRegisters fun _ ↦ c).map`: the code `c`
on the data register of each site, the reference on the other wires. In the core it is the map
of a cost-0 isometric layer followed by the identification of the wires. -/
noncomputable def portEncoding (N k d : ℕ) {m : ℕ} (c : Fin m ↪ Fin (d ^ k)) :
    Matrix (Config (Qudits (Fin N) m) × DataReference N k d)
        (Config (Qudits (Fin N) m) × DataReference N k d) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits (Fin (N * (1 + k + k))) d))
        (Config (Qudits (Fin (N * (1 + k + k))) d)) ℂ :=
  sorry

/-- Gap 9: TNLean's `registerEncoding (wordCodeConfiguration (portWordCode d k))`, the
isometry writing each `d`-level site into the word code of its `1 + k + k` wires (the Kraus
operator of a cost-0 onsite isometric layer). -/
noncomputable def portWordEncoding (N k d : ℕ) [NeZero d] :
    Matrix (Config (Qudits (Fin (N * (1 + k + k))) d)) (Config (Qudits (Fin N) d)) ℂ :=
  sorry

/-- Gap 7 (appended environment wires): TNLean's `PhysicalPortLayout.append P owner`. -/
def appendLayout {N W A : ℕ} (P : PhysicalPortLayout N W) (owner : Fin A → Fin N) :
    PhysicalPortLayout N (W + A) where
  site := Fin.addCases P.site owner
  port := P.port.trans (Fin.castAddEmb A)
  site_port _ := sorry

/-- Gap 7: the split of the wires `Fin (W + A)` into the original and the environment wires
(TNLean's `appendMatrixSplit` is reindexing along it). -/
def envSplit (W A d : ℕ) :
    Config (Qudits (Fin (W + A)) d) ≃ Config (Qudits (Fin W) d) × Config (Qudits (Fin A) d) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl (Fin d))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- Gap 7: TNLean's `appendEnvironmentInput W A d`, preparing the environment wires in `0`. -/
noncomputable def appendEnvironmentInput (W A d : ℕ) [NeZero d] :
    Matrix (Config (Qudits (Fin W) d)) (Config (Qudits (Fin W) d)) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits (Fin (W + A)) d)) (Config (Qudits (Fin (W + A)) d)) ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ (envSplit W A d).symm (envSplit W A d).symm).toLinearMap ∘ₗ
    singleKrausMap (fixedEnvEmbedding (0 : Config (Qudits (Fin A) d)))

/-- Gap 7: TNLean's `discardAppendedEnvironment W A d`, the partial trace over the environment
wires. -/
noncomputable def discardAppendedEnvironment (W A d : ℕ) :
    Matrix (Config (Qudits (Fin (W + A)) d)) (Config (Qudits (Fin (W + A)) d)) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits (Fin W) d)) (Config (Qudits (Fin W) d)) ℂ :=
  sorry

/-- Gap 4 (blocking map of the ring): the block `⌊i / k⌋` of a site of `Fin (M * k)`
(TNLean's `siteBlock`). -/
def siteBlock (M k : ℕ) (i : Fin (M * k)) : Fin M :=
  (finProdFinEquiv.symm i).1

/-- Gap 4 (blocked map): a map of the system, read on the blocked system along `f`
(TNLean's `regroupChannel M k F`, without the encoding `Fin k → Fin d ≃ Fin (d ^ k)`). -/
noncomputable def blockedMap {S S' : Type} (f : S → S') {X Z : S → Type}
    (F : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) :
    Matrix (Config (blockSystem f X)) (Config (blockSystem f X)) ℂ →ₗ[ℂ]
      Matrix (Config (blockSystem f Z)) (Config (blockSystem f Z)) ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ (blockConfigEquiv f Z).symm
      (blockConfigEquiv f Z).symm).toLinearMap ∘ₗ F ∘ₗ
    (Matrix.reindexLinearEquiv ℂ ℂ (blockConfigEquiv f X) (blockConfigEquiv f X)).toLinearMap

end Gaps

/-! ### PortMatching -/

/- TNLean `TNLean/Circuit/Channel/PortMatching.lean`:
theorem isPairProduct_permOp_swap (i j : Fin N) :
    IsPairProduct d N (2 * N) (permOp (Equiv.swap i j))
-/

/-- The SWAP of two arbitrary sites of the open chain is the Kraus operator of an unbranched
unitary circuit of gate count at most `2N` on the neighbouring pairs. -/
theorem isPairProduct_permOp_swap {d N : ℕ} (i j : Fin N) :
    IsUnitaryGateCircuit (chain N) (2 * N) (relabelOp d (Equiv.swap i j)) :=
  sorry

/-- Support (answer to the consumer question): the gate-count class on `chain n` is TNLean's
`IsPairProduct d n K U` verbatim, so `IsPairProduct` can become this class. -/
theorem isUnitaryGateCircuit_chain_iff {d n K : ℕ}
    (U : Matrix (Config (Qudits (Fin n) d)) (Config (Qudits (Fin n) d)) ℂ) :
    IsUnitaryGateCircuit (chain n) K U ↔
      ∃ l : List (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ), l.length ≤ K ∧
        (∀ Z ∈ l, Z ∈ unitary (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) ∧
          ∃ p p' : Fin n, p'.val = p.val + 1 ∧
            Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) {p, p'}) ∧
        U = l.prod :=
  sorry

/-! ### PortRouting -/

/- TNLean `TNLean/Circuit/Channel/PortRouting.lean` (`variable {d N W : ℕ} [NeZero N]`):
theorem IsPhysicalPortUnitary.selected_layer (P : PhysicalPortLayout N W)
    (e : Fin N ↪ Fin W) (he : ∀ i, P.site (e i) = i) (L : RingLayer d N) :
    IsPhysicalPortUnitary P 1 (embedOp e L.op)
-/

/-- A unitary layer of the ring, moved onto wires `e i` that lie at the site `i`, is a port
circuit of depth `1`. The ring layer may carry unitary onsite families (TNLean's has the
identity there), which land in cost-0 fibre cells. -/
theorem selected_layer {d N W : ℕ} [NeZero N] (P : PhysicalPortLayout N W)
    (e : Fin N ↪ Fin W) (he : ∀ i, P.site (e i) = i)
    (L : Layer (ring N) KrausGate (Qudits (Fin N) d) (Qudits (Fin N) d))
    (hL : L.Forall KrausGate.ev IsUnitaryLocal) (i : L.Index) :
    IsUnitaryCircuit (portGeometry P) 1
      (embedAlong d e (L.kraus KrausGate.ev i)) :=
  sorry

/- TNLean `TNLean/Circuit/Channel/PortRouting.lean` (`namespace IsPhysicalPortUnitary`,
`variable {d k N W : ℕ} [NeZero N]`):
theorem register_matching (P : PhysicalPortLayout N W) (e : Fin k → (Fin N ↪ Fin W))
    (he : ∀ t i, P.site (e t i) = i) (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) :
    IsPhysicalPortUnitary (d := d) P k
      (permOp (registerPermutation e (PortMatching.perm K hK)))
-/

/-- `k` unitary ring layers, the `t`-th moved onto the digit wires `e t`, form a port circuit
of depth `k`. TNLean's statement is the case where every layer is the swap layer of the
matching `K` (whose moved Kraus operators multiply to `registerPermutation`). -/
theorem register_matching {d k N W : ℕ} [NeZero N] (P : PhysicalPortLayout N W)
    (e : Fin k → (Fin N ↪ Fin W)) (he : ∀ t i, P.site (e t i) = i)
    (L : Fin k → Layer (ring N) KrausGate (Qudits (Fin N) d) (Qudits (Fin N) d))
    (hL : ∀ t, (L t).Forall KrausGate.ev IsUnitaryLocal) (i : ∀ t, (L t).Index) :
    IsUnitaryCircuit (portGeometry P) k
      (List.ofFn fun t ↦ embedAlong d (e t) ((L t).kraus KrausGate.ev (i t))).prod :=
  sorry

/-! ### PortChannelRouting -/

/- TNLean `TNLean/Circuit/Channel/PortChannelRouting.lean` (`variable {d W : ℕ}`,
`{N : ℕ} [NeZero N]`):
theorem IsPhysicalPortProtocol.of_register_routing {m r : ℕ} (P : PhysicalPortLayout N W)
    (e : Fin m ↪ Fin W) (K : Fin r → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)
    (hK : ∑ j, (K j)ᴴ * K j = 1) {T : ℕ} (σ : Equiv.Perm (Fin W))
    (hσ : IsPhysicalPortUnitary (d := d) P T (permOp σ))
    (i : Fin N) (hsite : ∀ j, P.site (σ (e j)) = i) :
    IsPhysicalPortProtocol P (2 * T) (rectangularKrausMap fun j => embedOp e (K j))
-/

/-- A trace-preserving family on a register `e`, which a unitary port circuit of depth `T`
relabels into one site, is a port protocol of depth `2T`. -/
theorem of_register_routing {d N W m : ℕ} [NeZero N] (P : PhysicalPortLayout N W)
    (e : Fin m ↪ Fin W) (K : KrausFamily (Config (Qudits (Fin m) d)) (Config (Qudits (Fin m) d)))
    (hK : K.IsTP) {T : ℕ} (σ : Equiv.Perm (Fin W))
    (hσ : IsUnitaryCircuit (portGeometry P) T (relabelOp d σ))
    (i : Fin N) (hsite : ∀ j, P.site (σ (e j)) = i) :
    IsProtocol (portGeometry P) (2 * T) (placeAlongFamily d e K).map :=
  sorry

/- TNLean `TNLean/Circuit/Channel/PortChannelRouting.lean`:
theorem IsPhysicalPortProtocol.of_routed_family {α : Type*} (P : PhysicalPortLayout N W)
    (s : Finset α)
    (F : α → Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ))
    (hcomm : (s : Set α).Pairwise (Function.onFun Commute F)) {T : ℕ}
    (σ : Equiv.Perm (Fin W)) (hσ : IsPhysicalPortUnitary (d := d) P T (permOp σ))
    (hF : ∀ j ∈ s, IsPhysicalPortProtocol P 0 (routingChannelConj σ (F j))) :
    IsPhysicalPortProtocol P (2 * T) (s.noncommProd F hcomm)
-/

/-- A layer of gates on disjoint cells of any geometry on the wires, each of which becomes a
depth-0 port protocol after relabelling by `σ`, is a port protocol of depth `2T` when the
relabelling is a unitary port circuit of depth `T`. The commuting family is the layer, and the
commutation hypothesis is the disjointness of its cells. -/
theorem of_routed_family {d N W : ℕ} [NeZero N] (P : PhysicalPortLayout N W)
    {Γ : Geometry (Fin W)} (cells : Finset Γ.Cell)
    (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell)
    (g : (b : cells) → KrausGate (Γ.cell b) (Qudits (Fin W) d) (Qudits (Fin W) d)) {T : ℕ}
    (σ : Equiv.Perm (Fin W)) (hσ : IsUnitaryCircuit (portGeometry P) T (relabelOp d σ))
    (hg : ∀ b : cells, IsProtocol (portGeometry P) 0
      (relabelConj d σ (Layer.placeFamily (Γ.cell b) (g b)).map)) :
    IsProtocol (portGeometry P) (2 * T)
      ((Layer.ofCells cells h g).krausFamily KrausGate.ev).map :=
  sorry

/-! ### PortSimulation -/

/- TNLean `TNLean/Circuit/Channel/PortSimulation.lean` (`namespace QuantumCircuit.PortRegisters`,
`variable {d N k : ℕ} [NeZero N]`):
theorem matchingChannel_isPhysicalPortProtocol (hN : 2 ≤ N) {r : Fin N → ℕ}
    (A : ∀ i, Fin (r i) → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (K : Finset (Fin N)) (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond)
    (hA : ∀ i ∈ K, ∑ a, (A i a)ᴴ * A i a = 1) :
    IsPhysicalPortProtocol (layout N k) (2 * k) (matchingChannel hN A K hK)
-/

/-- One layer of trace-preserving gates on the ring of `k`-wire data registers is a port
protocol of depth `2k`. `hN` is dropped: it only made `pairData i (i + 1)` an embedding. -/
theorem matchingChannel_isPhysicalPortProtocol {d N k : ℕ} [NeZero N]
    (K : Finset (registerRing N k).Cell)
    (hK : (K : Set (registerRing N k).Cell).PairwiseDisjoint (registerRing N k).cell)
    (g : (b : K) → KrausGate ((registerRing N k).cell b) (Qudits (Fin (N * (1 + k + k))) d)
      (Qudits (Fin (N * (1 + k + k))) d))
    (hg : ∀ b, (g b).IsTP) :
    IsProtocol (portGeometry (portLayout N k)) (2 * k)
      ((Layer.ofCells K hK g).krausFamily KrausGate.ev).map :=
  sorry

/-! ### PhysicalProtocolCompilation -/

/- TNLean `TNLean/Circuit/Channel/PhysicalProtocolCompilation.lean`
(`variable {N B m n T d : ℕ} [NeZero N]`):
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPortSimulation
    {Ψ : Matrix (Fin N → Fin m) (Fin N → Fin m) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin n) (Fin N → Fin n) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    let k := Nat.clog d B
    let hB : B ≤ d ^ k := Nat.le_pow_clog hd B
    let E := (OnsiteChannel.encodeRegisters fun _ : Fin N =>
      boundedAlphabetCode hB h.dimension_bounds.1.2).map
    let F := (OnsiteChannel.encodeRegisters fun _ : Fin N =>
      boundedAlphabetCode hB h.dimension_bounds.2.2).map
    ∃ Γ, IsPhysicalPortProtocol (PortRegisters.layout N k) (2 * k * T) Γ ∧
      Γ ∘ₗ PortRegisters.physicalEncoding E =
        PortRegisters.physicalEncoding F ∘ₗ tensorMapIdLM Ψ
-/

/-- A dimension-bounded ring protocol of depth `T` compiles to a port protocol of depth
`2 ⌈log_d B⌉ T` intertwining the register encodings, with the port and scratch wires as a
reference. The bounds `m, n ≤ d ^ k` (TNLean's `h.dimension_bounds` composed with
`Nat.le_pow_clog`) are returned, since the codes need them. -/
theorem exists_physicalPortSimulation {N B m n T d : ℕ} [NeZero N]
    {Ψ : Matrix (Config (Qudits (Fin N) m)) (Config (Qudits (Fin N) m)) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits (Fin N) n)) (Config (Qudits (Fin N) n)) ℂ}
    (h : IsBoundedProtocol (ring N) B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    let k := Nat.clog d B
    ∃ (hm : m ≤ d ^ k) (hn : n ≤ d ^ k), ∃ Φ,
      IsProtocol (portGeometry (portLayout N k)) (2 * k * T) Φ ∧
      Φ ∘ₗ portEncoding N k d (Fin.castLEEmb hm) =
        portEncoding N k d (Fin.castLEEmb hn) ∘ₗ tensorMapIdLM Ψ :=
  sorry

/-! ### RegroupedProtocol -/

/-- Support (the blocking theorem): an unbranched trace-preserving circuit on the ring of
`M * k` sites, blocked into `M` blocks of `k` consecutive sites, is an unbranched
trace-preserving circuit on the ring of `M` sites of depth at most `2` (`M` even) or `3` times
the depth, with the same map read through the blocking; intermediate bases of size at most `B`
become blocks of size at most `B ^ k`. Both `exists_regrouped` are corollaries. -/
theorem exists_blocked {M k : ℕ} [NeZero M] [NeZero k] {X Z : Fin (M * k) → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (c : Circuit (ring (M * k)) KrausGate X Z) (hc : c.IsUnbranched)
    (hTP : c.Forall KrausGate.ev IsTPLocal) :
    ∃ c' : Circuit (ring M) KrausGate (blockSystem (siteBlock M k) X)
        (blockSystem (siteBlock M k) Z),
      c'.IsUnbranched ∧ c'.Forall KrausGate.ev IsTPLocal ∧
      c'.depth ≤ (if M % 2 = 0 then 2 else 3) * c.depth ∧
      (∀ B, c.IsDimBounded B → c'.IsDimBounded (B ^ k)) ∧
      c'.map KrausGate.ev = blockedMap (siteBlock M k) (c.map KrausGate.ev) :=
  sorry

/- TNLean `TNLean/Circuit/Channel/RegroupedProtocol.lean` (`variable {M k d e : ℕ}`):
theorem ChannelLayer.exists_regrouped_layers [NeZero M] [NeZero k] (L : ChannelLayer d (M * k)) :
    ∃ Ls : List (ChannelLayer (d ^ k) M),
      Ls.length ≤ (if M % 2 = 0 then 2 else 3) ∧
        channelCircuitMap Ls = regroupChannel M k L.map
-/

/-- A layer of trace-preserving gates on the ring of `M * k` sites, blocked, is a sequence of
at most `2` (`M` even) or `3` trace-preserving layers on the ring of `M` blocks. -/
theorem exists_regrouped_layers {M k d : ℕ} [NeZero M] [NeZero k]
    (K : Finset (ring (M * k)).Cell)
    (hK : (K : Set (ring (M * k)).Cell).PairwiseDisjoint (ring (M * k)).cell)
    (g : (b : K) → KrausGate ((ring (M * k)).cell b) (Qudits (Fin (M * k)) d)
      (Qudits (Fin (M * k)) d))
    (hg : ∀ b, (g b).IsTP) :
    ∃ Ls : List (Layer (ring M) KrausGate (blockSystem (siteBlock M k) (Qudits (Fin (M * k)) d))
        (blockSystem (siteBlock M k) (Qudits (Fin (M * k)) d))),
      Ls.length ≤ (if M % 2 = 0 then 2 else 3) ∧ (∀ L ∈ Ls, L.Forall KrausGate.ev IsTPLocal) ∧
      (Circuit.seq Ls).map KrausGate.ev =
        blockedMap (siteBlock M k) ((Layer.ofCells K hK g).krausFamily KrausGate.ev).map :=
  sorry

/- TNLean `TNLean/Circuit/Channel/RegroupedProtocol.lean`:
theorem IsDimensionBoundedLocalChannelProtocol.exists_regrouped [NeZero M] [NeZero k] {B T : ℕ}
    {F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T F) :
    ∃ S, S ≤ (if M % 2 = 0 then 2 else 3) * T ∧
      IsDimensionBoundedLocalChannelProtocol (B ^ k) S (regroupChannel M k F)
-/

/-- Blocking a protocol with intermediate bases of size at most `B` gives a protocol on the
blocked ring of depth at most `(2 | 3) T` with blocks of size at most `B ^ k`. -/
theorem exists_regrouped_bounded {M k : ℕ} [NeZero M] [NeZero k] {B T : ℕ}
    {X Z : Fin (M * k) → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    {F : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol (ring (M * k)) B T F) :
    ∃ S, S ≤ (if M % 2 = 0 then 2 else 3) * T ∧
      IsBoundedProtocol (ring M) (B ^ k) S (blockedMap (siteBlock M k) F) :=
  sorry

/- TNLean `TNLean/Circuit/Channel/RegroupedProtocol.lean`:
theorem IsLocalChannelProtocol.exists_regrouped [NeZero M] [NeZero k] {T : ℕ}
    {F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ}
    (h : IsLocalChannelProtocol T F) (hd : 0 < d) :
    ∃ S, S ≤ (if M % 2 = 0 then 2 else 3) * T ∧
      IsLocalChannelProtocol S (regroupChannel M k F)
-/

/-- Blocking a protocol on the ring of `M * k` sites gives a protocol on the ring of `M` blocks
of depth at most `(2 | 3) T`. `hd : 0 < d` is dropped: it served only TNLean's detour through a
dimension bound. -/
theorem exists_regrouped {M k : ℕ} [NeZero M] [NeZero k] {T : ℕ}
    {X Z : Fin (M * k) → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    {F : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol (ring (M * k)) T F) :
    ∃ S, S ≤ (if M % 2 = 0 then 2 else 3) * T ∧
      IsProtocol (ring M) S (blockedMap (siteBlock M k) F) :=
  sorry

/-! ### BoundedPortPureOutput -/

/- TNLean `TNLean/Circuit/Channel/BoundedPortPureOutput.lean`
(`variable {B d N T : ℕ} [NeZero d] [NeZero N]`):
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPort_pure_output
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (ψ φ : (Fin N → Fin d) → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hOutput : Ψ (vecMulVec ψ (star ψ)) = vecMulVec φ (star φ)) :
    let k := Nat.clog d B
    let W := N * (1 + k + k)
    let V := registerEncoding (PortRegisters.wordCodeConfiguration
      (N := N) (PortRegisters.portWordCode d k))
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        ∃ η : (Fin A → Fin d) → ℂ,
          IsPhysicalPortUnitary ((PortRegisters.layout N k).append owner) (2 * k * T) U ∧
          discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
            appendEnvironmentInput W A d ∘ₗ
            PortRegisters.wordInitialization (PortRegisters.portWordCode d k) =
              PortRegisters.wordInitialization (PortRegisters.portWordCode d k) ∘ₗ Ψ ∧
          star η ⬝ᵥ η = 1 ∧ ∀ x e,
            ((appendMatrixSplit W A d U) *ᵥ
              (fixedEnvEmbedding (0 : Fin A → Fin d) *ᵥ (V *ᵥ ψ))) (x, e) =
                (V *ᵥ φ) x * η e
-/

/-- A dimension-bounded pure-to-pure ring protocol of depth `T` is realised by a unitary port
circuit of depth `2 ⌈log_d B⌉ T` on the register layout with appended environment wires: it
dilates the channel exactly, and sends the encoded input with the environment in `0` to the
encoded output times a unit environment vector. -/
theorem exists_physicalPort_pure_output {B d N T : ℕ} [NeZero d] [NeZero N]
    {Ψ : Module.End ℂ (Matrix (Config (Qudits (Fin N) d)) (Config (Qudits (Fin N) d)) ℂ)}
    (h : IsBoundedProtocol (ring N) B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (ψ φ : Config (Qudits (Fin N) d) → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hOutput : Ψ (vecMulVec ψ (star ψ)) = vecMulVec φ (star φ)) :
    let k := Nat.clog d B
    let W := N * (1 + k + k)
    let V := portWordEncoding N k d
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Config (Qudits (Fin (W + A)) d)) (Config (Qudits (Fin (W + A)) d)) ℂ,
        ∃ η : Config (Qudits (Fin A) d) → ℂ,
          IsUnitaryCircuit (portGeometry (appendLayout (portLayout N k) owner)) (2 * k * T) U ∧
          discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
            appendEnvironmentInput W A d ∘ₗ singleKrausMap V = singleKrausMap V ∘ₗ Ψ ∧
          star η ⬝ᵥ η = 1 ∧ ∀ x e,
            (U.submatrix (envSplit W A d).symm (envSplit W A d).symm *ᵥ
              (fixedEnvEmbedding (0 : Config (Qudits (Fin A) d)) *ᵥ (V *ᵥ ψ))) (x, e) =
                (V *ᵥ φ) x * η e :=
  sorry

/-! ### BoundedPortApproximateOutput -/

/- TNLean `TNLean/Circuit/Channel/BoundedPortApproximateOutput.lean`
(`variable {B d N T : ℕ} [NeZero d] [NeZero N]`):
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPort_approximate_output
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (ψ φ : (Fin N → Fin d) → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (hφ : star φ ⬝ᵥ φ = 1) {ε : ℝ}
    (herror : chainTraceNorm (Ψ (vecMulVec ψ (star ψ)) - vecMulVec φ (star φ)) ≤ ε) :
    let k := Nat.clog d B
    let W := N * (1 + k + k)
    let V := registerEncoding (PortRegisters.wordCodeConfiguration
      (N := N) (PortRegisters.portWordCode d k))
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        ∃ η : EuclideanSpace ℂ (Fin A → Fin d),
          IsPhysicalPortUnitary ((PortRegisters.layout N k).append owner) (2 * k * T) U ∧
          discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
            appendEnvironmentInput W A d ∘ₗ
            PortRegisters.wordInitialization (PortRegisters.portWordCode d k) =
              PortRegisters.wordInitialization (PortRegisters.portWordCode d k) ∘ₗ Ψ ∧
          ‖η‖ = 1 ∧
          ‖(WithLp.toLp 2 (((appendMatrixSplit W A d U) *ᵥ
              (fixedEnvEmbedding (0 : Fin A → Fin d) *ᵥ (V *ᵥ ψ))) -
                fun p => (V *ᵥ φ) p.1 * η p.2) :
            EuclideanSpace ℂ ((Fin W → Fin d) × (Fin A → Fin d)))‖ ≤ Real.sqrt (2 * ε)
-/

/-- The approximate version: a native output within trace-norm `ε` of the pure target gives a
dilated port output within Euclidean distance `√(2ε)` of the encoded target times a unit
environment vector. TNLean's `chainTraceNorm` (trace norm after reindexing to `Fin`) is
`rectangularTraceNorm`. -/
theorem exists_physicalPort_approximate_output {B d N T : ℕ} [NeZero d] [NeZero N]
    {Ψ : Module.End ℂ (Matrix (Config (Qudits (Fin N) d)) (Config (Qudits (Fin N) d)) ℂ)}
    (h : IsBoundedProtocol (ring N) B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (ψ φ : Config (Qudits (Fin N) d) → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (hφ : star φ ⬝ᵥ φ = 1) {ε : ℝ}
    (herror : rectangularTraceNorm (Ψ (vecMulVec ψ (star ψ)) - vecMulVec φ (star φ)) ≤ ε) :
    let k := Nat.clog d B
    let W := N * (1 + k + k)
    let V := portWordEncoding N k d
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Config (Qudits (Fin (W + A)) d)) (Config (Qudits (Fin (W + A)) d)) ℂ,
        ∃ η : EuclideanSpace ℂ (Config (Qudits (Fin A) d)),
          IsUnitaryCircuit (portGeometry (appendLayout (portLayout N k) owner)) (2 * k * T) U ∧
          discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
            appendEnvironmentInput W A d ∘ₗ singleKrausMap V = singleKrausMap V ∘ₗ Ψ ∧
          ‖η‖ = 1 ∧
          ‖(WithLp.toLp 2 ((U.submatrix (envSplit W A d).symm (envSplit W A d).symm *ᵥ
              (fixedEnvEmbedding (0 : Config (Qudits (Fin A) d)) *ᵥ (V *ᵥ ψ))) -
                fun p ↦ (V *ᵥ φ) p.1 * η p.2) :
            EuclideanSpace ℂ (Config (Qudits (Fin W) d) × Config (Qudits (Fin A) d)))‖ ≤
            Real.sqrt (2 * ε) :=
  sorry

end Inventory.D
