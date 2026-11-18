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

open Filter Topology

namespace Inventory.A

variable {S : Type} [Fintype S] [DecidableEq S]

/-! ### Gaps -/

open Fin.CommRing in
/-- Gap G4: TNLean's ring separation (`TNLean/Circuit/Geometry.lean`), verbatim: no point of `Y`
is within ring distance `s` of a point of `X`. -/
def IsSeparatedBy {N : ℕ} [NeZero N] (X Y : Finset (Fin N)) (s : ℕ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ m : ℤ, |m| ≤ s → y ≠ x + (m : Fin N)

/-- Gap G4: separation at ring distance `2T` makes the `T`-fold neighbourhoods in the ring
geometry disjoint (the core has no ring ball; TNLean's `neighbourhood X T` is
`(ring N).neighbourhood^[T] X`). -/
theorem disjoint_iterate_neighbourhood_of_isSeparatedBy {N : ℕ} [NeZero N]
    {X Y : Finset (Fin N)} {T : ℕ} (h : IsSeparatedBy X Y (2 * T)) :
    Disjoint ((ring N).neighbourhood^[T] X) ((ring N).neighbourhood^[T] Y) := sorry

/-- Gap G4: every bond of the ring has positive cost, so depth bounds light cones. -/
theorem ring_cost_pos {N : ℕ} [NeZero N] (b : (ring N).Cell) : 0 < (ring N).cost b :=
  Nat.one_pos

/-- An exact conversion: some protocol of depth at most `T` maps `ρ` to `σ`
(TNLean's `IsLocalChannelConversion` when `Γ = ring N`; a restriction of `Circuit`). -/
def IsConversion (Γ : Geometry S) (T : ℕ) {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (ρ : Matrix (Config X) (Config X) ℂ) (σ : Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ Φ, IsProtocol Γ T Φ ∧ Φ ρ = σ

/-- Gap G9/G3: the layer with no cells and the onsite families `k` (TNLean's `OnsiteChannel`);
the core has the notion but no named constructor. -/
def onsiteLayer (Γ : Geometry S) (G : Finset S → (S → Type) → (S → Type) → Type 1)
    [GateFamily G] {X Y : S → Type} (k : (s : S) → KrausFamily (X s) (Y s)) :
    Layer Γ G X Y where
  cells := ∅
  pairwiseDisjoint := by simp
  gate b := absurd b.2 (Finset.notMem_empty _)
  onsite s := k s.1

/-- Gap G11: the isometry `|x⟩ ↦ |e x⟩` of an embedding (TNLean's `registerEncoding`). -/
def embeddingMatrix {α β : Type} [DecidableEq β] (e : α ↪ β) : Matrix β α ℂ :=
  (1 : Matrix β β ℂ).submatrix id e

/-- Gap G5: a matrix of the system `X` as a matrix of the blocked system (TNLean's
`blockSites`, up to the core's configuration equivalence). -/
noncomputable def blockMatrix {S' : Type} (f : S → S') (X : S → Type)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    Matrix (Config (blockSystem f X)) (Config (blockSystem f X)) ℂ :=
  Matrix.reindex (blockConfigEquiv f X).symm (blockConfigEquiv f X).symm ρ

/-- Gap G5: a map on the blocked system as a map on the system (TNLean's
`nativeChannelReindex`, up to the core's configuration equivalence). -/
noncomputable def unblockMap {S' : Type} [Fintype S'] (f : S → S') (X : S → Type)
    [∀ s, Fintype (X s)]
    (Φ : Matrix (Config (blockSystem f X)) (Config (blockSystem f X)) ℂ →ₗ[ℂ]
      Matrix (Config (blockSystem f X)) (Config (blockSystem f X)) ℂ) :
    Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config X) (Config X) ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ (blockConfigEquiv f X) (blockConfigEquiv f X)).toLinearMap ∘ₗ
    Φ ∘ₗ (Matrix.reindexLinearEquiv ℂ ℂ (blockConfigEquiv f X).symm
      (blockConfigEquiv f X).symm).toLinearMap

/-- Gap G5: an exact conversion after blocking along `f` (TNLean's
`IsBlockedLocalChannelConversion` when `f = ringBlock M k`, `Γ' = ring M`). -/
def IsBlockedConversion {S' : Type} [Fintype S'] [DecidableEq S'] (f : S → S')
    (Γ' : Geometry S') (T : ℕ) {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    {Z : S' → Type} [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (ρ : Matrix (Config X) (Config X) ℂ) (σ : Matrix (Config Z) (Config Z) ℂ) : Prop :=
  IsConversion Γ' T (blockMatrix f X ρ) σ

/-- Gap G4/G5: the block of a site of the ring `Fin (M * k)` (TNLean's `siteBlock`). -/
def ringBlock (M k : ℕ) (i : Fin (M * k)) : Fin M := (finProdFinEquiv.symm i).1

/-- Gap G10: the wires of the site `i` of a port layout. -/
def siteWires {N W : ℕ} (P : PhysicalPortLayout N W) (i : Fin N) : Finset (Fin W) :=
  Finset.univ.filter fun w ↦ P.site w = i

/-- Gap G7: the trace norm on matrices over any finite index type (TNLean's
`chainTraceNorm`; QICLean's `Matrix.traceNorm` is only on `Fin D`). -/
noncomputable def cfgTraceNorm {α : Type} [Fintype α] (A : Matrix α α ℂ) : ℝ :=
  Matrix.traceNorm (Matrix.reindex (Fintype.equivFin α) (Fintype.equivFin α) A)

/-- An approximate conversion: some protocol of depth at most `T` maps `ρ` to within trace
distance `ε` of `σ` (TNLean's `IsApproxLocalChannelConversion` when `Γ = ring N`). -/
def IsApproxConversion (Γ : Geometry S) (T : ℕ) (ε : ℝ) {X Z : S → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (ρ : Matrix (Config X) (Config X) ℂ) (σ : Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ Φ, IsProtocol Γ T Φ ∧ cfgTraceNorm (Φ ρ - σ) ≤ ε

/-- Asymptotic conversion of families on rings of growing size: errors tending to `0` at
polylogarithmic depth (TNLean's `IsAsymptoticLocalChannelConversion`). -/
def IsAsymptoticConversion {d e : ℕ}
    (ρ : (N : ℕ) → Matrix (Config (Qudits (Fin N) d)) (Config (Qudits (Fin N) d)) ℂ)
    (σ : (N : ℕ) → Matrix (Config (Qudits (Fin N) e)) (Config (Qudits (Fin N) e)) ℂ) : Prop :=
  ∃ (k : ℕ) (C : ℝ) (ε : ℕ → ℝ), 0 ≤ C ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ᶠ (N : ℕ) in atTop, ∀ [NeZero N], ∃ T : ℕ,
      (T : ℝ) ≤ C * (1 + Real.log ((N : ℝ) + 1)) ^ k ∧
      IsApproxConversion (ring N) T (ε N) (ρ N) (σ N)

/-! ### 1. Light-cone factorization (Channel/Layer, Channel/Conversion) -/

section Factorization

variable {Γ : Geometry S} {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]
  (ev : Interpretation G)

/- TNLean/Circuit/Channel/Layer.lean
theorem BondChannelLayer.dual_mul [Fintype β] (L : BondChannelLayer d bond) {X Y : Finset ι}
    (hXY : Disjoint (bondNeighbourhood bond X) (bondNeighbourhood bond Y))
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y) :
    L.dual (A * B) = L.dual A * L.dual B
-/
/-- Gap G2: the Heisenberg picture of a layer with trace-preserving gates and onsite families is
multiplicative on operators whose one-layer light cones are disjoint. -/
theorem Layer.dual_mul_of_disjoint_lightCone {X Y : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (L : Layer Γ G X Y) (hL : L.Forall ev KrausFamily.IsTP) {R R' : Finset S}
    (hRR' : Disjoint (L.lightCone R) (L.lightCone R'))
    {A B : Matrix (Config Y) (Config Y) ℂ} (hA : A ∈ supportedOperators Y R)
    (hB : B ∈ supportedOperators Y R') :
    L.dual ev (A * B) = L.dual ev A * L.dual ev B := sorry

/- TNLean/Circuit/Channel/Conversion.lean
theorem OnsiteChannel.dual_mul (Φ : OnsiteChannel d e ι) {X Y : Finset ι} (hXY : Disjoint X Y)
    {A B : Matrix (ι → Fin e) (ι → Fin e) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) Y) :
        Φ.dual (A * B) = Φ.dual A * Φ.dual B
-/
/-- The Heisenberg picture of a layer with no cells and trace-preserving onsite families is
multiplicative on operators with disjoint supports (the case `cells = ∅` of the previous
theorem, whose light cone is the region itself). -/
theorem Layer.dual_mul_of_cells_eq_empty {X Y : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (L : Layer Γ G X Y) (hcells : L.cells = ∅) (hL : L.Forall ev KrausFamily.IsTP)
    {R R' : Finset S} (hRR' : Disjoint R R')
    {A B : Matrix (Config Y) (Config Y) ℂ} (hA : A ∈ supportedOperators Y R)
    (hB : B ∈ supportedOperators Y R') :
    L.dual ev (A * B) = L.dual ev A * L.dual ev B := sorry

/- TNLean/Circuit/Channel/Layer.lean
theorem channelCircuitDual_mul_of_disjoint_lightCone [Fintype β]
    (Ls : List (BondChannelLayer d bond))
    {X Y : Finset ι} (hXY : Disjoint (lightCone bond X Ls.length) (lightCone bond Y Ls.length))
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y) :
    channelCircuitDual Ls (A * B) = channelCircuitDual Ls A * channelCircuitDual Ls B
-/
/-- Gap G2: the Heisenberg picture of an unbranched circuit with trace-preserving gates and
onsite families is multiplicative on operators whose backward light cones are disjoint. -/
theorem Circuit.dual_mul_of_disjoint_lightCone {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (c : Circuit Γ G X Z) (hc : c.IsUnbranched) (hTP : c.Forall ev KrausFamily.IsTP)
    {R R' : Finset S} (hRR' : Disjoint (c.lightCone R) (c.lightCone R'))
    {A B : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R)
    (hB : B ∈ supportedOperators Z R') :
    c.dual ev (A * B) = c.dual ev A * c.dual ev B := sorry

/-- **The light-cone factorization** (gaps G1, G2, G3). For an unbranched circuit with
trace-preserving gates and onsite families, applied to a product input `⊗ₛ σₛ` with
`tr σₛ = 1`, the expectations of operators with disjoint backward light cones factorize.
This is the one core theorem behind every `trace_mul_mul_eq` item of this group. -/
theorem Circuit.trace_map_prodOp_mul_mul {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (c : Circuit Γ G X Z) (hc : c.IsUnbranched) (hTP : c.Forall ev KrausFamily.IsTP)
    (σ : (s : S) → Matrix (X s) (X s) ℂ) (hσ : ∀ s, trace (σ s) = 1)
    {R R' : Finset S} (hRR' : Disjoint (c.lightCone R) (c.lightCone R'))
    {A B : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R)
    (hB : B ∈ supportedOperators Z R') :
    trace (c.map ev (prodOp σ) * (A * B)) =
      trace (c.map ev (prodOp σ) * A) * trace (c.map ev (prodOp σ) * B) := sorry

end Factorization

section ProtocolFactorization

/- TNLean/Circuit/Channel/Layer.lean
def IsBondChannelPreparedInDepth (T : ℕ) (ρ : Matrix (ι → Fin d) (ι → Fin d) ℂ) : Prop :=
  ∃ Ls : List (BondChannelLayer d bond), Ls.length = T ∧
    ∃ σ : ι → Matrix (Fin d) (Fin d) ℂ, (∀ i, (σ i).PosSemidef ∧ trace (σ i) = 1) ∧
      ρ = channelCircuitMap Ls (rectKronecker σ)
theorem IsBondChannelPreparedInDepth.trace_mul_mul_eq [Fintype β] {T : ℕ}
    {ρ : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hρ : IsBondChannelPreparedInDepth bond T ρ)
    {X Y : Finset ι} (hXY : Disjoint (lightCone bond X T) (lightCone bond Y T))
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y) :
    trace (ρ * (A * B)) = trace (ρ * A) * trace (ρ * B)
-/
/-- The factorization for an exact conversion of depth `T` from a product input, on any
geometry of positive costs: expectations factorize when the `T`-fold neighbourhoods are
disjoint. Changes: `Ls.length = T` becomes depth `≤ T`; positivity of `σᵢ` is dropped (only
`tr σᵢ = 1` is used, as in `trace_mul_mul_eq_of_isLocalChannelConversion`); `hpos` is the
core form of "every bond costs one". -/
theorem IsConversion.trace_mul_mul_eq {Γ : Geometry S} [Fintype Γ.Cell]
    (hpos : ∀ b, 0 < Γ.cost b) {T : ℕ} {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    {σ₀ : (s : S) → Matrix (X s) (X s) ℂ} (hσ₀ : ∀ s, trace (σ₀ s) = 1)
    {σ : Matrix (Config Z) (Config Z) ℂ} (h : IsConversion Γ T (prodOp σ₀) σ)
    {R R' : Finset S}
    (hRR' : Disjoint (Γ.neighbourhood^[T] R) (Γ.neighbourhood^[T] R'))
    {A B : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R)
    (hB : B ∈ supportedOperators Z R') :
    trace (σ * (A * B)) = trace (σ * A) * trace (σ * B) := sorry

end ProtocolFactorization

/-! ### 2. Ring corollaries (gap G4) -/

section Ring

variable {N : ℕ} [NeZero N]

/- TNLean/Circuit/Channel/Conversion.lean
theorem IsLocalChannelProtocol.exists_dual {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ] Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsLocalChannelProtocol T Ψ) :
    ∃ Ψ' : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ] Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ,
      (∀ ρ A, trace (Ψ ρ * A) = trace (ρ * Ψ' A)) ∧
      (∀ X : Finset (Fin N), ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
        Ψ' A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (neighbourhood X T)) ∧
      (∀ X Y : Finset (Fin N), Disjoint (neighbourhood X T) (neighbourhood Y T) →
        ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
            ∀ B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) Y,
          Ψ' (A * B) = Ψ' A * Ψ' B)
TNLean/Circuit/Channel/Layer.lean (ring instances, same content):
theorem ChannelLayer.dual_mul ..., theorem channelCircuitDual_mul ...
-/
/-- A protocol of depth at most `T` on a geometry of positive costs has a Heisenberg picture
(G1 duality), mapping operators on `R` to operators on the `T`-fold neighbourhood of `R`, and
multiplicative on operators with disjoint `T`-fold neighbourhoods (G2). TNLean's ring statement
is the case `Γ = ring N` (`ring_cost_pos`); the ring `dual_mul` items are its one-layer and
`T`-layer instances. -/
theorem IsProtocol.exists_dual {Γ : Geometry S} [Fintype Γ.Cell] (hpos : ∀ b, 0 < Γ.cost b)
    {T : ℕ} {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    {Ψ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Ψ) :
    ∃ Ψ' : Matrix (Config Z) (Config Z) ℂ →ₗ[ℂ] Matrix (Config X) (Config X) ℂ,
      (∀ ρ A, trace (Ψ ρ * A) = trace (ρ * Ψ' A)) ∧
      (∀ R : Finset S, ∀ A ∈ supportedOperators Z R,
        Ψ' A ∈ supportedOperators X (Γ.neighbourhood^[T] R)) ∧
      (∀ R R' : Finset S, Disjoint (Γ.neighbourhood^[T] R) (Γ.neighbourhood^[T] R') →
        ∀ A ∈ supportedOperators Z R, ∀ B ∈ supportedOperators Z R',
          Ψ' (A * B) = Ψ' A * Ψ' B) := sorry

/- TNLean/Circuit/Channel/Conversion.lean
theorem trace_mul_mul_eq_of_isLocalChannelConversion {d' T : ℕ}
    {σ₀ : Fin N → Matrix (Fin d) (Fin d) ℂ} (hσ₀ : ∀ i, trace (σ₀ i) = 1)
    {σ : Matrix (Fin N → Fin d') (Fin N → Fin d') ℂ}
    (h : IsLocalChannelConversion T (finKronecker σ₀) σ)
    {X Y : Finset (Fin N)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin N → Fin d') (Fin N → Fin d') ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d') X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d') Y) :
    trace (σ * (A * B)) = trace (σ * A) * trace (σ * B)
TNLean/Circuit/Channel/Layer.lean (the case d' = d, with PosSemidef σᵢ):
theorem trace_mul_mul_eq_of_isChannelPreparedInDepth {T : ℕ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ} (hρ : IsChannelPreparedInDepth T ρ)
    {X Y : Finset (Fin N)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y) :
    trace (ρ * (A * B)) = trace (ρ * A) * trace (ρ * B)
-/
/-- The ring factorization: for an exact conversion of depth `T` on the ring from a product
input with unit-trace factors, expectations factorize at ring distance greater than `2T`.
Both TNLean items are this statement (`finKronecker σ₀` is `prodOp σ₀`); the intermediate
systems of the core protocol need not be uniform. -/
theorem trace_mul_mul_eq_of_isConversion_ring {d d' T : ℕ}
    {σ₀ : Fin N → Matrix (Fin d) (Fin d) ℂ} (hσ₀ : ∀ i, trace (σ₀ i) = 1)
    {σ : Matrix (Fin N → Fin d') (Fin N → Fin d') ℂ}
    (h : IsConversion (ring N) T (X := Qudits (Fin N) d) (Z := Qudits (Fin N) d')
      (prodOp σ₀) σ)
    {X Y : Finset (Fin N)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin N → Fin d') (Fin N → Fin d') ℂ}
    (hA : A ∈ supportedOperators (Qudits (Fin N) d') X)
    (hB : B ∈ supportedOperators (Qudits (Fin N) d') Y) :
    trace (σ * (A * B)) = trace (σ * A) * trace (σ * B) := sorry

end Ring

/-! ### 3. Blocking (Channel/SiteBlocking; gaps G4, G5) -/

section Blocking

/- TNLean/Circuit/Channel/SiteBlocking.lean
theorem preimage_siteBlock_neighbourhood_subset [NeZero M] [NeZero k] (X : Finset (Fin M))
    (r : ℕ) :
    (Finset.univ.filter fun p ↦ siteBlock (k := k) p ∈ neighbourhood X r) ⊆
      neighbourhood (Finset.univ.filter fun p ↦ siteBlock (k := k) p ∈ X) (k * r)
-/
/-- The fine sites of the `r`-fold ring neighbourhood of a set of blocks lie in the `k r`-fold
ring neighbourhood of the fine sites of those blocks. -/
theorem preimage_ringBlock_neighbourhood_subset {M k : ℕ} [NeZero M] [NeZero k]
    (R : Finset (Fin M)) (r : ℕ) :
    (Finset.univ.filter fun p ↦ ringBlock M k p ∈ (ring M).neighbourhood^[r] R) ⊆
      (ring (M * k)).neighbourhood^[k * r]
        (Finset.univ.filter fun p ↦ ringBlock M k p ∈ R) := sorry

/- TNLean/Circuit/Channel/SiteBlocking.lean
theorem IsLocalChannelProtocol.exists_dual_comp_blockSites [NeZero M] [NeZero d] {T : ℕ}
    {Ψ : Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ →ₗ[ℂ]
      Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsLocalChannelProtocol T Ψ) :
    ∃ Ψ' : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ,
      (∀ ρ A, trace (Ψ (blockSites M k d ρ) * A) = trace (ρ * Ψ' A)) ∧
      (∀ X : Finset (Fin M), ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
        Ψ' A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
          (Finset.univ.filter fun p ↦ siteBlock p ∈ neighbourhood X T)) ∧
      (∀ X Y : Finset (Fin M), Disjoint (neighbourhood X T) (neighbourhood Y T) →
        ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
            ∀ B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) Y,
          Ψ' (A * B) = Ψ' A * Ψ' B)
-/
/-- A protocol on the blocked system, precomposed with blocking, has a Heisenberg picture on the
fine system: dual, supported on the fibres of the `T`-fold neighbourhood, multiplicative on
disjoint neighbourhoods. Stated for any blocking `f` and coarse geometry `Γ'` of positive
costs; TNLean's is `f = ringBlock M k`, `Γ' = ring M`. `[NeZero d]` is dropped: it served the
digit encoding `Fin (d ^ k)`, which `blockSystem` makes unnecessary. -/
theorem IsProtocol.exists_dual_comp_block {S' : Type} [Fintype S'] [DecidableEq S']
    (f : S → S') {Γ' : Geometry S'} [Fintype Γ'.Cell] (hpos : ∀ b, 0 < Γ'.cost b) {T : ℕ}
    {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    {Z : S' → Type} [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    {Ψ : Matrix (Config (blockSystem f X)) (Config (blockSystem f X)) ℂ →ₗ[ℂ]
      Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ' T Ψ) :
    ∃ Ψ' : Matrix (Config Z) (Config Z) ℂ →ₗ[ℂ] Matrix (Config X) (Config X) ℂ,
      (∀ ρ A, trace (Ψ (blockMatrix f X ρ) * A) = trace (ρ * Ψ' A)) ∧
      (∀ R : Finset S', ∀ A ∈ supportedOperators Z R,
        Ψ' A ∈ supportedOperators X
          (Finset.univ.filter fun s ↦ f s ∈ Γ'.neighbourhood^[T] R)) ∧
      (∀ R R' : Finset S', Disjoint (Γ'.neighbourhood^[T] R) (Γ'.neighbourhood^[T] R') →
        ∀ A ∈ supportedOperators Z R, ∀ B ∈ supportedOperators Z R',
          Ψ' (A * B) = Ψ' A * Ψ' B) := sorry

variable {M k : ℕ} [NeZero M] [NeZero k]

/- TNLean/Circuit/Channel/SiteBlocking.lean
theorem IsBlockedLocalChannelConversion.exists_dual [NeZero d] {T : ℕ}
    {ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedLocalChannelConversion k T ρ σ) :
    ∃ Ψ' : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ,
      (∀ A, trace (σ * A) = trace (ρ * Ψ' A)) ∧
      (∀ X : Finset (Fin M), ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
        Ψ' A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
          (neighbourhood (Finset.univ.filter fun p ↦ siteBlock (k := k) p ∈ X) (k * T))) ∧
      (∀ X Y : Finset (Fin M), Disjoint (neighbourhood X T) (neighbourhood Y T) →
        ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
            ∀ B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) Y,
          Ψ' (A * B) = Ψ' A * Ψ' B)
-/
/-- A blocked conversion of depth `T` on the ring of blocks has a Heisenberg picture whose light
cone, on the fine ring, has radius `k T`. `[NeZero d]` is dropped (digit encoding). -/
theorem IsBlockedConversion.exists_dual_ring {d e T : ℕ}
    {ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedConversion (ringBlock M k) (ring M) T (X := Qudits (Fin (M * k)) d)
      (Z := Qudits (Fin M) e) ρ σ) :
    ∃ Ψ' : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ,
      (∀ A, trace (σ * A) = trace (ρ * Ψ' A)) ∧
      (∀ R : Finset (Fin M), ∀ A ∈ supportedOperators (Qudits (Fin M) e) R,
        Ψ' A ∈ supportedOperators (Qudits (Fin (M * k)) d)
          ((ring (M * k)).neighbourhood^[k * T]
            (Finset.univ.filter fun p ↦ ringBlock M k p ∈ R))) ∧
      (∀ R R' : Finset (Fin M),
        Disjoint ((ring M).neighbourhood^[T] R) ((ring M).neighbourhood^[T] R') →
        ∀ A ∈ supportedOperators (Qudits (Fin M) e) R,
          ∀ B ∈ supportedOperators (Qudits (Fin M) e) R',
          Ψ' (A * B) = Ψ' A * Ψ' B) := sorry

/- TNLean/Circuit/Channel/SiteBlocking.lean
theorem trace_mul_mul_eq_of_isBlockedLocalChannelConversion [NeZero M] [NeZero k] {T : ℕ}
    {σ₀ : Fin (M * k) → Matrix (Fin d) (Fin d) ℂ} (hσ₀ : ∀ i, trace (σ₀ i) = 1)
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedLocalChannelConversion k T (finKronecker σ₀) σ)
    {X Y : Finset (Fin M)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) Y) :
    trace (σ * (A * B)) = trace (σ * A) * trace (σ * B)
-/
/-- The blocked ring factorization: a blocked conversion of depth `T` from a fine product input
with unit-trace factors factorizes at block distance greater than `2T` (the blocked input is a
product over blocks, then `trace_mul_mul_eq_of_isConversion_ring`'s argument applies). -/
theorem trace_mul_mul_eq_of_isBlockedConversion_ring {d e T : ℕ}
    {σ₀ : Fin (M * k) → Matrix (Fin d) (Fin d) ℂ} (hσ₀ : ∀ i, trace (σ₀ i) = 1)
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedConversion (ringBlock M k) (ring M) T (X := Qudits (Fin (M * k)) d)
      (Z := Qudits (Fin M) e) (prodOp σ₀) σ)
    {X Y : Finset (Fin M)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (hA : A ∈ supportedOperators (Qudits (Fin M) e) X)
    (hB : B ∈ supportedOperators (Qudits (Fin M) e) Y) :
    trace (σ * (A * B)) = trace (σ * A) * trace (σ * B) := sorry

end Blocking

/-! ### 4. Whole-site channels on ports (Channel/WholeSiteChannels; gaps G5, G9, G10) -/

section WholeSite

variable {N W d : ℕ} [NeZero N]

/- TNLean/Circuit/Channel/WholeSiteChannels.lean
theorem wholeSite_onsiteChannel (hd : 0 < d)
    (Φ : OnsiteChannel (d ^ (1 + k + k)) (d ^ (1 + k + k)) (Fin N)) :
    IsPhysicalPortProtocol (layout N k) 0
      (nativeChannelReindex N (1 + k + k) d Φ.map)
-/
/-- An onsite channel on the system blocked by sites (basis at site `i`: the configurations of
its wires), read on the wires, is a depth-0 port protocol: each site's family is a gate on the
cost-0 cell of that site's wires. Changes: any layout `P` instead of `layout N k`; `hd` is
dropped (it served the digit encoding `Fin (d ^ (1 + k + k))`). -/
theorem wholeSite_onsiteChannel (P : PhysicalPortLayout N W)
    (k : (i : Fin N) → KrausFamily (blockSystem P.site (Qudits (Fin W) d) i)
      (blockSystem P.site (Qudits (Fin W) d) i)) (hk : ∀ i, (k i).IsTP) :
    IsProtocol (portGeometry P) 0
      (unblockMap P.site (Qudits (Fin W) d)
        ((onsiteLayer (ring N) KrausGate k).krausFamily KrausGate.ev).map) := sorry

/- TNLean/Circuit/Channel/WholeSiteChannels.lean
theorem wholeSite_local (hd : 0 < d) (e : Fin s ↪ Fin N)
    (Φ : Module.End ℂ (Matrix (Fin s → Fin (d ^ (1 + k + k)))
      (Fin s → Fin (d ^ (1 + k + k))) ℂ))
    (hΦ : IsKrausCPTP Φ) (i : Fin N) (he : ∀ a, e a = i) :
    IsPhysicalPortProtocol (layout N k) 0
      (nativeChannelReindex N (1 + k + k) d (registerChannelLift e Φ))
-/
/-- A channel on the block of one site `i` (identity on the other blocks), read on the wires, is
a depth-0 port protocol. Changes: `IsKrausCPTP Φ` is given as a trace-preserving Kraus family
`K` of `Φ`; the register embedding `e` with all registers at `i` becomes the site `i` itself
(`e` is injective, so it names at most that one block); `hd` is dropped (digit encoding). -/
theorem wholeSite_local (P : PhysicalPortLayout N W) (i : Fin N)
    (K : KrausFamily (blockSystem P.site (Qudits (Fin W) d) i)
      (blockSystem P.site (Qudits (Fin W) d) i)) (hK : K.IsTP) :
    IsProtocol (portGeometry P) 0
      (unblockMap P.site (Qudits (Fin W) d)
        ((onsiteLayer (ring N) KrausGate
          (Function.update (fun j ↦ KrausFamily.single 1) i K)).krausFamily
            KrausGate.ev).map) := sorry

end WholeSite

/-! ### 5. Encoding (Channel/DataInitialization; gap G11) -/

section Encoding

/- TNLean/Circuit/Channel/DataInitialization.lean
theorem wordInitialization_data_eq_physicalEncoding (c : Fin d ↪ Fin (d ^ k)) :
    wordInitialization (N := N) (dataWordCode c) =
      physicalEncoding (OnsiteChannel.encodeRegisters (fun _ : Fin N => c)).map ∘ₗ
        zeroDataReferencePrep
-/
/-- Two onsite layers of isometries of embeddings `e₁ s`, then `e₂ s`, have the map of one onsite
layer of the composite embeddings. TNLean's item is the instance `e₁` = attach the zero
reference, `e₂` = place the data code on the data wires, composite = `dataWordCode c`, on the
system blocked by sites; the identity `dataWordCode c = prep.trans enc` is a coordinate
identity the core does not need, and the wire picture is `unblockMap` of this one. -/
theorem map_onsiteEmbedding_comp {Γ : Geometry S} {X Y Z : S → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (e₁ : (s : S) → X s ↪ Y s) (e₂ : (s : S) → Y s ↪ Z s) :
    (Circuit.step (onsiteLayer Γ KrausGate fun s ↦ KrausFamily.single (embeddingMatrix (e₁ s)))
      fun _ ↦ Circuit.step
        (onsiteLayer Γ KrausGate fun s ↦ KrausFamily.single (embeddingMatrix (e₂ s)))
        fun _ ↦ Circuit.done Z).map KrausGate.ev =
    (Circuit.step (onsiteLayer Γ KrausGate fun s ↦
        KrausFamily.single (embeddingMatrix ((e₁ s).trans (e₂ s))))
      fun _ ↦ Circuit.done Z).map KrausGate.ev := sorry

end Encoding

/-! ### 6. Approximate and asymptotic conversion (gap G7) -/

section Approximate

/- TNLean/Circuit/Channel/ApproximateConversion.lean
theorem IsApproxLocalChannelConversion.trans {T₁ T₂ : ℕ} {ε₁ ε₂ : ℝ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {τ : Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (h₁ : IsApproxLocalChannelConversion T₁ ε₁ ρ σ)
    (h₂ : IsApproxLocalChannelConversion T₂ ε₂ σ τ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    IsApproxLocalChannelConversion (T₁ + T₂) (ε₁ + ε₂) ρ τ
-/
/-- Approximate conversions compose with additive depths and errors, for Hermitian inputs
(trace-norm contractivity of channels on Hermitian matrices, Wolf Thm 8.16). Stated on any
geometry and any systems; TNLean's is `Γ = ring N` with uniform systems. -/
theorem IsApproxConversion.trans {Γ : Geometry S} {T₁ T₂ : ℕ} {ε₁ ε₂ : ℝ}
    {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    {ρ : Matrix (Config X) (Config X) ℂ} {σ : Matrix (Config Y) (Config Y) ℂ}
    {τ : Matrix (Config Z) (Config Z) ℂ}
    (h₁ : IsApproxConversion Γ T₁ ε₁ ρ σ) (h₂ : IsApproxConversion Γ T₂ ε₂ σ τ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    IsApproxConversion Γ (T₁ + T₂) (ε₁ + ε₂) ρ τ := sorry

/- TNLean/Circuit/Channel/AsymptoticConversion.lean
theorem IsAsymptoticLocalChannelConversion.trans
    {ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : (N : ℕ) → Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {τ : (N : ℕ) → Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (h₁ : IsAsymptoticLocalChannelConversion ρ σ)
    (h₂ : IsAsymptoticLocalChannelConversion σ τ)
    (hρ : ∀ᶠ N in atTop, (ρ N).IsHermitian)
    (hσ : ∀ᶠ N in atTop, (σ N).IsHermitian) :
    IsAsymptoticLocalChannelConversion ρ τ
-/
/-- Asymptotic conversion is transitive on eventually Hermitian families (from
`IsApproxConversion.trans` and polylog arithmetic). -/
theorem IsAsymptoticConversion.trans {d e f : ℕ}
    {ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : (N : ℕ) → Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {τ : (N : ℕ) → Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (h₁ : IsAsymptoticConversion ρ σ) (h₂ : IsAsymptoticConversion σ τ)
    (hρ : ∀ᶠ N in atTop, (ρ N).IsHermitian) (hσ : ∀ᶠ N in atTop, (σ N).IsHermitian) :
    IsAsymptoticConversion ρ τ := sorry

end Approximate

/-! ### 7. The dimension-bounded class (Channel/DimensionBoundedConversion; gap G6)

TNLean's inductive `IsDimensionBoundedLocalChannelProtocol B T Ψ` is `IsBoundedProtocol (ring N)
B T Ψ` of the Prelude; its lemmas are stated once for any geometry. -/

section Bounded

variable {Γ : Geometry S} {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]

/- TNLean/Circuit/Channel/DimensionBoundedConversion.lean
theorem IsDimensionBoundedLocalChannelProtocol.dimension_bounds ... :
    (0 < d ∧ d ≤ B) ∧ (0 < e ∧ e ≤ B)
-/
/-- The input and output local dimensions of a bounded protocol lie in `(0, B]`. -/
theorem IsBoundedProtocol.dimension_bounds {B T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol Γ B T Φ) :
    (∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B) ∧
      (∀ s, 0 < Nat.card (Z s) ∧ Nat.card (Z s) ≤ B) := sorry

/- TNLean/Circuit/Channel/DimensionBoundedConversion.lean
theorem IsDimensionBoundedLocalChannelProtocol.mono_bound (hBC : B ≤ C)
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) :
    IsDimensionBoundedLocalChannelProtocol C T Ψ
-/
/-- A larger budget keeps a bounded protocol bounded. -/
theorem IsBoundedProtocol.mono_bound {B C T : ℕ} (hBC : B ≤ C)
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol Γ B T Φ) : IsBoundedProtocol Γ C T Φ := sorry

/- TNLean/Circuit/Channel/DimensionBoundedConversion.lean
theorem IsDimensionBoundedLocalChannelProtocol.comp
    (hΦ : IsDimensionBoundedLocalChannelProtocol B T Φ)
    (hΨ : IsDimensionBoundedLocalChannelProtocol B S Ψ) :
    IsDimensionBoundedLocalChannelProtocol B (T + S) (Ψ ∘ₗ Φ)
-/
/-- Bounded protocols compose with the same budget and additive depth. -/
theorem IsBoundedProtocol.comp {B T T' : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Y) (Config Y) ℂ}
    {Ψ : Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (hΦ : IsBoundedProtocol Γ B T Φ) (hΨ : IsBoundedProtocol Γ B T' Ψ) :
    IsBoundedProtocol Γ B (T + T') (Ψ ∘ₗ Φ) := sorry

/- TNLean/Circuit/Channel/DimensionBoundedConversion.lean
theorem IsLocalChannelProtocol.exists_dimension_bound {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsLocalChannelProtocol T Ψ) (hd : 0 < d) :
    ∃ B, IsDimensionBoundedLocalChannelProtocol B T Ψ
-/
/-- Every protocol with nonempty input sites is bounded by some budget (TP families cannot reach
an empty site; finitely many intermediate systems). `hd : 0 < d` becomes `Nonempty (X s)`. -/
theorem IsProtocol.exists_dimension_bound {T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Φ) (hX : ∀ s, Nonempty (X s)) : ∃ B, IsBoundedProtocol Γ B T Φ := sorry

end Bounded

end Inventory.A
