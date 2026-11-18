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
