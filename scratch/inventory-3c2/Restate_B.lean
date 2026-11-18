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

/-! # Group B: registers and encodings (restated (c) items) -/

namespace Inventory.B

open Matrix ManyBody QuantumCircuit
open scoped ComplexOrder

variable {S : Type} [Fintype S] [DecidableEq S]

/-! ### Gaps -/

section Gaps

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- (c-supp, kept from TNLean `RegisterEncoding`) The isometry `|a⟩ ↦ |e a⟩` of an embedding
of bases. Not a core gap: a matrix primitive, used as the onsite family
`KrausFamily.single (registerEncoding e)`. -/
def registerEncoding (e : α ↪ β) : Matrix β α ℂ :=
  (1 : Matrix β β ℂ).submatrix id e

/-- (c-supp, kept from TNLean `RegisterEncoding`) The completed decoder: conjugation by the
adjoint isometry on the code space, with the off-code weight sent to the fixed matrix `ρ`
(`Matrix.supportCompletion`, already in QICLean). -/
noncomputable def registerDecoding (e : α ↪ β) (ρ : Matrix α α ℂ) :
    Matrix β β ℂ →ₗ[ℂ] Matrix α α ℂ :=
  Matrix.supportCompletion (KrausFamily.single (registerEncoding e)ᴴ).map
    (registerEncoding e * (registerEncoding e)ᴴ) ρ

/-- **Gap G4** (Kraus family of a channel): a Kraus family realising the completed decoder of a
density `ρ`, so that it can be an onsite family of a layer. -/
noncomputable def registerDecoder (e : α ↪ β) (ρ : Matrix α α ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) : KrausFamily β α :=
  sorry

/-- **Gap G4**, specification: the decoder family has the completed decoder as its map. -/
theorem map_registerDecoder (e : α ↪ β) (ρ : Matrix α α ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) : (registerDecoder e ρ hρ htr).map = registerDecoding e ρ :=
  sorry

/-- **Gap G4**, specification: the decoder family is trace-preserving (TNLean
`registerDecoding_isKrausCPTP`). -/
theorem isTP_registerDecoder (e : α ↪ β) (ρ : Matrix α α ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) : (registerDecoder e ρ hρ htr).IsTP :=
  sorry

end Gaps

section GapsLayers

variable {Γ : Geometry S} {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

/-- **Gap (onsite layer)**: the layer with no cells and the Kraus family `K s` at every site
(TNLean's `OnsiteChannel`, with the local dimension allowed to change). The core has
`Layer.ofCells` and `Layer.single` but no named layer without cells. -/
def onsiteLayer {X Y : S → Type} (K : ∀ s, KrausFamily (X s) (Y s)) : Layer Γ G X Y where
  cells := ∅
  pairwiseDisjoint := by simp
  gate b := absurd b.2 (Finset.notMem_empty _)
  onsite s := K s.1

/-- **Gap (one-layer circuit)**: the circuit made of the single layer `L`. -/
def layerCircuit {X Y : S → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (L : Layer Γ G X Y) : Circuit Γ G X Y :=
  .step L fun _ ↦ .done Y

variable {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- The product code of the sitewise embeddings `e s : X s ↪ Y s` as a one-layer onsite circuit
(TNLean `OnsiteChannel.encodeRegisters`, an (a) item: defined here only because the restated
statements mention it). -/
noncomputable def encodeCircuit (Γ : Geometry S) (e : ∀ s, X s ↪ Y s) :
    Circuit Γ KrausGate X Y :=
  layerCircuit (onsiteLayer fun s ↦ KrausFamily.single (registerEncoding (e s)))

/-- The product of the completed decoders as a one-layer onsite circuit (TNLean
`OnsiteChannel.decodeRegisters`, an (a) item; needs Gap G4). -/
noncomputable def decodeCircuit (Γ : Geometry S) (e : ∀ s, X s ↪ Y s)
    (ρ : ∀ s, Matrix (X s) (X s) ℂ) (hρ : ∀ s, (ρ s).PosSemidef)
    (htr : ∀ s, (ρ s).trace = 1) : Circuit Γ KrausGate Y X :=
  layerCircuit (onsiteLayer fun s ↦ registerDecoder (e s) (ρ s) (hρ s) (htr s))

end GapsLayers

section GapsPorts

variable {N : ℕ}

/-- **Gap (site permutation operator)**: the operator `|x⟩ ↦ |x ∘ π⁻¹⟩` permuting the sites of a
uniform system (TNLean `permOp`, verbatim). The core has no site-permutation matrix; it is the
permutation matrix of `ManyBody.siteConfigurationEquiv π (fun _ ↦ Equiv.refl _)`. -/
def sitePermOp {V : Type} [Fintype V] [DecidableEq V] {d : ℕ} (π : Equiv.Perm V) :
    Matrix (Config (Qudits V d)) (Config (Qudits V d)) ℂ :=
  of fun x y ↦ if y = x ∘ π then 1 else 0

/-- (statement data, TNLean `PortRegisters.layout` verbatim) One port followed by `k` data and
`k` scratch wires at each of the `N` sites, flattened to `Fin (N * (1 + k + k))`. -/
def portRegisterLayout (N k : ℕ) : PhysicalPortLayout N (N * (1 + k + k)) where
  site w := (finProdFinEquiv.symm w).1
  port :=
    { toFun := fun i ↦ finProdFinEquiv (i, (⟨0, by omega⟩ : Fin (1 + k + k)))
      inj' := fun i j h ↦ congrArg Prod.fst (finProdFinEquiv.injective h) }
  site_port i := by simp

/-- (statement data, TNLean `PortRegisters.data`) Data wire `t` of site `i`. -/
def dataWire {k : ℕ} (i : Fin N) (t : Fin k) : Fin (N * (1 + k + k)) :=
  finProdFinEquiv (i, ⟨1 + t.val, by omega⟩)

/-- (statement data, TNLean `PortRegisters.scratch`) Scratch wire `t` of site `i`. -/
def scratchWire {k : ℕ} (i : Fin N) (t : Fin k) : Fin (N * (1 + k + k)) :=
  finProdFinEquiv (i, ⟨1 + k + t.val, by omega⟩)

variable [NeZero N]

/-- (statement data, TNLean `PortMatching.perm`) The product of the swaps `(i, i+1)` over a set
`K` of pairwise disjoint ring bonds. The bonds are the cells of `ring N`. -/
noncomputable def matchingPerm (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint (ring N).cell) : Equiv.Perm (Fin N) :=
  K.noncommProd (fun i ↦ Equiv.swap i (i + 1)) (by sorry)

/-- (c-int, TNLean `PortRegisters.selection`) Data digit `t` at the sites of `K`, scratch digit
`t` elsewhere. -/
def selection {k : ℕ} (K : Finset (Fin N)) (t : Fin k) : Fin N ↪ Fin (N * (1 + k + k)) where
  toFun i := if i ∈ K then dataWire i t else scratchWire i t
  inj' := by sorry

/-- (c-int, TNLean `PortRegisters.routingPermutation` = `registerPermutation (selection K)
(PortMatching.perm K hK)`) The wire permutation applying the matching permutation to every
selected digit in turn. -/
noncomputable def routingPermutation {k : ℕ} (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint (ring N).cell) :
    Equiv.Perm (Fin (N * (1 + k + k))) :=
  (List.ofFn fun t : Fin k ↦ (matchingPerm K hK).viaEmbedding (selection K t)).prod

end GapsPorts

section GapsBlocking

variable {S' : Type} [Fintype S'] [DecidableEq S']

/-- **Gap G6** (blocking, region form): the configurations of the blocked system on a region
`D'` are those of the system on the preimage of `D'`. -/
noncomputable def blockRegionConfigEquiv (f : S → S') (X : S → Type) (D' : Finset S') :
    RegionConfig (blockSystem f X) D' ≃ RegionConfig X (Finset.univ.filter fun s ↦ f s ∈ D') :=
  sorry

end GapsBlocking

/-! ### 1. Completed-decoder retraction -/

/-
TNLean/Circuit/Channel/RegisterEncoding.lean
theorem registerDecoding_encoding (e : α ↪ β)
    (ρ X : Matrix α α ℂ) :
    registerDecoding e ρ (singleKrausMap (registerEncoding e) X) = X
-/

/-- Decoding after encoding is the identity on every matrix: the completed decoder of any `ρ`
is a left inverse of the map of the encoding family `KrausFamily.single (registerEncoding e)`. -/
theorem registerDecoding_encoding {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ↪ β) (ρ X : Matrix α α ℂ) :
    registerDecoding e ρ ((KrausFamily.single (registerEncoding e)).map X) = X :=
  sorry

/-! ### 2. Product-code retraction -/

/-
TNLean/Circuit/Channel/OnsiteRegisterEncoding.lean
theorem decodeRegisters_encodeRegisters (e : ι → (Fin m ↪ Fin q))
    (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    (decodeRegisters e ρ hρ htr).map ∘ₗ (encodeRegisters e).map = LinearMap.id
-/

/-- The onsite encoding layer followed by the onsite decoding layer is the identity channel on
the whole system. Stated for arbitrary systems `X`, `Y` on any geometry; TNLean's case is
`X = Qudits ι m`, `Y = Qudits ι q`. -/
theorem map_encodeCircuit_comp_decodeCircuit (Γ : Geometry S) {X Y : S → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (e : ∀ s, X s ↪ Y s) (ρ : ∀ s, Matrix (X s) (X s) ℂ) (hρ : ∀ s, (ρ s).PosSemidef)
    (htr : ∀ s, (ρ s).trace = 1) :
    ((encodeCircuit Γ e).comp (decodeCircuit Γ e ρ hρ htr)).map KrausGate.ev = LinearMap.id :=
  sorry

/-! ### 3 and 7. Encoding one layer -/

/-
TNLean/Circuit/Channel/OnsiteRegisterEncoding.lean
theorem encoded_map_encodeRegisters (Φ : OnsiteChannel m n ι)
    (e : ι → (Fin m ↪ Fin q)) (f : ι → (Fin n ↪ Fin r))
    (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    (Φ.encoded e f ρ hρ htr).map ∘ₗ (encodeRegisters e).map =
      (encodeRegisters f).map ∘ₗ Φ.map

TNLean/Circuit/Channel/EncodedChannelLayer.lean
theorem ChannelLayer.exists_encodedRegisters (L : ChannelLayer m N) (hN : 2 ≤ N) (hm : 0 < m)
    (c : Fin N → (Fin m ↪ Fin q))
    (ρ : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    ∃ L' : ChannelLayer q N, L'.bonds = L.bonds ∧
      L'.map ∘ₗ (OnsiteChannel.encodeRegisters c).map =
        (OnsiteChannel.encodeRegisters c).map ∘ₗ L.map
-/

/-- Every layer of trace-preserving plain gates and onsite families from `X` to `Y` has an
encoded layer from `X'` to `Y'` on the same cells, again trace-preserving, that intertwines with
the sitewise codes `e` and `f`. With no cells this is item 3 (an onsite channel); on the ring
with `X = Y` and `e = f` it is item 7 (a pair layer). Dropped `2 ≤ N` and `0 < m`: they only
served to extract two-site Kraus operators from TNLean's global ones, and core gates are
already local. -/
theorem Layer.exists_encoded {Γ : Geometry S} {X Y X' Y' : S → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    [∀ s, Fintype (X' s)] [∀ s, DecidableEq (X' s)] [∀ s, Fintype (Y' s)]
    [∀ s, DecidableEq (Y' s)]
    (L : Layer Γ KrausGate X Y) (hL : L.Forall KrausGate.ev IsTPLocal)
    (e : ∀ s, X s ↪ X' s) (f : ∀ s, Y s ↪ Y' s)
    (ρ : ∀ s, Matrix (X s) (X s) ℂ) (hρ : ∀ s, (ρ s).PosSemidef)
    (htr : ∀ s, (ρ s).trace = 1) :
    ∃ L' : Layer Γ KrausGate X' Y', L'.cells = L.cells ∧ L'.Forall KrausGate.ev IsTPLocal ∧
      ((encodeCircuit Γ e).comp (layerCircuit L')).map KrausGate.ev =
        ((layerCircuit L).comp (encodeCircuit Γ f)).map KrausGate.ev :=
  sorry

/-! ### 8. Encoding a dimension-bounded circuit into a constant alphabet (core theorem) -/

/-
TNLean/Circuit/Channel/EncodedChannelProtocol.lean
theorem IsDimensionBoundedLocalChannelProtocol.exists_fixedRegisterWord {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hN : 2 ≤ N) (hB : B ≤ q) :
    ∃ ops : List (FixedRegisterOperation q N),
      FixedRegisterOperation.wordDepth ops = T ∧
      FixedRegisterOperation.wordMap ops ∘ₗ
          (OnsiteChannel.encodeRegisters fun _ =>
            boundedAlphabetCode hB h.dimension_bounds.1.2).map =
        (OnsiteChannel.encodeRegisters fun _ => boundedAlphabetCode hB h.dimension_bounds.2.2).map
          ∘ₗ Ψ
-/

/-- **Core theorem.** A circuit of trace-preserving plain gates whose intermediate local
dimensions all lie in `[1, B]`, with `B ≤ q`, is simulated by a circuit on the constant
alphabet `Fin q`, of the same depth, trace-preserving, unbranched when the original is, which
intertwines exactly with any sitewise codes `e` of the input and `f` of the output. Proved by
structural induction from `Layer.exists_encoded`, with the fallback densities supplied by
`0 < card`. Dropped `2 ≤ N` (as in `Layer.exists_encoded`); the codes are arbitrary, TNLean's
`Fin.castLEEmb` being one choice. -/
theorem Circuit.exists_encoded_of_isDimBounded {Γ : Geometry S} {B q : ℕ} (hB : B ≤ q)
    {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)]
    [∀ s, DecidableEq (Z s)] (c : Circuit Γ KrausGate X Z)
    (hc : c.Forall KrausGate.ev IsTPLocal) (hdim : c.IsDimBounded B)
    (e : ∀ s, X s ↪ Fin q) (f : ∀ s, Z s ↪ Fin q) :
    ∃ c' : Circuit Γ KrausGate (Qudits S q) (Qudits S q),
      c'.Forall KrausGate.ev IsTPLocal ∧ (c.IsUnbranched → c'.IsUnbranched) ∧
        c'.depth = c.depth ∧
        ((encodeCircuit Γ e).comp c').map KrausGate.ev =
          (c.comp (encodeCircuit Γ f)).map KrausGate.ev :=
  sorry

/-- Item 8 in TNLean's shape, as a statement about the classes on the ring: every
dimension-bounded protocol of depth `≤ T` between uniform alphabets `Fin d` and `Fin e`, with
`B ≤ q`, is intertwined by the sitewise codes with a protocol of depth `≤ T` on `Fin q`. A
corollary of `Circuit.exists_encoded_of_isDimBounded`; `2 ≤ N` dropped. -/
theorem IsBoundedProtocol.exists_fixedRegisterWord {N : ℕ} [NeZero N] {B q d e T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsBoundedProtocol (ring N) B T (X := Qudits (Fin N) d) (Z := Qudits (Fin N) e) Ψ)
    (hB : B ≤ q) (cd : Fin d ↪ Fin q) (ce : Fin e ↪ Fin q) :
    ∃ Ψ' : Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ,
      IsProtocol (ring N) T (X := Qudits (Fin N) q) (Z := Qudits (Fin N) q) Ψ' ∧
      Ψ' ∘ₗ (encodeCircuit (ring N)
          (fun _ ↦ cd : ∀ s, Qudits (Fin N) d s ↪ Qudits (Fin N) q s)).map KrausGate.ev =
        (encodeCircuit (ring N)
          (fun _ ↦ ce : ∀ s, Qudits (Fin N) e s ↪ Qudits (Fin N) q s)).map KrausGate.ev ∘ₗ Ψ :=
  sorry

/-! ### 4 and 5. Routing over a ring matching -/

/-
TNLean/Circuit/Channel/PortRegisters.lean
theorem routingPermutation_isPhysicalPortUnitary (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) :
    IsPhysicalPortUnitary (d := d) (layout N k) k (permOp (routingPermutation K hK))
-/

/-- The routing permutation of a set `K` of pairwise disjoint ring bonds is the Kraus operator
of an unbranched unitary circuit of depth at most `k` on the port geometry of the register
layout. The ring bonds are the cells of `ring N`. -/
theorem routingPermutation_isUnitaryCircuit {N k d : ℕ} [NeZero N] (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint (ring N).cell) :
    IsUnitaryCircuit (portGeometry (portRegisterLayout N k)) k
      (X := Qudits (Fin (N * (1 + k + k))) d) (sitePermOp (routingPermutation K hK)) :=
  sorry

/-
TNLean/Circuit/Channel/PortRegisters.lean
theorem routingPermutation_pairData_site (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) {i : Fin N}
    (hi : i ∈ K) (hne : i ≠ i + 1) (a : Fin (k + k)) :
    (layout N k).site (routingPermutation K hK (pairData i (i + 1) hne a)) = i + 1
-/

/-- For a selected bond `{i, i+1}`, the routing permutation moves every data wire of site `i`
and of site `i+1` to a wire at site `i+1`. Dropped `i ≠ i + 1`: it only made TNLean's flattened
pair register `pairData` injective; the two data registers are quantified separately. -/
theorem site_routingPermutation_dataWire {N k : ℕ} [NeZero N] (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint (ring N).cell) {i : Fin N} (hi : i ∈ K)
    (t : Fin k) :
    (portRegisterLayout N k).site (routingPermutation K hK (dataWire i t)) = i + 1 ∧
      (portRegisterLayout N k).site (routingPermutation K hK (dataWire (i + 1) t)) = i + 1 :=
  sorry

/-! ### 6. Blocking commutes with placement -/

/-
TNLean/Circuit/Channel/NativeRegisterWires.lean
theorem dataOperator_embedOp (e : Fin s ↪ Fin N)
    (A : Matrix (Fin s → Fin (d ^ k)) (Fin s → Fin (d ^ k)) ℂ) :
    dataOperator (embedOp e A) = embedOp (selectedData e) (nativeMatrixEquiv s k d A)
-/

/-- Blocking the sites along `f : S → S'` commutes with placement: an operator placed on the
region `D'` of the blocked system is, read on the original sites, the placement on the preimage
of `D'` of the same operator read on the preimage. TNLean's statement is the case of the
blocking `Fin N × Fin k → Fin N` and `D'` the image of `e`, composed with two encodings that
the core makes separate: the basis relabelling `finFunctionFinEquiv` (`Fin k → Fin d ≃
Fin (d ^ k)`) and the placement of the data wires among the port and scratch wires (idle
sites). -/
theorem reindex_blockConfigEquiv_place {S' : Type} [Fintype S'] [DecidableEq S'] (f : S → S')
    {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (D' : Finset S')
    (K : Matrix (RegionConfig (blockSystem f X) D') (RegionConfig (blockSystem f X) D') ℂ) :
    reindex (blockConfigEquiv f X) (blockConfigEquiv f X) (place D' K) =
      place (Finset.univ.filter fun s ↦ f s ∈ D')
        (reindex (blockRegionConfigEquiv f X D') (blockRegionConfigEquiv f X D') K) :=
  sorry

end Inventory.B
