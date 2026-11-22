/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausMap.KrausFamilyAncilla
import QICLean.Circuit.Model.Protocol

/-!
# Channel circuits and onsite channels

Two restrictions of protocols recur in local channel conversions. A *channel circuit* is a
sequence of layers of trace-preserving gates on one system, each gate a channel on its cell; it
is unbranched, keeps the local bases, and has depth at most the number of its layers that use a
cell of positive cost. An *onsite channel* is a layer with no cells: the product `⊗ₛ Φₛ` of a
channel `Φₛ` at every site, which may change the local bases, as attaching an ancilla
(`KrausFamily.attach`) or discarding one (`KrausFamily.traceRight`) does. Both are protocols:
a layer of depth `t` is a protocol of depth `t` (`IsProtocol.ofLayer`), a sequence of layers is
a protocol of the sum of the depths (`IsProtocol.seq`), and an onsite channel is a protocol of
depth `0` (`IsProtocol.ofOnsite`). A local channel conversion of depth `T`, which alternates
onsite channels with layers of channels on cells, is therefore an exact conversion in the sense
of `IsConversion`, by composition of protocols.

An onsite channel maps a product `⊗ₛ σₛ` to `⊗ₛ Φₛ(σₛ)`, and its Heisenberg picture keeps the
support of an operator, since its backward light cone of a region is the region itself
(`Layer.lightCone_ofOnsite`). A circuit with one branch, such as a circuit of unitary gates,
has as map the conjugation by its Kraus operator (`Circuit.map_eq_of_subsingleton`).

## Main results

* `QuantumCircuit.Circuit.map_eq_of_subsingleton` — the map of a circuit with one branch.
* `QuantumCircuit.Circuit.map_seq_cons` — the map of a sequence of layers, layer by layer.
* `QuantumCircuit.Circuit.depth_seq_le_length` — a sequence of layers has depth at most its
  length.
* `QuantumCircuit.Layer.lightCone_ofOnsite` — an onsite layer does not spread supports.
* `QuantumCircuit.Circuit.map_ofLayer_ofOnsite`,
  `QuantumCircuit.Circuit.map_ofLayer_ofOnsite_piKronecker` — the map of an onsite layer is the
  product channel, which sends product operators to product operators.
* `QuantumCircuit.IsProtocol.ofLayer`, `QuantumCircuit.IsProtocol.seq`,
  `QuantumCircuit.IsProtocol.ofOnsite` — layers, channel circuits and onsite channels are
  protocols.
* `QuantumCircuit.IsConversion.ofOnsite_seq` — attaching ancillas, running a channel circuit
  and discarding the ancillas converts the input into the output in the depth of the circuit.

The declarations restate, as restrictions of `Circuit`, the channel circuits and onsite channels
of `TNLean/Circuit/Channel/Layer.lean` (`BondChannelLayer`, `channelCircuitMap`,
`channelCircuitMap_map_toChannelLayer`) and `TNLean/Circuit/Channel/Conversion.lean`
(`OnsiteChannel`, `map_rectKronecker`, `dual_mem_supportedOperators`, `dual_mul`,
`IsLocalChannelProtocol.channelCircuitMap_comp`, `isLocalChannelConversion_circuit`) at commit
`414a18fb882d1b8c41c8d28d4b0c66d0d6ef2a2e` (Apache-2.0). The changes: any geometry and any
finite bases at the sites instead of the ring with one dimension at every site; the onsite
channels are layers without cells, so the light cone and the multiplicativity of their
Heisenberg pictures are those of layers (`Layer.dual_mem_supportedOperators_lightCone`,
`Layer.dual_mul_of_disjoint_lightCone`); the attachment and discard of ancillas are Kraus
families at one site.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, main text, paragraph "Quantum circuits and
  LOCC": the circuits `V' = U_ℓ V_ℓ ⋯ U_1 V_1 U_0` with local operations `U_n` on each site and
  its ancillas between the layers `V_n`, here with channels in place of unitaries.
* Malz, Styliaris, Wei and Cirac, arXiv:2307.01696, main text before Theorem 1 (layers of a
  local circuit), with channels in place of unitary gates.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

/-! ### Circuits with one branch and sequences of layers -/

namespace Circuit

variable {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The map of a circuit with a single branch `p` is the conjugation by its Kraus operator. A
circuit of unitary gates and onsite families has a single branch
(`Circuit.nonempty_unique_index`), so its map is `ρ ↦ U ρ Uᴴ`.

Source: arXiv:2307.01696, main text before Theorem 1 (a depth-`T` unitary circuit), read as a
circuit of channels with one Kraus operator per gate. -/
theorem map_eq_of_subsingleton [∀ s, Fintype (Z s)] (ev : Interpretation G)
    (c : Circuit Γ G X Z) [Subsingleton c.Index] (p : c.Index)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    c.map ev ρ = c.kraus ev p * ρ * (c.kraus ev p)ᴴ :=
  Fintype.sum_subsingleton _ p

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
/-- A sequence of layers starting with `L` is the circuit of `L` followed by the rest. -/
theorem seq_cons (L : Layer Γ G X X) (Ls : List (Layer Γ G X X)) [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] : seq (L :: Ls) = (ofLayer L).comp (seq Ls) :=
  rfl

/-- The map of a sequence of layers, layer by layer: the head of the list is applied first,
`seq [L₁, …, L_T] = Φ_{L_T} ∘ ⋯ ∘ Φ_{L₁}`.

Source: arXiv:2307.01696, main text before Theorem 1 (layers of a local circuit, in the order
applied), with channels in place of unitary gates. -/
theorem map_seq_cons (ev : Interpretation G) (L : Layer Γ G X X) (Ls : List (Layer Γ G X X)) :
    (seq (L :: Ls)).map ev = (seq Ls).map ev ∘ₗ (L.krausFamily ev).map := by
  rw [seq_cons, map_comp, map_ofLayer]

/-- A sequence of layers has depth at most its number of layers. -/
theorem depth_seq_le_length (Ls : List (Layer Γ G X X)) : (seq Ls).depth ≤ Ls.length := by
  refine (depth_seq_le Ls).trans ?_
  induction Ls with
  | nil => exact le_rfl
  | cons L Ls ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, add_comm Ls.length]
    exact Nat.add_le_add L.depth_le_one ih

end Circuit

/-! ### Onsite layers -/

namespace Layer

variable {X Y : S → Type}

omit [Fintype S] [GateFamily G] in
/-- An onsite layer does not spread supports: its backward light cone of a region is the region.

Source: arXiv:2103.13367, Supplemental Material, proof of the area law (local operations do not
increase the entanglement across a cut), in the Heisenberg picture. -/
@[simp] theorem lightCone_ofOnsite (o : (s : S) → KrausFamily (X s) (Y s)) (R : Finset S) :
    (ofOnsite (Γ := Γ) (G := G) o).lightCone R = R := by
  simp [lightCone, ofOnsite]

omit [Fintype S] in
/-- An onsite layer has a local property when every onsite family has it. -/
theorem forall_ofOnsite [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (ev : Interpretation G)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    {o : (s : S) → KrausFamily (X s) (Y s)} (ho : ∀ s, P (o s)) :
    (ofOnsite (Γ := Γ) (G := G) o).Forall ev P :=
  ⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun s ↦ ho s.1⟩

end Layer

namespace Circuit

variable {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

/-- The circuit of an onsite layer realises the product channel `⊗ₛ o s`. -/
theorem map_ofLayer_ofOnsite (ev : Interpretation G) (o : (s : S) → KrausFamily (X s) (Y s)) :
    (ofLayer (Layer.ofOnsite (Γ := Γ) (G := G) o)).map ev = (prodFamily o).map := by
  rw [map_ofLayer, Layer.map_krausFamily_ofOnsite]

/-- **Onsite channels are product channels.** The circuit of an onsite layer maps a product
operator `⊗ₛ σₛ` to `⊗ₛ (o s)(σₛ)`.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" (local operations
`U = ⊗ᵢ uᵢ` acting on each site and its ancillas), with channels in place of unitaries. -/
theorem map_ofLayer_ofOnsite_piKronecker (ev : Interpretation G)
    (o : (s : S) → KrausFamily (X s) (Y s)) (σ : (s : S) → Matrix (X s) (X s) ℂ) :
    (ofLayer (Layer.ofOnsite (Γ := Γ) (G := G) o)).map ev (piKronecker σ) =
      piKronecker fun s ↦ (o s).map (σ s) := by
  rw [map_ofLayer_ofOnsite, map_prodFamily_piKronecker]

end Circuit

/-! ### Layers, channel circuits and onsite channels as protocols -/

section Protocols

variable {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]

/-- A layer of trace-preserving plain gates and onsite families is a protocol of its depth,
realising the map of its Kraus family. -/
theorem IsProtocol.ofLayer (L : Layer Γ KrausGate X Y)
    (hL : L.Forall KrausGate.ev KrausFamily.IsTP) :
    IsProtocol Γ L.depth (L.krausFamily KrausGate.ev).map :=
  ⟨Circuit.ofLayer L, ⟨hL, fun _ ↦ trivial⟩, (Circuit.depth_ofLayer L).le,
    Circuit.map_ofLayer _ L, Circuit.isUnbranched_ofLayer L⟩

/-- **Channel circuits are protocols.** A sequence of layers of trace-preserving plain gates and
onsite families on one system is a protocol of depth at most the sum of the depths of the
layers, which is at most the number of layers.

Source: arXiv:2307.01696, main text before Theorem 1 (depth-`T` local circuits), with channels
in place of unitary gates. -/
theorem IsProtocol.seq (Ls : List (Layer Γ KrausGate X X))
    (h : ∀ L ∈ Ls, L.Forall KrausGate.ev KrausFamily.IsTP) :
    IsProtocol Γ (Ls.map Layer.depth).sum ((Circuit.seq Ls).map KrausGate.ev) :=
  ⟨Circuit.seq Ls, Circuit.forall_seq _ Ls h, Circuit.depth_seq_le Ls, rfl,
    Circuit.isUnbranched_seq Ls⟩

omit [∀ s, DecidableEq (Y s)] in
/-- **Onsite channels are protocols of depth `0`.** The product `⊗ₛ o s` of trace-preserving
Kraus families, one at every site, is realised by a protocol of depth `0`; the bases may change,
as when ancillas are attached or discarded.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" (local operations on
each site and its ancillas are free), with channels in place of unitaries. -/
theorem IsProtocol.ofOnsite {o : (s : S) → KrausFamily (X s) (Y s)} (ho : ∀ s, (o s).IsTP) :
    IsProtocol Γ 0 (prodFamily o).map := by
  classical
  have h := IsProtocol.ofLayer (Layer.ofOnsite (Γ := Γ) (G := KrausGate) o)
    (Layer.forall_ofOnsite KrausGate.ev ho)
  rwa [Layer.depth_ofOnsite, Layer.map_krausFamily_ofOnsite] at h

omit [∀ s, DecidableEq (Z s)] in
/-- **Attaching ancillas, a channel circuit, and discarding them.** Applying onsite channels
`i s`, a sequence of layers of trace-preserving gates on the enlarged bases, and onsite channels
`o s` converts `ρ` into the result in depth at most the number of layers.

Source: arXiv:2103.13367, main text, paragraph "Phases of matter" ("a given preparation protocol
… (where ancillas are traced out at the end), defines a quantum channel"). -/
theorem IsConversion.ofOnsite_seq {i : (s : S) → KrausFamily (X s) (Y s)} (hi : ∀ s, (i s).IsTP)
    (Ls : List (Layer Γ KrausGate Y Y)) (hLs : ∀ L ∈ Ls, L.Forall KrausGate.ev KrausFamily.IsTP)
    {o : (s : S) → KrausFamily (Y s) (Z s)} (ho : ∀ s, (o s).IsTP)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    IsConversion Γ Ls.length ρ
      ((prodFamily o).map ((Circuit.seq Ls).map KrausGate.ev ((prodFamily i).map ρ))) := by
  classical
  have hc : IsProtocol Γ Ls.length ((Circuit.seq Ls).map KrausGate.ev) :=
    ⟨Circuit.seq Ls, Circuit.forall_seq _ Ls hLs, Circuit.depth_seq_le_length Ls, rfl,
      Circuit.isUnbranched_seq Ls⟩
  exact ⟨_, (((IsProtocol.ofOnsite hi).comp hc).comp (IsProtocol.ofOnsite ho)).mono
    (by omega), rfl⟩

end Protocols

end QuantumCircuit
