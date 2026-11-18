# Inventory, group D (TNLean `origin/main`)

Modules: `TNLean/Circuit/Channel/{PhysicalProtocolCompilation, PortChannelRouting, PortMatching,
PortRouting, PortSimulation, RegroupedProtocol, BoundedPortApproximateOutput,
BoundedPortPureOutput}.lean`, `TNLean/Circuit/Measurement/AdaptiveConversion.lean`.

Total: 1907 lines.

## How the TNLean models map to the core

These are the restrictions of `Circuit` that the verdicts below refer to.

- **Ring model**: geometry on `Fin N` with cells `ringBond k = {k, k+1}` of cost 1. TNLean's
  `RingLayer d N` (unitary) and `ChannelLayer d N` (`BondChannelLayer d ringBond`: a TP Kraus
  family on each selected bond, with pairwise disjoint bonds) are a `Layer.ofCells` of
  `KrausGate`s on that geometry with constant system `fun _ => Fin d`. `OnsiteChannel d e (Fin N)`
  is a layer with no cells and onsite families `Fin d → Fin e`. `IsLocalChannelProtocol` is an
  unbranched circuit of TP families on the ring with homogeneous systems `fun _ => Fin d_t`.
  `IsDimensionBoundedLocalChannelProtocol B` adds the condition "every intermediate `d_t ∈ (0, B]`".
- **Physical-port model**: sites are wires `Fin W`. `PhysicalPortLayout N W` (`site : Fin W → Fin N`,
  `port : Fin N ↪ Fin W`) gives the geometry. It has cost-0 cells, one per fibre
  `{p | site p = i}` (arbitrary unitaries, onsite wire permutations, arbitrary TP channels), and
  cost-1 cells `{port k, port (k+1)}` (the ring layer placed on the ports). The system is constant,
  `fun _ => Fin d`, and circuits are unbranched. `IsPhysicalPortUnitary P T U` restricts this to
  unitary gates and `IsPhysicalPortProtocol P T Φ` allows TP gates. Depth `T` is the core
  `Circuit.depth`, since the cost-0 fibre cells are free.
- **Adaptive model** (`IsAdaptiveChannelProtocol`): a branching circuit on the ring. It branches
  only on the outcome tuple of a cell-free onsite layer; layer outcomes are averaged.

The core has neither a ring geometry nor a port geometry yet (see the core gaps).

---

## 1. `TNLean/Circuit/Channel/PortMatching.lean` (167 lines)

Imports `TNLean.Circuit.PairProduct`, `Mathlib.GroupTheory.Perm.Support`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `QuantumCircuit.isPairProduct_permOp_swap` | theorem | `permOp (Equiv.swap i j)` is a product of at most `2 * N` neighbouring-pair unitaries on the open chain | (c) routing | Genuine routing statement: a SWAP of two arbitrary chain sites costs ≤ 2N nearest-neighbour gates (core: a nearest-neighbour chain circuit of `gateCount ≤ 2N` whose Kraus operator is the swap). Its proof is one line from `isPairProduct_embedOp_pairSites` (PairProduct.lean, other group); restate together with that lemma. Used outside the channel stack (below) |
| `PortMatching.swap_apply_of_notMem_bond`, `swap_disjoint_of_disjoint_bond`, `swap_commute` | private thms | disjoint bond swaps are disjoint permutations and commute | (b) | Helpers for `perm`; commutation of gates on disjoint cells is built into `Layer.ofCells` |
| `PortMatching.perm` | def | `K.noncommProd (fun i => swap i (i+1))` for a matching `K` of ring bonds | (c)-support | Pure `Equiv.Perm (Fin N)` combinatorics. The restated routing theorems name it as "the relabelling realised by the swap layer". Keep it, beside the ring geometry, with no circuit content |
| `PortMatching.perm_apply_of_notMem`, `perm_apply_of_mem` | theorems | fixed off the matching, equal to the bond swap on a bond | (c)-support | Used only by `perm_apply_left`/`_right` and `PortRegisters.right_notMem` |
| `PortMatching.perm_apply_left` | theorem (simp) | `perm K hK i = i + 1` | (c)-support | Used by `PortRegisters.lean:192` |
| `PortMatching.perm_apply_right` | theorem (simp) | `perm K hK (i + 1) = i` | (d) | Only used inside this file (by `perm_involutive`) |
| `PortMatching.perm_involutive` | theorem | `perm` is involutive | (d) | No use outside the file (only `perm_symm` uses it) |
| `PortMatching.perm_symm` | theorem (simp) | `(perm K hK).symm = perm K hK` | (d) | No use |
| `PortMatching.swap_mem_supportedOperators` | private thm | the bond swap is supported on its bond | (b) | Automatic for a `KrausGate` on a cell |
| `PortMatching.layer` | def | the `RingLayer d N` with a SWAP on every bond of `K` | (a) | `Layer.ofCells K` of swap gates on the ring geometry; the definition disappears |
| `PortMatching.layer_op` | theorem | `(layer d K hK).op = permOp (perm K hK)` | (b) | `Layer.kraus_ofCells` plus "the product of commuting swaps is the matching permutation". Needs a core swap gate and its relabelling operator (gap 3) |
| `PortMatching.layer_op_one_site` | theorem (simp) | on `Fin 1` the layer is `1` | (d) | No use |

Verbatim (c) signature:

```lean
theorem isPairProduct_permOp_swap (i j : Fin N) :
    IsPairProduct d N (2 * N) (permOp (Equiv.swap i j))
```

The definitions it mentions:

```lean
def IsPairProduct (d n K : ℕ) (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop :=
  ∃ l : List (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ), l.length ≤ K ∧
    (∀ Z ∈ l, IsNeighbourGate Z) ∧
    X = l.prod
-- IsNeighbourGate Z: Z unitary and ∃ p p' : Fin n, p'.val = p.val + 1 ∧
--   Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) {p, p'}
def permOp (τ : Equiv.Perm (Fin n)) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  of fun x y => if y = x ∘ τ then 1 else 0
noncomputable def PortMatching.perm (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) : Equiv.Perm (Fin N)
def ringBond (k : Fin N) : Finset (Fin N) := {k, k + 1}
abbrev RingLayer (d N : ℕ) [NeZero N] := BondLayer d (ringBond (N := N))
```

**Lean consumers** (`import TNLean.Circuit.Channel.PortMatching`): `TNLean/Circuit/Channel.lean`
(aggregator), `Channel/PhysicalPort.lean`, `Channel/PortChannelRouting.lean`, `Channel/PortRouting.lean`,
`Circuit/QuantitativeSitePermutation.lean`, `MPS/Preparation/BlockUnitary.lean`.

- **`TNLean/Circuit/QuantitativeSitePermutation.lean`** uses exactly one declaration,
  `isPairProduct_permOp_swap`, at line 93. A permutation of `n` sites is factored into at most
  `n` swaps (`swapFactors`), and each swap is routed with `isPairProduct_permOp_swap i j`, which
  gives the `2 * n ^ 2` bound. It uses nothing from the `PortMatching` namespace.
- **`TNLean/MPS/Preparation/BlockUnitary.lean`** also uses exactly one declaration,
  `isPairProduct_permOp_swap`, at line 112, inside `isPairProduct_permOp_routePerm`. It uses
  nothing from the `PortMatching` namespace.
- **`Channel/PhysicalPort.lean`** imports the file but names none of its declarations. It
  probably relies on it only for transitive imports (`PairProduct`, `ringBond`).
- **`PortRouting.lean`** uses `PortMatching.perm`, `PortMatching.layer` and
  `PortMatching.layer_op`. **`PortRegisters.lean`** (other group) uses `PortMatching.perm` and
  `PortMatching.perm_apply_left`.
- **Blueprint**: no `\lean{}` tag.

So the only use outside the channel stack is `isPairProduct_permOp_swap`. If PortMatching is
dissolved, that theorem must move to `PairProduct.lean` or to the `SitePermutation` side, or be
restated in the core.

Verdict counts: (a) 1, (b) 5 (3 private helpers, 1 private support lemma, `layer_op`),
(c) 1 (`isPairProduct_permOp_swap`), (c)-support 4 (`perm`, `perm_apply_of_notMem`,
`perm_apply_of_mem`, `perm_apply_left`), (d) 4.

---

## 2. `TNLean/Circuit/Channel/PortRouting.lean` (253 lines)

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PhysicalPortLayout.selectWire`, `site_selectWire`, `selectWire_involutive` | private | onsite swap of port ↔ chosen wire | (b) | Helpers |
| `PhysicalPortLayout.selectionPermutation` | def | the involutive onsite permutation port i ↔ `e i` at every site | (a) | A cost-0 layer of onsite swap gates on the fibre cells; the definition disappears |
| `selectionPermutation_site`, `_port`, `_symm` | theorems | it preserves sites, sends `port i` to `e i`, and is self-inverse | (b) | Used only in `selected_layer`'s proof; facts about a cost-0 swap layer |
| `IsPhysicalPortUnitary.selected_layer` | theorem | any ring layer, moved onto one selected memory wire per site (`embedOp e L.op`), has port depth 1 | (c) routing | Between the ring circuit moved by `mapSites` along `e` and the port-restricted circuit: conjugating by the cost-0 selection swap gives depth 1 |
| `embedOp_permOp_viaEmbedding` | theorem | `embedOp e (permOp σ) = permOp (σ.viaEmbedding e)` | (b) | `kraus_mapSites` for a permutation operator (original ⊗ identity on idle sites). Used by `PhysicalPortEmbedding.lean` too |
| `IsPhysicalPortUnitary.selected_permutation_layer` | theorem | if `L.op = permOp σ`, then `permOp (σ.viaEmbedding e)` has port depth 1 | (b) | Two-line corollary of `selected_layer` and the previous lemma |
| `registerPermutation` | def | `(List.ofFn fun t => σ.viaEmbedding (e t)).prod`: σ applied digit by digit | (a) | The Kraus operator of `seq` of `k` copies of σ's layer, moved along the digit embeddings `e t`; the definition disappears |
| `registerPermutation_apply_of_fixed`, `registerPermutation_pairwise` | private | permutation helpers | (b) | Helpers |
| `registerPermutation_apply` | theorem | `registerPermutation e σ (e t i) = e t (σ i)` | (b) | `kraus_seq` plus `kraus_mapSites` on each digit. Used by `PortRegisters.lean` |
| `registerPermutation_apply_of_notMem` | theorem | fixes wires outside the registers | (b) | Same. Used by `PortRegisters.lean` |
| `registerPermutation_involutive` | theorem | involutive when σ is | (d) | No use |
| `IsPhysicalPortUnitary.permOp_prod` | private | depth of a product of depth-1 permutations | (b) | `total_seq_le` |
| `IsPhysicalPortUnitary.register_matching` | theorem | the `k`-digit register swap along a matching has port depth ≤ k | (c) routing | Statement between the ring model (k matching-swap layers on selected wires) and the port model. Proof: `selected_layer` per digit + additivity, so it is a one-liner after `selected_layer` is restated. Used by `PortRegisters.lean` |

Verbatim (c) signatures:

```lean
theorem IsPhysicalPortUnitary.selected_layer (P : PhysicalPortLayout N W)
    (e : Fin N ↪ Fin W) (he : ∀ i, P.site (e i) = i) (L : RingLayer d N) :
    IsPhysicalPortUnitary P 1 (embedOp e L.op)

theorem register_matching (P : PhysicalPortLayout N W) (e : Fin k → (Fin N ↪ Fin W))
    (he : ∀ t i, P.site (e t i) = i) (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) :
    IsPhysicalPortUnitary (d := d) P k
      (permOp (registerPermutation e (PortMatching.perm K hK)))
-- (in namespace IsPhysicalPortUnitary, variable [NeZero N])
```

The definitions they mention:

```lean
structure PhysicalPortLayout (N W : ℕ) where
  site : Fin W → Fin N
  port : Fin N ↪ Fin W
  site_port : ∀ i, site (port i) = i

inductive IsPhysicalPortUnitary (P : PhysicalPortLayout N W) : ℕ →
    Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ → Prop
  | onsite (i : Fin N) {U : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ}
      (hU : U ∈ unitary (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ))
      (hs : U ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
          (Finset.univ.filter fun p ↦ P.site p = i)) :
      IsPhysicalPortUnitary P 0 U
  | onsitePermutation (π : Equiv.Perm (Fin W)) (hπ : ∀ x, P.site (π x) = P.site x) :
      IsPhysicalPortUnitary P 0 (permOp π)
  | layer (L : RingLayer d N) : IsPhysicalPortUnitary P 1 (embedOp P.port L.op)
  | mul {T S : ℕ} {U V} (hU : IsPhysicalPortUnitary P T U)
      (hV : IsPhysicalPortUnitary P S V) : IsPhysicalPortUnitary P (T + S) (U * V)
  | mono {T S : ℕ} {U} (hU : IsPhysicalPortUnitary P T U) (hTS : T ≤ S) :
      IsPhysicalPortUnitary P S U

noncomputable def embedOp (e : κ → ι) (X : Matrix (κ → Fin d) (κ → Fin d) ℂ) :
    Matrix (ι → Fin d) (ι → Fin d) ℂ :=
  of fun x y => if AgreeOff e x y then X (x ∘ e) (y ∘ e) else 0

noncomputable def registerPermutation (e : Fin k → (Fin N ↪ Fin W))
    (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Fin W) :=
  (List.ofFn fun t => σ.viaEmbedding (e t)).prod

structure BondLayer (d : ℕ) (bond : β → Finset ι) where
  bonds : Finset β
  gate : β → Matrix (ι → Fin d) (ι → Fin d) ℂ
  gate_mem_unitary : ∀ b ∈ bonds, gate b ∈ unitary (Matrix (ι → Fin d) (ι → Fin d) ℂ)
  gate_mem_supportedOperators :
      ∀ b ∈ bonds, gate b ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (bond b)
  pairwiseDisjoint : (bonds : Set β).PairwiseDisjoint bond
```

**Lean consumers**: `Channel.lean` (aggregator), `Channel/PhysicalPortEmbedding.lean` (uses
`embedOp_permOp_viaEmbedding`), `Channel/PortChannelRouting.lean`, `Channel/PortRegisters.lean`
(uses `registerPermutation`, `registerPermutation_apply`, `registerPermutation_apply_of_notMem`,
`IsPhysicalPortUnitary.register_matching`). Blueprint: no `\lean{}` tag.

Verdict counts: (a) 2, (b) 13 (incl. 6 private/helper), (c) 2, (d) 1.

---

## 3. `TNLean/Circuit/Channel/PortChannelRouting.lean` (197 lines)

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `sum_conjTranspose_embedOp_mul` | theorem | placing a TP Kraus family on a register keeps it TP | (b) | Trace preservation of a placed family (`Layer.placeFamily`, `Layer.forall_ofCells` + `Layer.isTP_krausFamily`). Used by `EncodedChannelLayer`, `NativePortLayer`, `PortSimulation`, `WholeSiteChannels` |
| `routingMatrixEquiv`, `routingMatrixEquiv_apply`, `routingMatrixEquiv_symm_apply` | def + thms | conjugation by `permOp σ` as a linear equiv | (b) | Relabelling of sites (`mapSites` with `R = Empty`). Only used in this file |
| `routingChannelConj`, `routingChannelConj_apply` | def + thm | monoid hom `Φ ↦ U Φ(U† · U) U†` | (b) | Same; the monoid-hom property is `kraus_comp` under relabelling. Appears in the statements of `of_routed_map` and `of_routed_family` |
| `routingChannelConj_embeddedKraus` | theorem | conjugating a family placed along `e` places it along `σ ∘ e` | (b) | Functoriality of `mapSites` (relabel ∘ placement = placement along the composite); see gap 8. Used by `NativePortLayer`, `PortSimulation` |
| `IsPhysicalPortProtocol.of_routed_map` | theorem | if the σ-routing has port depth T and `routingChannelConj σ Φ` has depth 0, then Φ has depth 2T | (b) | `comp` of routing, local part and inverse routing + `depth_comp`. Only used in this file |
| `IsPhysicalPortProtocol.of_register_routing` | theorem | a TP channel on register `e`, routed into one spatial site, is a port protocol of depth 2T | (c) routing | Compiles a register gate via routing. Used by `PortRegisters.lean` |
| `IsPhysicalPortProtocol.of_routed_family` | theorem | a commuting family whose routed images are all depth 0 shares one routing: depth 2T | (c) routing | In the core the commuting family is one `Layer.ofCells` (`map_ofCells`). Restated: a layer whose routed cells each lie in one fibre compiles to depth `2T`. Used by `NativePortLayer`, `PortSimulation` |

Verbatim (c) signatures (`variable {d W : ℕ}`, `{N : ℕ} [NeZero N]`):

```lean
theorem IsPhysicalPortProtocol.of_register_routing {m r : ℕ} (P : PhysicalPortLayout N W)
    (e : Fin m ↪ Fin W) (K : Fin r → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)
    (hK : ∑ j, (K j)ᴴ * K j = 1) {T : ℕ} (σ : Equiv.Perm (Fin W))
    (hσ : IsPhysicalPortUnitary (d := d) P T (permOp σ))
    (i : Fin N) (hsite : ∀ j, P.site (σ (e j)) = i) :
    IsPhysicalPortProtocol P (2 * T) (rectangularKrausMap fun j => embedOp e (K j))

theorem IsPhysicalPortProtocol.of_routed_family {α : Type*} (P : PhysicalPortLayout N W)
    (s : Finset α)
    (F : α → Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ))
    (hcomm : (s : Set α).Pairwise (Function.onFun Commute F)) {T : ℕ}
    (σ : Equiv.Perm (Fin W)) (hσ : IsPhysicalPortUnitary (d := d) P T (permOp σ))
    (hF : ∀ j ∈ s, IsPhysicalPortProtocol P 0 (routingChannelConj σ (F j))) :
    IsPhysicalPortProtocol P (2 * T) (s.noncommProd F hcomm)
```

The definitions they mention (beyond §2):

```lean
inductive IsPhysicalPortProtocol (P : PhysicalPortLayout N W) : ℕ →
    (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) → Prop
  | unitary {T : ℕ} {U : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ}
      (hU : IsPhysicalPortUnitary P T U) :
      IsPhysicalPortProtocol P T (singleKrausMap U)
  | onsite (i : Fin N) {r : ℕ}
      (K : Fin r → Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)
      (hK : ∀ j, K j ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
          (Finset.univ.filter fun p ↦ P.site p = i))
      (htrace : ∑ j, (K j)ᴴ * K j = 1) :
      IsPhysicalPortProtocol P 0 (rectangularKrausMap K)
  | comp {T S : ℕ} {Φ Ψ}
      (hΦ : IsPhysicalPortProtocol P T Φ) (hΨ : IsPhysicalPortProtocol P S Ψ) :
      IsPhysicalPortProtocol P (T + S) (Ψ ∘ₗ Φ)
  | mono {T S : ℕ} {Φ} (hΦ : IsPhysicalPortProtocol P T Φ) (hTS : T ≤ S) :
      IsPhysicalPortProtocol P S Φ

def routingChannelConj (σ : Equiv.Perm (Fin W)) :
    Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) →*
      Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :=
  (routingMatrixEquiv σ).conjRingEquiv.toMonoidHom
-- rectangularKrausMap, singleKrausMap: QICLean/Channel/KrausCPTP.lean (already in QICLean)
```

**Lean consumers**: `Channel.lean`, `Channel/EncodedChannelLayer.lean`, `Channel/PortRegisters.lean`,
`Channel/PortSimulation.lean`; by name also `Channel/NativePortLayer.lean` and `Channel/WholeSiteChannels.lean`
(via `sum_conjTranspose_embedOp_mul`, `routingChannelConj_embeddedKraus`, `of_routed_family`).
Blueprint: no `\lean{}` tag.

Verdict counts: (a) 0, (b) 8, (c) 2, (d) 0.

---

## 4. `TNLean/Circuit/Channel/PortSimulation.lean` (212 lines)

Imports `PortChannelRouting`, `PortRegisters`, `RegisterEncoding`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PortRegisters.left_ne_right` | private | `2 ≤ N → i ≠ i + 1` | (b) | Helper (ring geometry fact) |
| `PortRegisters.pairChannel` | def | a two-register Kraus channel placed on `pairData i (i+1)` | (a) | A `KrausGate` on the cell "data registers of sites i, i+1"; the definition disappears |
| `pairData_site_mem_bond`, `pair_kraus_mem_supportedOperators` | private | supports | (b) | Automatic for a gate on a cell |
| `PortRegisters.pairChannel_commute` | theorem | channels on disjoint bonds commute | (b) | Built into `Layer.ofCells` (disjoint cells) |
| `PortRegisters.matchingChannel` | def | `K.noncommProd (pairChannel hN A)` | (a) | `Layer.ofCells K` of the pair gates (`map_ofCells`) on the ring of registers |
| `PortRegisters.matchingChannel_isPhysicalPortProtocol` | theorem | a matching of TP two-register channels has port depth ≤ `2 * k` | (c) compilation to physical ports | One ring layer on sites carrying `k`-qudit registers compiles to depth `2k` on the port geometry. This is the one-layer case of the `dataChannelLift_channelLayer` compiler (NativePortLayer, other group); restate once, for a layer |
| `boundedPairRegisterCode` | def | `(Fin m × Fin m) ↪ (Fin (clog d B + clog d B) → Fin d)` | (c)-support | Encoding embedding (a `Fin`-level code); used only by the next theorem |
| `exists_bounded_matching_simulation` | theorem | a bounded-dimension encoded matching of CPTP pair channels with a fallback extension, at depth `2 * clog d B` | (d) duplicate | No Lean consumer and no blueprint tag. It is the one-layer case of `IsDimensionBoundedLocalChannelProtocol.exists_physicalPortSimulation` (§5), which encodes onsite (`boundedAlphabetCode`) and needs no fallback density. Signature is below in case it is kept |
| `IsPhysicalPortProtocol.list_prod_uniform` | theorem | a list of depth-`c` protocols has depth `c * length` | (b) | `total_seq_le` / `depth_comp`. No use |

Verbatim (c) signature:

```lean
theorem matchingChannel_isPhysicalPortProtocol (hN : 2 ≤ N) {r : Fin N → ℕ}
    (A : ∀ i, Fin (r i) → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (K : Finset (Fin N)) (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond)
    (hA : ∀ i ∈ K, ∑ a, (A i a)ᴴ * A i a = 1) :
    IsPhysicalPortProtocol (layout N k) (2 * k) (matchingChannel hN A K hK)
-- namespace QuantumCircuit.PortRegisters, variable {d N k : ℕ} [NeZero N]
```

Signature of the (d) item, recorded in case it is kept:

```lean
theorem exists_bounded_matching_simulation {d B m N : ℕ} [NeZero N]
    (hd : 2 ≤ d) (hm : m ≤ B) (hN : 2 ≤ N)
    (Φ : Fin N → Module.End ℂ (Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ))
    (K : Finset (Fin N)) (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond)
    (hΦ : ∀ i ∈ K, IsKrausCPTP (Φ i))
    (ρ : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ)
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    ∃ (r : Fin N → ℕ)
      (A : ∀ i, Fin (r i) →
        Matrix (Fin (Nat.clog d B + Nat.clog d B) → Fin d)
          (Fin (Nat.clog d B + Nat.clog d B) → Fin d) ℂ),
      (∀ i ∈ K, rectangularKrausMap (A i) =
        registerEncodedMap (boundedPairRegisterCode hd hm) (boundedPairRegisterCode hd hm)
          ρ (Φ i)) ∧
      (∀ i ∈ K, ∀ X,
        rectangularKrausMap (A i) (singleKrausMap (registerEncoding
          (boundedPairRegisterCode hd hm)) X) =
        singleKrausMap (registerEncoding (boundedPairRegisterCode hd hm)) (Φ i X)) ∧
      IsPhysicalPortProtocol (PortRegisters.layout N (Nat.clog d B))
        (2 * Nat.clog d B) (PortRegisters.matchingChannel hN A K hK)
```

The definitions they mention:

```lean
def PortRegisters.layout (N k : ℕ) : PhysicalPortLayout N (N * (1 + k + k)) where
  site w := (finProdFinEquiv.symm w).1
  port := { toFun := fun i => finProdFinEquiv (i, (⟨0, by omega⟩ : Fin (1 + k + k))) ... }
noncomputable def pairChannel (hN : 2 ≤ N) {r : Fin N → ℕ}
    (A : ∀ i, Fin (r i) → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (i : Fin N) :
    Module.End ℂ (Matrix (Fin (N * (1 + k + k)) → Fin d)
      (Fin (N * (1 + k + k)) → Fin d) ℂ) :=
  rectangularKrausMap fun a => embedOp (pairData i (i + 1) (left_ne_right hN i)) (A i a)
noncomputable def matchingChannel (hN : 2 ≤ N) {r : Fin N → ℕ}
    (A : ∀ i, Fin (r i) → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (K : Finset (Fin N)) (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) :
    Module.End ℂ (Matrix (Fin (N * (1 + k + k)) → Fin d)
      (Fin (N * (1 + k + k)) → Fin d) ℂ) :=
  K.noncommProd (pairChannel hN A) (pairChannel_commute hN A K hK)
def pairData (i j : Fin N) (hij : i ≠ j) : Fin (k + k) ↪ Fin (N * (1 + k + k))  -- PortRegisters
def boundedPairRegisterCode {d B m : ℕ} (hd : 2 ≤ d) (hm : m ≤ B) :
    (Fin m × Fin m) ↪ (Fin (Nat.clog d B + Nat.clog d B) → Fin d)
def registerEncodedMap (e : α ↪ β) (f : γ ↪ δ)
    (ρ : Matrix α α ℂ) (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix γ γ ℂ) :
    Matrix β β ℂ →ₗ[ℂ] Matrix δ δ ℂ
def registerEncoding (e : α ↪ β) : Matrix β α ℂ
```

**Lean consumers**: only `TNLean/Circuit/Channel.lean` (aggregator). Blueprint: no `\lean{}` tag.

Verdict counts: (a) 2, (b) 5, (c) 1, (c)-support 1, (d) 1.

---

## 5. `TNLean/Circuit/Channel/PhysicalProtocolCompilation.lean` (109 lines)

Imports `EncodedChannelProtocol`, `NativePortLayer`, `PhysicalRegisterEncoding`. Its docstring
carries a **Scope restriction** marker citing `docs/paper-gaps/psc21_physical_port_simulation_scope.tex`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PortRegisters.lift_word_cons`, `wordDepth_cons` | private | unfolding | (b) | Helpers |
| `PortRegisters.dataChannelLift_word` | theorem | a fixed-register word lifts to a port protocol of depth `2 * k * wordDepth` | (b), given gap 5 | The induction is "compile each layer by a port circuit, depths add". Once the core has layer-by-circuit substitution with `depth ≤ K · depth` (gap 5), this is that bound applied to `dataChannelLift_channelLayer` (NativePortLayer). Only used in this file |
| `IsDimensionBoundedLocalChannelProtocol.exists_physicalPortSimulation` | theorem | a bounded native protocol of depth T has a port protocol of depth `2 * clog d B * T` that intertwines exactly with the onsite input/output codes, with the full port/scratch reference retained | (c) compilation to physical ports + encoding | Main theorem. It goes from the ring model with intermediate dimension ≤ B to the port model with registers of `clog d B` digits. Used by `PhysicalPortIO.lean:54` |

Verbatim (c) signature:

```lean
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
-- variable {N B m n T d : ℕ} [NeZero N]
```

The definitions it mentions:

```lean
inductive IsDimensionBoundedLocalChannelProtocol (B : ℕ) :
    {d e : ℕ} → ℕ →
    (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) → Prop
  | onsite {d e : ℕ} (Φ : OnsiteChannel d e (Fin N))
      (hd : 0 < d ∧ d ≤ B) (he : 0 < e ∧ e ≤ B) :
      IsDimensionBoundedLocalChannelProtocol B 0 Φ.map
  | layer {d e T : ℕ}
      {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
      (hΨ : IsDimensionBoundedLocalChannelProtocol B T Ψ) (L : ChannelLayer e N) :
      IsDimensionBoundedLocalChannelProtocol B (T + 1) (L.map ∘ₗ Ψ)
  | onsite_comp {d e f T : ℕ}
      {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
      (hΨ : IsDimensionBoundedLocalChannelProtocol B T Ψ)
      (Φ : OnsiteChannel e f (Fin N)) (hf : 0 < f ∧ f ≤ B) :
      IsDimensionBoundedLocalChannelProtocol B T (Φ.map ∘ₗ Ψ)
-- (h.dimension_bounds : (0 < d ∧ d ≤ B) ∧ (0 < e ∧ e ≤ B), a theorem in DimensionBoundedConversion)

structure OnsiteChannel (d e : ℕ) (ι : Type*) where
  r : ι → ℕ
  kraus : (i : ι) → Fin (r i) → Matrix (Fin e) (Fin d) ℂ
  sum_kraus : ∀ i, ∑ j, (kraus i j)ᴴ * kraus i j = 1

abbrev ChannelLayer (d N : ℕ) [NeZero N] := BondChannelLayer d (ringBond (N := N))
structure BondChannelLayer (d : ℕ) (bond : β → Finset ι) where
  bonds : Finset β
  r : β → ℕ
  kraus : (b : β) → Fin (r b) → Matrix (ι → Fin d) (ι → Fin d) ℂ
  kraus_mem_supportedOperators :
      ∀ b ∈ bonds, ∀ j, kraus b j ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (bond b)
  sum_kraus : ∀ b ∈ bonds, ∑ j, (kraus b j)ᴴ * kraus b j = 1
  pairwiseDisjoint : (bonds : Set β).PairwiseDisjoint bond

noncomputable def OnsiteChannel.encodeRegisters (e : ι → (Fin m ↪ Fin q)) : OnsiteChannel m q ι
def boundedAlphabetCode (hB : B ≤ q) {m : ℕ} (hm : m ≤ B) : Fin m ↪ Fin q :=
  Fin.castLEEmb (hm.trans hB)
abbrev DataReference (N k d : ℕ) :=
  {w : Fin (N * (1 + k + k)) // w ∉ Set.range (allData N k)} → Fin d
def PortRegisters.physicalEncoding
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) :
    Matrix (α × DataReference N k d) (α × DataReference N k d) ℂ →ₗ[ℂ]
      Matrix (Fin (N * (1 + k + k)) → Fin d) (Fin (N * (1 + k + k)) → Fin d) ℂ :=
  (registerMatrixSplit (allData N k)).symm.toLinearMap ∘ₗ
    tensorMapIdLM ((nativeMatrixEquiv N k d).toLinearMap ∘ₗ E)
-- tensorMapIdLM : QICLean/Channel/TensorMap.lean (already in QICLean)
-- used in the proof: FixedRegisterOperation (q N) := Sum (OnsiteChannel q q (Fin N)) (ChannelLayer q N),
--   wordMap, wordDepth; PortRegisters.dataChannelLift (N k d) : Module.End … →* Module.End …
```

**Lean consumers**: `Channel.lean`, `Channel/PhysicalPortIO.lean` (uses
`exists_physicalPortSimulation`). Blueprint: no direct `\lean{}` tag (ch33 physical_ports
tags the downstream §7/§8 theorems).

Verdict counts: (a) 0, (b) 3, (c) 1, (d) 0.

---

## 6. `TNLean/Circuit/Channel/RegroupedProtocol.lean` (532 lines)

Imports `SiteBlocking`, `OnsiteRegisterEncoding`, `DimensionBoundedConversion`. Its docstring
cites `docs/paper-gaps/psc21_local_channel_phase_scope.tex` and calls the file an internal
comparison motivated by arXiv:2103.13367 App. E.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `regroupColor` | def | 3-colouring of the ring bonds (2 colours when `M` is even) | (c)-support | Ring-geometry combinatorics needed by `exists_regrouped_layers`. Keep it with the ring geometry |
| `regroupColor_lt_two` | theorem | an even ring uses only colours 0, 1 | (c)-support | Used only in this file |
| `val_add_one` | private | `(j+1).val` on `Fin M` | (b) | Helper |
| `regroupColor_pairwiseDisjoint` | theorem | each colour class is a matching | (c)-support | Used only in this file |
| `sixSite_seam_matching` | theorem | `{1,3,5}` is a matching on `Fin 6` | (d) | No use (obstruction remark) |
| `threeBlock_seams_no_two_colors` | theorem | the triangle cannot be 2-coloured as matchings | (d) | No use |
| `sixSite_seam_block_image` | theorem | blocking pairs sends the seams to the triangle bonds | (d) | No use |
| `ringBond_subset_preimage_siteBlock` | theorem | each original bond lies in the preimage of its block's bond | (c)-support | Becomes "the blocking map sends ring cells into ring cells", i.e. a `Geometry.Hom`-like statement over the blocking map (gap 4) |
| `supportedKraus_mul`, `supportedKraus_noncommProd` | private | composites of TP families supported on S are TP families supported on S | (b) | Merging gates on one cell (KrausFamily composition) |
| `noncommProd_fibers` | private | regroup a noncommProd by fibres | (b) | Helper |
| `regroupChannel` | def | `blockSites e ∘ F ∘ blockSites d ⁻¹` | (c)-support → replaced | Becomes the core blocking map on circuits/maps (gap 4); the definition disappears into it |
| `regroupEnd`, `regroupEnd_kraus` | private | blocked Kraus family | (b) | Kraus operators of a blocked circuit |
| `regroupChannel_blockSites` | theorem | intertwining `regroupChannel F ∘ blockSites = blockSites ∘ F` | (b) | Holds by definition for the blocking map |
| `regroupChannel_comp` | private | functoriality | (b) | Blocking map vs `comp` |
| `blockMatrixEquiv` | private def | reindex `(Fin k → Fin d) ≃ Fin (d^k)` | (b) | Part of the blocking map |
| `OnsiteChannel.inBlock` | private def | restriction to a block | (b) | Helper |
| `OnsiteChannel.regroup` | def | product of onsite channels in each block, as an onsite channel `d^k → e^k` | (a)/(b) | In the core, onsite families of a layer, blocked, are onsite families of the fibre: this is part of the blocking map on layers (gap 4) |
| `OnsiteChannel.regroup_map` | theorem | `Φ.regroup.map = regroupChannel M k Φ.map` | (b) | Kraus operators of a blocked onsite layer, given gap 4 |
| `ChannelLayer.exists_regrouped_layers` | theorem | a ring layer on `M * k` sites is ≤ 2 (M even) or ≤ 3 layers on the blocked ring, exactly | (c) regrouping/blocking | Between the ring circuit and the blocked-ring circuit; the colouring is the content |
| `IsDimensionBoundedLocalChannelProtocol.append_layers` | private | append layers | (b) | `total_append` |
| `IsDimensionBoundedLocalChannelProtocol.exists_regrouped` | theorem | blocking a protocol with dimension bound B gives depth ≤ (2∣3)·T and bound `B ^ k` | (c) regrouping | Same as below plus the intermediate-basis-size bound (gap 6). In the core it should be one blocking theorem plus a basis-size lemma (sizes multiply over a fibre) |
| `IsLocalChannelProtocol.exists_regrouped` | theorem | the same without a dimension bound (`0 < d`) | (c) regrouping | Primary restated statement. Its proof goes through the bounded version only to keep induction on the inductive predicate |
| `regroupChannel_blockSites_reference` | theorem | intertwining with an external reference `tensorMapIdLM` | (d) | No use (would be (b): `tensorMapIdLM` functoriality) |
| `IsLocalChannelConversion.then_blocked` | theorem | an unblocked then a blocked conversion compose, with depth `(2∣3)·T + U` | (b) | `exists_regrouped` + `total_append`. **Blueprint-tagged**: `ch33_local_quantum_circuits_channels.tex:359`; re-point the tag to the restated blocking theorem + `depth_comp` |
| `oneSiteMatrixEquiv`, `oneSiteMatrixEquiv_rectKronecker`, `exists_oneSite_onsite` | private | one-site channels are onsite | (b) | Helpers |
| `regroupChannel_oneBlock_depth_zero` | theorem | with one block every CPTP channel is depth 0 | (d) | No use (in the core a family on a single site is an onsite family of cost 0) |

Verbatim (c) signatures (`variable {M k d e : ℕ}`, `open Fin.CommRing`, `noncomputable section`):

```lean
theorem ChannelLayer.exists_regrouped_layers [NeZero M] [NeZero k] (L : ChannelLayer d (M * k)) :
    ∃ Ls : List (ChannelLayer (d ^ k) M),
      Ls.length ≤ (if M % 2 = 0 then 2 else 3) ∧
        channelCircuitMap Ls = regroupChannel M k L.map

theorem IsDimensionBoundedLocalChannelProtocol.exists_regrouped [NeZero M] [NeZero k] {B T : ℕ}
    {F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T F) :
    ∃ S, S ≤ (if M % 2 = 0 then 2 else 3) * T ∧
      IsDimensionBoundedLocalChannelProtocol (B ^ k) S (regroupChannel M k F)

theorem IsLocalChannelProtocol.exists_regrouped [NeZero M] [NeZero k] {T : ℕ}
    {F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ}
    (h : IsLocalChannelProtocol T F) (hd : 0 < d) :
    ∃ S, S ≤ (if M % 2 = 0 then 2 else 3) * T ∧
      IsLocalChannelProtocol S (regroupChannel M k F)
```

Signature of the (b) item that carries a blueprint tag:

```lean
theorem IsLocalChannelConversion.then_blocked [NeZero M] [NeZero k] {f T U : ℕ}
    {ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    {σ : Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ}
    {τ : Matrix (Fin M → Fin f) (Fin M → Fin f) ℂ}
    (h₁ : IsLocalChannelConversion T ρ σ)
    (h₂ : IsBlockedLocalChannelConversion k U σ τ) (hd : 0 < d) :
    IsBlockedLocalChannelConversion k ((if M % 2 = 0 then 2 else 3) * T + U) ρ τ
```

The definitions they mention:

```lean
def regroupChannel (M k : ℕ)
    (F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ) :
    Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ →ₗ[ℂ]
      Matrix (Fin M → Fin (e ^ k)) (Fin M → Fin (e ^ k)) ℂ :=
  (blockSites M k e).toLinearMap ∘ₗ F ∘ₗ (blockSites M k d).symm.toLinearMap
def blockSites (M k d : ℕ) :
    Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ ≃ₐ[ℂ]
      Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ :=
  (nativeMatrixEquiv M k d).symm
def siteBlock (i : Fin (M * k)) : Fin M := (finProdFinEquiv.symm i).1
def regroupColor (M : ℕ) (j : Fin M) : Fin 3 :=
  if j.val + 1 = M ∧ M % 2 = 1 then 2 else ⟨j.val % 2, by omega⟩
noncomputable def channelCircuitMap :
    List (BondChannelLayer d bond) → Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ)
  | [] => 1
  | L :: Ls => channelCircuitMap Ls * L.map
inductive IsLocalChannelProtocol :
    {d e : ℕ} → ℕ →
    (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ] Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) → Prop
  | onsite {d e : ℕ} (Φ : OnsiteChannel d e (Fin N)) : IsLocalChannelProtocol 0 Φ.map
  | layer {d e T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ] Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
      (hΨ : IsLocalChannelProtocol T Ψ) (L : ChannelLayer e N) :
      IsLocalChannelProtocol (T + 1) (L.map ∘ₗ Ψ)
  | onsite_comp {d e f T : ℕ}
      {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ] Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
      (hΨ : IsLocalChannelProtocol T Ψ) (Φ : OnsiteChannel e f (Fin N)) :
      IsLocalChannelProtocol T (Φ.map ∘ₗ Ψ)
def IsLocalChannelConversion {d' : ℕ} (T : ℕ) (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (σ : Matrix (Fin N → Fin d') (Fin N → Fin d') ℂ) : Prop :=
  ∃ T' ≤ T, ∃ Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ] Matrix (Fin N → Fin d')
    (Fin N → Fin d') ℂ,
    IsLocalChannelProtocol T' Ψ ∧ Ψ ρ = σ
def IsBlockedLocalChannelConversion [NeZero M] (k : ℕ) [NeZero k] (T : ℕ)
    (ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ)
    (σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ) : Prop :=
  IsLocalChannelConversion T (blockSites M k d ρ) σ
-- ChannelLayer, IsDimensionBoundedLocalChannelProtocol, OnsiteChannel: see §5
```

**Lean consumers**: only `TNLean/Circuit/Channel.lean` (aggregator); every declaration is used
only inside this file. Blueprint: `then_blocked` at `ch33_local_quantum_circuits_channels.tex:359`.

Verdict counts: (a)/(b) 1 (`OnsiteChannel.regroup`), (b) 16 (incl. private helpers and
`then_blocked`), (c) 3, (c)-support 5 (`regroupColor`, `regroupColor_lt_two`,
`regroupColor_pairwiseDisjoint`, `ringBond_subset_preimage_siteBlock`, `regroupChannel`
→ blocking map), (d) 5.

---

## 7. `TNLean/Circuit/Channel/BoundedPortPureOutput.lean` (96 lines)

Imports `PhysicalPortIO`, `PhysicalPortPureOutput`. Scope-restriction marker citing
`docs/paper-gaps/psc21_physical_port_simulation_scope.tex`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `IsDimensionBoundedLocalChannelProtocol.exists_physicalPort_pure_output` | theorem | a bounded native pure-to-pure conversion is realised by a port unitary on the layout with appended environment wires, depth `2·clog d B·T`, keeping the full channel identity, with the final vector factorising as encoded output ⊗ unit environment η | (c) compilation + dilation | Between the bounded ring model and the unitary port model with fresh environment sites. The proof composes `exists_physicalPortIO` (other group) with `exists_appended_unitary_dilation_pure_output` (other group) |

Verbatim signature (`variable {B d N T : ℕ} [NeZero d] [NeZero N]`, `noncomputable section`):

```lean
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
```

The definitions it mentions:

```lean
def PhysicalPortLayout.append (P : PhysicalPortLayout N W) {A : ℕ}
    (owner : Fin A → Fin N) : PhysicalPortLayout N (W + A)
  -- site := Fin.addCases P.site owner; port := Fin.castAdd A ∘ P.port
def PortRegisters.wordCodeConfiguration (c : Fin d ↪ (Fin w → Fin d)) :
    (Fin N → Fin d) ↪ (Fin (N * w) → Fin d)
def PortRegisters.portWordCode (d k : ℕ) [NeZero d] : Fin d ↪ (Fin (1 + k + k) → Fin d)
def PortRegisters.wordInitialization (c : Fin d ↪ (Fin w → Fin d)) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (N * w) → Fin d) (Fin (N * w) → Fin d) ℂ
def appendEnvironmentInput (W A d : ℕ) [NeZero d] :
    Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ
def discardAppendedEnvironment (W A d : ℕ) :
    Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ
def appendMatrixSplit (W A d : ℕ) :
    Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ ≃ₐ[ℂ]
      Matrix ((Fin W → Fin d) × (Fin A → Fin d))
        ((Fin W → Fin d) × (Fin A → Fin d)) ℂ
-- fixedEnvEmbedding: QICLean/Channel/EnvironmentEmbedding.lean:30 (already in QICLean)
-- registerEncoding (e : α ↪ β) : Matrix β α ℂ; IsPhysicalPortUnitary, PortRegisters.layout: see above
```

**Lean consumers**: only `Channel.lean`. Blueprint: `ch33_local_quantum_circuits_physical_ports.tex:800`.

Verdict counts: (c) 1.

---

## 8. `TNLean/Circuit/Channel/BoundedPortApproximateOutput.lean` (144 lines)

Imports `ApproximateConversion`, `PhysicalPortDilation`, `PhysicalPortIO`,
`QICLean.Channel.PureMarginalApproximation`. Same scope-restriction marker.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `IsDimensionBoundedLocalChannelProtocol.exists_physicalPort_approximate_output` | theorem | same as §7 but approximate: trace-norm error ε on the native output gives Euclidean error ≤ `√(2ε)` for the dilated port output against encoded target ⊗ unit η | (c) compilation + dilation + approximation | Uses `exists_physicalPortIO`, `exists_appended_unitary_dilation` and QICLean's `exists_unit_product_approx_of_pure_marginal`. The proof is about 100 lines of norm bookkeeping that survives the restatement |

Verbatim signature (`variable {B d N T : ℕ} [NeZero d] [NeZero N]`, `noncomputable section`):

```lean
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
```

Additional definition it mentions:

```lean
def chainTraceNorm (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : ℝ :=
  -- traceNorm (Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _) A)
```

**Lean consumers**: only `Channel.lean`. Blueprint: `ch33_local_quantum_circuits_physical_ports.tex:849`.

Verdict counts: (c) 1.

---

## 9. `TNLean/Circuit/Measurement/AdaptiveConversion.lean` (197 lines)

Imports `TNLean.Circuit.Channel.Feedforward`. Its docstring carries a **Scope restriction**
marker citing `docs/paper-gaps/psc21_adaptive_channel_round_scope.tex`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `IsAdaptiveChannelProtocol` | inductive | adaptive ring protocol: `onsite` (depth 0), `layer` (ChannelLayer then continuation, +1), `instrument` (onsite instrument, the continuation depends on the full outcome tuple `(i : Fin N) → Fin (Φ.r i)`, depth unchanged), `mono` | (a) | A branching `Circuit` on the ring geometry. Restrictions: homogeneous systems `fun _ => Fin d` at each step; TP local families; branching only on the outcomes of cell-free (onsite) layers, gate outcomes averaged. The instrument's outcome tuple is exactly `Layer.Index` of a layer with no cells, `feedforwardMap` is `Circuit.map` of `step L next`, and depth is `Circuit.depth` (sup over branches). The core is more general (it may branch on gate outcomes), which is harmless |
| `IsAdaptiveChannelProtocol.isKrausCPTP` | theorem | the averaged map is CPTP | (b) | `Circuit.isKrausCPTP_map` |
| `IsAdaptiveChannelProtocol.onsite_comp` | theorem | prepend onsite, depth unchanged | (b) | `depth_comp` with a cost-0 layer |
| `IsAdaptiveChannelProtocol.comp` | theorem | composition with additive depth | (b) | `Circuit.comp`/`append` + `total_append` / `depth_comp` |
| `IsAdaptiveChannelProtocol.channelLayer` | theorem | one layer has depth 1 | (b) | `Layer.depth_le_one` |
| `IsLocalChannelProtocol.adaptive` | theorem | deterministic protocols are adaptive | (b) | Trivial in the core: an unbranched circuit is a circuit |
| `IsAdaptiveChannelConversion` | def | `∃ Ψ, IsAdaptiveChannelProtocol T Ψ ∧ Ψ ρ = σ` | (a) | `∃ c : Circuit …, c.depth ≤ T ∧ c.map ρ = σ` (with the restrictions above); the definition disappears or becomes a one-line abbreviation over `Circuit` |
| `IsAdaptiveChannelConversion.refl` | theorem | depth-0 identity | (b) | `Circuit.done`, `map_done` |
| `IsAdaptiveChannelConversion.mono` | theorem | monotone in T | (b) | `≤`-form of depth |
| `IsAdaptiveChannelConversion.trans` | theorem | composition | (b) | `map_comp`, `depth_comp` |
| `IsAdaptiveChannelConversion.density` | theorem | output is a density matrix | (b) | `isKrausCPTP_map` (`trace_map` + positivity) |
| `IsLocalChannelConversion.adaptive` | theorem | deterministic conversions are adaptive | (b) | Trivial inclusion |

No (c) items. The definition the (a) items mention:

```lean
inductive IsAdaptiveChannelProtocol : {d e : ℕ} → ℕ →
    (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) → Prop
  | onsite {d e : ℕ} (Φ : OnsiteChannel d e (Fin N)) :
      IsAdaptiveChannelProtocol 0 Φ.map
  | layer {d e T : ℕ} (L : ChannelLayer d N)
      {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
      (hΨ : IsAdaptiveChannelProtocol T Ψ) :
      IsAdaptiveChannelProtocol (T + 1) (Ψ ∘ₗ L.map)
  | instrument {d e f T : ℕ} (Φ : OnsiteChannel d e (Fin N))
      {Ψ : ((i : Fin N) → Fin (Φ.r i)) →
        Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
          Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
      (hΨ : ∀ J, IsAdaptiveChannelProtocol T (Ψ J)) :
      IsAdaptiveChannelProtocol T (Φ.feedforwardMap Ψ)
  | mono {d e T T' : ℕ}
      {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
      (hΨ : IsAdaptiveChannelProtocol T Ψ) (hT : T ≤ T') :
      IsAdaptiveChannelProtocol T' Ψ
-- variable {N : ℕ} [NeZero N]
def OnsiteChannel.feedforwardMap (Φ : OnsiteChannel d e (Fin N))
    (Ψ : ((i : Fin N) → Fin (Φ.r i)) →
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ :=
  ∑ J, Ψ J ∘ₗ singleKrausMap (Φ.krausOp J)
```

**Lean consumers** (`import TNLean.Circuit.Measurement.AdaptiveConversion`):
`TNLean/Circuit/Measurement.lean` (aggregator) and `TNLean/Circuit/Measurement/AdaptiveRound.lean`.
`AdaptiveRound` is the only file outside this one that names any of its declarations. In
`MeasurementRound.adaptive` (AdaptiveRound.lean:119–150) it uses exactly these:

- `IsAdaptiveChannelProtocol`, the predicate in its statement
  `IsAdaptiveChannelProtocol R.depth R.map`.
- The constructor `IsAdaptiveChannelProtocol.instrument`, line 127.
- The constructor `IsAdaptiveChannelProtocol.onsite`, as `.onsite _` at line 131.
- `IsLocalChannelProtocol.adaptive`, as `h.adaptive` at line 138, applied to the
  `IsLocalChannelProtocol` obtained from `channelCircuitMap_comp`.
- `IsAdaptiveChannelProtocol.comp`, as `hCircuit.comp hfeed` at line 150.

It uses none of `isKrausCPTP`, `onsite_comp`, `channelLayer`, the `mono` constructor, the
`layer` constructor directly, `IsAdaptiveChannelConversion` or its lemmas, or
`IsLocalChannelConversion.adaptive`. After the restatement, `MeasurementRound.adaptive` becomes
an instance: the round is `seq` of the bond layers, then a measurement layer
(`KrausFamily.measure` on the measured sites) whose continuation is the correction layer chosen
by the outcome.

Blueprint: none of these declarations has a `\lean{}` tag. `ch33_local_quantum_circuits_adaptive.tex`
tags `OnsiteChannel.feedforwardMap`, `MeasurementRound.map` and `MeasurementRound.adaptive`. The
paper-gap note `psc21_adaptive_channel_round_scope.tex` mentions these declarations in prose.

Verdict counts: (a) 2, (b) 10, (c) 0, (d) 0.

---

## Core gaps the restatements need

1. **Ring geometry.** `Geometry (Fin N)` with a cost-1 cell `ringBond k = {k, k+1}` for every `k`
   (cells coincide for N = 1, 2), plus its colouring lemma (`regroupColor_pairwiseDisjoint`). The
   core `Geometry/Basic` and `Sites/Lattice` have chain intervals, but no circuit geometry for the
   ring. Needed by every module here.
2. **Physical-port geometry.** Sites `Fin W` with `site : Fin W → Fin N`. It has cost-0 fibre
   cells `{p | site p = i}` (arbitrary gates, including onsite wire permutations) and cost-1 cells
   `{port k, port (k+1)}`; `PhysicalPortLayout.append` adds environment wires with an owner.
   Cost-0 cells are allowed in the core, so this is only a definition plus the identification
   "port depth = `Circuit.depth`". With it, `IsPhysicalPortUnitary`/`IsPhysicalPortProtocol`
   become the restriction "unbranched, constant system `Fin d`, unitary (resp. TP) gates on this
   geometry".
3. **SWAP and site-permutation gates for a general system.** Only `Matrix.swapMatrix 2` (qubits,
   `Circuit/Algorithm`) exists. Needed: a swap `KrausGate` on a pair cell with equal basis types,
   and the lemma "the Kraus operator of `Layer.ofCells` of swaps on a matching is the relabelling
   operator of `PortMatching.perm`". The relabelling exists as `siteConfigurationEquiv` in
   `Sites/Relabel`. Needed for `layer_op`, `selected_layer`, `register_matching`.
4. **Blocking map `S → S'` grouping sites.** The brief notes it is missing. The new system at `s'`
   is the configurations of the fibre, and blocking moves layers, Kraus families and onsite
   families. Needed for `regroupChannel`, `OnsiteChannel.regroup`, `exists_regrouped_layers`,
   `exists_regrouped`, `then_blocked`, `ringBond_subset_preimage_siteBlock`, and also for the
   register picture of `PortRegisters` (the sites `Fin (N * (1 + k + k))` grouped into `N` sites).
   A layer of the original geometry does not go to a single layer (cells crossing block borders
   need the 2/3-colouring), so blocking is not a `LayerMap`; it needs gap 5.
5. **Layer-by-circuit substitution (`bind`/compile).** The core `mapLayers` sends layers to
   layers. Compilation sends each layer to a circuit and needs a bound
   `depth (compile c) ≤ K * depth c` (ports: `K = 2k`; blocking: `K = 2` or `3`). Needed for
   `dataChannelLift_word`, `exists_physicalPortSimulation`, `exists_regrouped`.
6. **A bound on intermediate basis sizes as a function on circuits.** The brief notes it is
   missing. It replaces `IsDimensionBoundedLocalChannelProtocol B` and gives the `B ^ k` bound
   under blocking (fibre sizes multiply). Needed by `exists_physicalPortSimulation`, §7, §8 and
   the bounded `exists_regrouped`.
7. **Dilation of a circuit.** Each local TP family becomes a unitary on the same cell enlarged by
   fresh environment sites (prepared by an onsite family, `fixedEnvEmbedding 0`), with one final
   discard; it keeps the depth. This is `exists_appended_unitary_dilation(_pure_output)` (other
   group). Needed by §7, §8. In the core, the environment sites enter through `mapSites` idle sites
   or through onsite families that change the basis type.
8. **Functoriality of `mapSites`, and conjugation by a site bijection.** There is no lemma for
   `mapSites e ∘ mapSites e' = mapSites (e' ∘ e)`, and none for "moving along a bijection (`R = Empty`)
   is conjugation by the relabelling operator". Needed for `routingChannelConj_embeddedKraus`,
   `embedOp_permOp_viaEmbedding`, `of_register_routing`.
9. **Encodings.** These are register codes: `OnsiteChannel.encodeRegisters`/`boundedAlphabetCode`,
   `wordInitialization`/`portWordCode`, `registerEncoding`, `physicalEncoding` with the reference
   `DataReference`. They are onsite isometric families that change the basis type, which the core
   already allows, so there is no structural gap. They need restating as onsite layers, and the
   intertwining "compiled ∘ encode = encode ∘ (Ψ ⊗ id_ref)" needs a core form. `tensorMapIdLM`
   is already in QICLean, and so is the extension to a reference (`mapSites` with idle reference
   sites).

## Summary verdict counts

| Module | lines | (a) | (b) | (c) | (c)-support | (d) |
|---|---|---|---|---|---|---|
| PortMatching | 167 | 1 | 5 | 1 | 4 | 4 |
| PortRouting | 253 | 2 | 13 | 2 | 0 | 1 |
| PortChannelRouting | 197 | 0 | 8 | 2 | 0 | 0 |
| PortSimulation | 212 | 2 | 5 | 1 | 1 | 1 |
| PhysicalProtocolCompilation | 109 | 0 | 3 | 1 | 0 | 0 |
| RegroupedProtocol | 532 | 1 | 16 | 3 | 5 | 5 |
| BoundedPortPureOutput | 96 | 0 | 0 | 1 | 0 | 0 |
| BoundedPortApproximateOutput | 144 | 0 | 0 | 1 | 0 | 0 |
| AdaptiveConversion | 197 | 2 | 10 | 0 | 0 | 0 |

"(c)-support" means definitions and lemmas that are pure combinatorics or encodings, which the
restated (c) statements still name: `PortMatching.perm` and its apply lemmas, `regroupColor`,
`boundedPairRegisterCode`. `regroupChannel` is counted here too, as the stand-in for the blocking
map. Private helpers are counted under (b).

The 12 (c) theorems to restate:
- `isPairProduct_permOp_swap`
- `IsPhysicalPortUnitary.selected_layer`
- `IsPhysicalPortUnitary.register_matching`
- `IsPhysicalPortProtocol.of_register_routing`
- `IsPhysicalPortProtocol.of_routed_family`
- `PortRegisters.matchingChannel_isPhysicalPortProtocol`
- `IsDimensionBoundedLocalChannelProtocol.exists_physicalPortSimulation`
- `ChannelLayer.exists_regrouped_layers`
- `IsDimensionBoundedLocalChannelProtocol.exists_regrouped`
- `IsLocalChannelProtocol.exists_regrouped`
- `IsDimensionBoundedLocalChannelProtocol.exists_physicalPort_pure_output`
- `IsDimensionBoundedLocalChannelProtocol.exists_physicalPort_approximate_output`

Two of these may collapse after restatement:
- `register_matching` is `selected_layer` plus additivity of depth.
- The two `exists_regrouped` theorems become one blocking theorem plus a basis-size lemma.
