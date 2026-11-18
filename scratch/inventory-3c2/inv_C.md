# Inventory group C: TNLean/Circuit/Channel/PhysicalPort* and NativePortLayer

All files read at `origin/main` of /home/user/lionsr/tnlean. Namespace `QuantumCircuit` unless
marked `PortRegisters.` (= `QuantumCircuit.PortRegisters`).

## The one translation used throughout

A `PhysicalPortLayout N W` becomes a geometry on the sites `Fin W` (the wires; system
constant `fun _ => Fin d`):

* cost-0 cells: every finset of wires contained in one fibre `{j | P.site j = i}`
  (must be all subsets, not just whole fibres, see gap G2);
* cost-1 cells: the port ring bonds `{P.port k, P.port (k+1)}`, `k : Fin N`.

With that geometry:

* `IsPhysicalPortUnitary P T U` = an unbranched circuit on that geometry, system constant `Fin d`,
  every gate and onsite family `IsUnitary`, `depth ≤ T`, unique Kraus operator `U`. Restrictions:
  no branching, constant system, unitary local families, port geometry.
* `IsPhysicalPortProtocol P T Φ` = the same with every local family `IsTP`, not unitary. The
  outcomes of the onsite instruments are summed, so it is unbranched or the branching is ignored.
  `c.map = Φ`.

`RingLayer` gates on ports become one `Layer.ofCells` on the cost-1 cells. The
`onsitePermutation` constructor becomes one layer of cost-0 permutation gates on the whole
fibres. `mul`/`comp` become `comp` plus `depth_comp`. `mono` becomes "depth ≤ T".

## Core gaps found (referenced below as G1–G7)

* **G1 Port geometry builder.** No `Geometry` exists that is built from a site map
  `site : W → N` plus a port embedding: down-closed cost-0 cells inside the fibres, and cost-1
  ring bonds on the ports. No ring or chain geometry exists in `Circuit/Geometry` either (only
  `Basic.lean`; `sitesAndPairs` is all pairs).
* **G2 `Geometry.Hom` demands exact images** (`cell_cellMap : Γ'.cell (cellMap b) = (Γ.cell b).map ι`).
  Embedding a layout into one with more wires per site enlarges the fibres, so whole-fibre cells
  do not map to cells. Fix: make the cost-0 cells down-closed (all subsets of a fibre), as above.
  The other fix is a lax Hom (image ⊆ cell, with the gate extended by the identity).
* **G3 Blocking map `S → S'`** (already listed as missing). Needed to regroup the `k` data wires
  of a site into one native site of basis `Fin (d^k)`, which is what `nativeMatrixEquiv`,
  `nativeChannelReindex`, `dataChannelLift`, `groupedConfigurations` and `wordCodeConfiguration`
  do. Needed for all of NativePortLayer and PhysicalPortCodes.
* **G4 Intermediate-dimension bound on circuits** (already listed as missing). It replaces
  `IsDimensionBoundedLocalChannelProtocol B T Ψ`, which is the hypothesis of the (c) theorems in
  PhysicalPortIO and PhysicalPortUnitaryCompilation.
* **G5 Unitary circuit gives a unitary operator.** The core has `nonempty_unique_index` and
  `isTP_krausFamily`. Nothing states that a circuit with unitary local families on a constant
  system has a Kraus operator in `unitaryGroup`; it follows in a few lines from VᴴV = 1 on a
  square matrix. Also no `depth (seqAdjoint …) = depth …` (for `IsPhysicalPortUnitary.conjTranspose`).
* **G6 Commuting layers on disjoint sites / deferred discard.** Moving an environment discard (a
  cost-0 onsite layer on idle sites) past later layers that do not touch those sites. It is needed
  if the dilation is assembled per piece, as TNLean does. If the core dilation builds one circuit
  on `S ⊕ R` directly, the gap does not arise. The matrix-level fact is already in QICLean
  (`Matrix.DeferredEnvironment.deferredEnvironment_comp`).
* **G7 Gate-level dilation.** A KrausFamily-level "TP family on a cell = reduced map of a unitary
  on the cell ∪ fresh environment sites" is missing. It exists only at matrix level in
  `QICLean/Channel/EnvironmentDilation` (`exists_freshEnvironment_unitary_of_equiv`).

Remark: the core can add and discard environments without new sites. An idle site with basis
`PUnit` receives a cost-0 onsite family `PUnit → Fin d` (prepare |0⟩) and later `Fin d → PUnit`
(trace). Then `appendEnvironmentInput`/`discardAppendedEnvironment` become two onsite layers, and
`P.append owner` becomes the port geometry on `Fin W ⊕ Fin A`, reached through `mapSites`.

---

## 1. TNLean/Circuit/Channel/PhysicalPort.lean (162 lines)

Imports `Layer`, `PortMatching`. Consumers: `TNLean/Circuit/Channel.lean` (aggregator) and
`TNLean/Circuit/Channel/PortRouting.lean`. Through the dependency tree it is used by every
Port*/PhysicalPort*/Bounded* module.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PhysicalPortLayout` | structure | wires→sites map, port embedding, `site_port` | (a) | port geometry on sites `Fin W` (G1) |
| `IsPhysicalPortUnitary` | inductive | unitary circuits: free onsite unitaries/perms, counted `RingLayer` on ports, `mul`, `mono` | (a) | unbranched, constant system `Fin d`, unitary local families, port geometry, `depth ≤ T` |
| `IsPhysicalPortUnitary.mem_unitary` | theorem | such U is unitary | (b) | `isTP_krausFamily` + `nonempty_unique_index` (small gap G5) |
| `IsPhysicalPortUnitary.conjTranspose` | theorem | Uᴴ has the same depth | (b) | `seqAdjoint`/`kraus_seqAdjoint` (depth equality, G5). Used in PortRouting, PortChannelRouting |
| `IsPhysicalPortUnitary.one` | theorem | identity at depth 0 | (b) | `done`, depth 0 |
| `IsPhysicalPortUnitary.onsite_swap` | theorem | swap within a site costs 0 | (b) | `Layer.single` on a cost-0 cell, `depth_single` |
| `IsPhysicalPortProtocol` | inductive | channel protocols: unitary circuits, onsite instruments (outcome discarded), `comp`, `mono` | (a) | as above with `IsTP` local families, `map = Φ` |
| `IsPhysicalPortProtocol.isKrausCPTP` | theorem | protocol is CPTP | (b) | `isKrausCPTP_map` |
| `IsPhysicalPortProtocol.one` | theorem | identity channel depth 0 | (b) | `map_done` |

Counts: a 3, b 6, c 0, d 0.

Verbatim definitions mentioned by (c) items elsewhere:

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
```
(variables: `{d N W : ℕ} [NeZero N]`. `RingLayer d N := BondLayer d (ringBond (N := N))`, i.e.
unitary gates on pairwise disjoint ring bonds `{k, k+1}`, TNLean/Circuit/LocalCircuit.lean.
`embedOp e X` is `X ⊗ 1` along `e`, TNLean/Circuit/SiteEmbedding.lean. `permOp`, from
TNLean/Circuit/SitePermutation.lean, sends `|x⟩ ↦ |x ∘ τ⁻¹⟩`.)

Also mentioned (PortRegisters.lean, group-external):
```lean
def PortRegisters.layout (N k : ℕ) : PhysicalPortLayout N (N * (1 + k + k)) where
  site w := (finProdFinEquiv.symm w).1
  port := { toFun := fun i => finProdFinEquiv (i, (⟨0, by omega⟩ : Fin (1 + k + k))) ... }
```
That is one port, `k` data wires and `k` scratch wires per site. It is (a): a port geometry
built from `Fin N × Fin (1+k+k)`.

---

## 2. TNLean/Circuit/Channel/PhysicalPortCodes.lean (200 lines)

Imports `WholeSiteChannels`, `OnsiteRegisterEncoding`. Consumers: `Channel.lean` and
`DataInitialization.lean`. `wordInitialization`, `wordCodeConfiguration` and `portWordCode` are
also used in BoundedPortApproximateOutput, BoundedPortPureOutput, PhysicalPortIO and
PhysicalPortUnitaryCompilation.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PortRegisters.nativeWordCode` | def | `Fin d ↪ (Fin w → Fin d)` composed into `Fin d ↪ Fin (d^w)` | (d) | absorbed into the blocking equivalence (G3) |
| `PortRegisters.wordCodeConfiguration` | def | product code `(Fin N → Fin d) ↪ (Fin (N*w) → Fin d)` | (a) | per-site basis-changing onsite isometry, then un-block (G3) |
| `PortRegisters.wordCodeConfiguration_apply` | simp thm | evaluation | (d) | coordinate lemma, disappears |
| `grouped_wordCodeConfiguration` | private thm | grouping | (d) | coordinate lemma |
| `PortRegisters.wordInitialization` | def | `singleKrausMap (registerEncoding (wordCodeConfiguration c))` | (a) | one cost-0 layer of onsite isometries `Fin d → (block basis)`, onsite dimension change plus blocking (G3) |
| `PortRegisters.wordInitialization_isKrausCPTP` | theorem | CPTP | (b) | `isKrausCPTP_map` (isometries are TP) |
| `PortRegisters.wordInitialization_eq` | theorem | equals reindexed `encodeRegisters` | (d) | two descriptions of one onsite layer; one definition in core |
| `PortRegisters.wordCodeChange` | def | `OnsiteChannel` converting code c to code f | (a) | onsite TP layer |
| `PortRegisters.wordCodeChangeMap` | def | its map on physical wires | (a) | same, through the blocking map |
| `PortRegisters.wordCodeChangeMap_initialization` | theorem | change ∘ init c = init f | (b) | `map_comp` + the per-site identity `OnsiteChannel.encoded_map_encodeRegisters` (one-site KrausFamily fact) |
| `PortRegisters.wordCodeChangeMap_isPhysicalPortProtocol` | theorem | code change has depth 0 | (b) | onsite / cost-0 cells cost 0 |
| `PortRegisters.portWordCode` | def | input on port, zeros on data/scratch | (a) | "input on the port wire, other wires prepared at 0": onsite prepare layer on idle wires; appears in (c) statements |
| `PortRegisters.dataWordCode` | def | input's native code on data digits, zeros elsewhere | (d) | internal to the proof of `exists_physicalPortIO` |
| `portWordCode_apply`, `dataWordCode_apply`, `portWordCode_port`, `portWordCode_data`, `portWordCode_scratch`, `dataWordCode_port`, `dataWordCode_data`, `dataWordCode_scratch` | simp thms | evaluation | (d) | coordinate lemmas |
| `PortRegisters.exists_portDataTransfers` | theorem | depth-0 pre/post converting between port code and data code | (b) | depth-0 onsite layers + `map_comp`; internal to `exists_physicalPortIO` |

Counts: a 5, b 4, c 0, d 13 (8 of the d's are simp lemmas).

Verbatim (mentioned by the (c) items of §6 and §9):
```lean
def nativeWordCode (c : Fin d ↪ (Fin w → Fin d)) : Fin d ↪ Fin (d ^ w) :=
  c.trans finFunctionFinEquiv.toEmbedding

def wordCodeConfiguration (c : Fin d ↪ (Fin w → Fin d)) :
    (Fin N → Fin d) ↪ (Fin (N * w) → Fin d) :=
  (Function.Embedding.piCongrRight fun _ : Fin N => nativeWordCode c).trans
    (groupedConfigurations N w d).symm.toEmbedding

def wordInitialization (c : Fin d ↪ (Fin w → Fin d)) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (N * w) → Fin d) (Fin (N * w) → Fin d) ℂ :=
  singleKrausMap (registerEncoding (wordCodeConfiguration c))

def portWordCode (d k : ℕ) [NeZero d] : Fin d ↪ (Fin (1 + k + k) → Fin d) where
  toFun x := Fin.append (Fin.append (fun _ : Fin 1 => x) (fun _ : Fin k => 0))
    (fun _ : Fin k => 0)
```

---

## 3. TNLean/Circuit/Channel/PhysicalPortDilation.lean (77 lines)

Imports `PhysicalPortLocalDilation`, `PhysicalPortEnvironmentComposition`. Consumers:
`Channel.lean`, `BoundedPortApproximateOutput.lean`, `PhysicalPortPureOutput.lean`,
`PhysicalPortUnitaryCompilation.lean`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `IsPhysicalPortProtocol.exists_appended_unitary_dilation` | theorem | every port protocol = discard ∘ (unitary port circuit on W+A wires, same depth) ∘ fresh-zero prep | (c) | **dilation** between "TP local families" and "unitary local families + prep/discard" at equal depth. Used by BoundedPortApproximateOutput, BoundedPortPureOutput, PhysicalPortPureOutput, PhysicalPortUnitaryCompilation |
| `IsPhysicalPortProtocol.exists_appended_unitary_dilation_reference` | theorem | same tensored with an external reference `δ` | (d) | duplicate: `congrArg tensorMapIdLM` of the above; no Lean consumer |

Counts: a 0, b 0, c 1, d 1.

Verbatim:
```lean
variable {d N W : ℕ} [NeZero d] [NeZero N]
theorem IsPhysicalPortProtocol.exists_appended_unitary_dilation
    {P : PhysicalPortLayout N W} {T : ℕ}
    {Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)}
    (hΦ : IsPhysicalPortProtocol P T Φ) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary (P.append owner) T U ∧
        discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
          appendEnvironmentInput W A d = Φ
```
What it needs: per-gate dilation (`exists_onsite_appended_dilation`, G7), transport to the larger
layout (`mapSites` + G2), and composition with deferred discard
(`appendEnvironment_comp_channel`, G6). Core restatement: for every circuit `c` on the port
geometry Γ_P with `IsTP` local families, there are an environment `R` (owner map `R → Fin N`) and
a unitary unbranched circuit `u` on the port geometry of `Fin W ⊕ R` with
`u.depth ≤ c.depth` (equivalently ≤ T), such that
`c.map = (prep ++ u ++ discard).map`. Here prep and discard are the cost-0 onsite layers
`PUnit ↔ Fin d` on `R`.

Definitions mentioned (RegisterEnvironment.lean, outside this group):
```lean
def appendEnvironmentInput (W A d : ℕ) [NeZero d] :
    Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ :=
  equivReindexMap (appendConfigurationSplit W A d).symm ∘ₗ
    freshEnvironmentInput (0 : Fin A → Fin d)

def discardAppendedEnvironment (W A d : ℕ) :
    Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ :=
  partialTraceRightLM ∘ₗ equivReindexMap (appendConfigurationSplit W A d)

def appendMatrixSplit (W A d : ℕ) :
    Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ ≃ₐ[ℂ]
      Matrix ((Fin W → Fin d) × (Fin A → Fin d))
        ((Fin W → Fin d) × (Fin A → Fin d)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (appendConfigurationSplit W A d)
```
`PhysicalPortLayout.append` is given in §4.

---

## 4. TNLean/Circuit/Channel/PhysicalPortEmbedding.lean (97 lines)

Imports `PortRouting`. Consumers: `Channel.lean`, `PhysicalPortEnvironmentComposition.lean`,
`PhysicalPortLocalDilation.lean`. `P.append` is also used in BoundedPort*, PhysicalPortDilation,
PhysicalPortPureOutput, PhysicalPortUnitaryCompilation and
`TNLean/PEPS/Approximation/DyadicProtocolSchedule.lean`. That last match comes from a grep and
may be a different `.append`; not checked.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PhysicalPortEmbedding` | structure | wire embedding preserving sites and ports | (a) | a `Geometry.Hom` of port geometries over `siteSplit ι` (needs G2: down-closed cost-0 cells) |
| `PhysicalPortLayout.append` | def | layout on `W + A` wires, new wires owned by `owner`, same ports | (a) | port geometry of `Fin W ⊕ Fin A` with the extended site map; target of `mapSites` with `R = Fin A` |
| `PhysicalPortLayout.appendEmbedding` | def | P into P.append owner | (b) | Hom over `Sum.inl` (`mapSites`, `e = Equiv.refl`) |
| `PhysicalPortEmbedding.unitary` | theorem | unitary port circuits lift at the same depth, identity on new wires | (b) | `mapSites` + `total_mapLayers_le` + `forall_mapLayers` + `kraus_mapSites` (Kronecker with 1) |

Counts: a 2, b 2, c 0, d 0.

Verbatim (mentioned by (c) items):
```lean
def PhysicalPortLayout.append (P : PhysicalPortLayout N W) {A : ℕ}
    (owner : Fin A → Fin N) : PhysicalPortLayout N (W + A) where
  site := Fin.addCases P.site owner
  port := ⟨fun i => Fin.castAdd A (P.port i), ...⟩
  site_port i := ...
```

---

## 5. TNLean/Circuit/Channel/PhysicalPortEnvironmentComposition.lean (325 lines)

Imports `RegisterEnvironment`, `PhysicalPortEmbedding`, `QICLean.Channel.DeferredEnvironmentTrace`.
Consumers: `Channel.lean`, `PhysicalPortDilation.lean`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PhysicalPortEmbedding.appendEnvironment` | def | environment injection A ↪ B extended by id | (b) | a Hom over a site embedding |
| `PhysicalPortEmbedding.appendEnvironment_wires_old` / `_wires_new` | simp thms | evaluation | (d) | coordinate lemmas |
| `PhysicalPortLayout.appendLeftEmbedding` / `appendRightEmbedding` | defs | the two inclusions into `P.append (Fin.append ownerA ownerB)` | (b) | Homs for `mapSites` |
| `IsPhysicalPortUnitary.appendEnvironment_comp` | theorem | lifted U, V compose at depth T + S | (b) | `mapSites` + `comp` + `depth_comp` |
| `appendEnvironmentConfigurationSplit` | def | `(Fin (W+(A+B)) → Fin d) ≃ ((_ × _) × _)` | (d) | coordinates; `extendSystem` / `kraus_mapSites` replace it |
| `appendEnvironmentConfigurationSplit_symm_apply` | simp thm | evaluation | (d) | coordinate lemma |
| `discardAppendedEnvironment_eq_iterated` | theorem | discard A+B = discard B ∘ discard A | (b) | trace of disjoint idle sites; onsite discard layer is a product |
| `reindex_appendEnvironmentInput` | theorem | zero prep on A+B = product of preps | (b) | onsite prep layer is a product |
| `appendLeftWireSum`, `appendRightWireSum`, `appendLeftWireSum_inl`, `appendRightWireSum_inl`, `appendEnvironmentConfigurationSplit_left`, `appendEnvironmentConfigurationSplit_right` | private defs/thms | wire bookkeeping | (d) | coordinate lemmas |
| `reindex_appendLeft_embedOp` / `reindex_appendRight_embedOp` | theorems | lifted operator = `U ⊗ 1` in coordinates | (b) | `kraus_mapSites` |
| `appendEnvironment_comp_trace` | theorem | deferred trace identity for operators | (b) | matrix fact `deferredEnvironment_comp` (already QICLean) |
| `appendEnvironment_comp_channel` | theorem | (red. V) ∘ (red. U) = reduced map of the lifted product, both environments discarded at the end | (b) | `map_comp` + `kraus_mapSites` + deferral of a discard layer (G6); disappears if the core dilation builds one circuit on `S ⊕ R` |

Counts: a 0, b 8, c 0, d 10 (counting private items and simp pairs individually: `_wires_old`,
`_wires_new`, the split, `_symm_apply`, and 6 private items).

No (c) items. Verbatim of the one statement that carries content:
```lean
theorem appendEnvironment_comp_channel [NeZero d] (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N)
    (U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ)
    (V : Matrix (Fin (W + B) → Fin d) (Fin (W + B) → Fin d) ℂ) :
    discardAppendedEnvironment W (A + B) d ∘ₗ
      singleKrausMap (embedOp (P.appendRightEmbedding ownerA ownerB).wires V *
        embedOp (P.appendLeftEmbedding ownerA ownerB).wires U) ∘ₗ
      appendEnvironmentInput W (A + B) d =
      (discardAppendedEnvironment W B d ∘ₗ singleKrausMap V ∘ₗ
        appendEnvironmentInput W B d) ∘ₗ
      (discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
        appendEnvironmentInput W A d)
```

---

## 6. TNLean/Circuit/Channel/PhysicalPortIO.lean (93 lines)

Imports `DataInitialization`, `PhysicalProtocolCompilation`. Consumers: `Channel.lean`,
`BoundedPortApproximateOutput.lean`, `BoundedPortPureOutput.lean`,
`PhysicalPortUnitaryCompilation.lean`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `IsDimensionBoundedLocalChannelProtocol.exists_physicalPortIO` | theorem | a native ring protocol (dimension ≤ B, depth T) compiles to a port protocol of depth `2 * clog d B * T` with I/O on the ports and memory initialized/reset to 0 | (c) | **compilation to physical ports / dimension-bounded conversion / encoding** |

Counts: a 0, b 0, c 1, d 0.

Verbatim:
```lean
variable {N B T d : ℕ} [NeZero N] [NeZero d]
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPortIO
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    let k := Nat.clog d B
    ∃ Γ, IsPhysicalPortProtocol (PortRegisters.layout N k) (2 * k * T) Γ ∧
      Γ ∘ₗ PortRegisters.wordInitialization (PortRegisters.portWordCode d k) =
        PortRegisters.wordInitialization (PortRegisters.portWordCode d k) ∘ₗ Ψ
```
Needs: `exists_physicalPortSimulation` (PhysicalProtocolCompilation, another group),
`exists_portDataTransfers`, `wordInitialization_data_eq_physicalEncoding`,
`tensorMapId_comp_zeroDataReferencePrep` (DataInitialization), `boundedAlphabetCode`,
`registerFallbackDensity` (EncodedChannelProtocol). Core restatement needs:

* G4: the hypothesis becomes "circuit on the ring geometry of `Fin N`, TP families, every
  intermediate basis of size ≤ B, depth ≤ T";
* G1: `PortRegisters.layout N k` becomes the port geometry on `Fin N × Fin (1+k+k)`;
* G3: data registers blocked into native sites;
* initialization `wordInitialization (portWordCode d k)`: the input sits on the port wire and the
  other `2k` wires of each site start as idle `PUnit` sites prepared at 0. This is an onsite
  prepare layer through `mapSites` along `Fin N × Fin (1+k+k) ≃ Fin N ⊕ R`.

Definition mentioned:
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
```
(TNLean/Circuit/Channel/DimensionBoundedConversion.lean; it is (a) in core: a circuit on the
ring geometry with an intermediate-dimension bound, G4.) Also `wordInitialization`,
`portWordCode`, `PortRegisters.layout` from §1–2.

---

## 7. TNLean/Circuit/Channel/PhysicalPortLocalDilation.lean (264 lines)

Imports `RegisterEnvironment`, `PhysicalPortEmbedding`, `Mathlib.Algebra.BigOperators.Fin`.
Consumers: `Channel.lean`, `PhysicalPortDilation.lean`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `exists_qudit_freshEnvironment_unitary` | theorem | a CPTP map on m qudits = reduced map of a unitary with 2m fresh zero qudits | (c) | genuine **dilation** fact, but at the channel (KrausFamily) level; belongs in `QICLean/Channel/EnvironmentDilation` next to `exists_freshEnvironment_unitary_of_equiv` |
| `selectedEnvironmentEmbedding` | def | `Fin (m+A) ↪ Fin (W+A)` | (d) | placement bookkeeping; `place`/`mapSites` replace it |
| `selectedEnvironmentEmbedding_old` / `_new` | simp thms | evaluation | (d) | coordinate lemmas |
| `append_comp_selectedEnvironment` | theorem | config restriction | (d) | coordinate lemma |
| `agreeOff_selectedEnvironment` | private thm | AgreeOff transfer | (d) | coordinate lemma |
| `environmentKraus_selectedEnvironment` | theorem | env blocks of placed operator = placed blocks | (b) | `kraus_single` / placement `M ⊗ 1` |
| `reduced_selectedEnvironment` | theorem | placed dilation, then discard = `registerChannelLift e` of the local reduced map | (b) | `kraus_single` + placement of a gate (`Layer.placeFamily`) |
| `exists_selected_onsite_dilation` | theorem | a channel on wires of site i = zero-depth unitary on those wires + 2m fresh wires owned by i | (c) | **gate-level dilation** in the port geometry (G7); sub-lemma of §3 |
| `PhysicalPortLayout.siteRegister` | def | enumerate the wires of site i | (d) | cells are finsets and gates act on `RegionConfig`, so no enumeration is needed. The other `siteRegister` hits in EncodedChannelPlacement and RegroupedProtocol are different declarations by name match; not checked |
| `PhysicalPortLayout.site_siteRegister` | simp thm | membership | (d) | coordinate |
| `PhysicalPortLayout.image_univ_siteRegister` | theorem | its image is the fibre | (d) | coordinate |
| `exists_localKraus` | private thm | supported Kraus ops = placements, TP | (b) | gates are already on `RegionConfig` of the cell |
| `exists_onsite_appended_dilation` | theorem | every supported onsite instrument has a zero-depth fresh-environment unitary realization | (c) | **gate-level dilation**, the `onsite` case of §3 (G7) |

Counts: a 0, b 3, c 3, d 7.

Verbatim (c):
```lean
theorem exists_qudit_freshEnvironment_unitary {d m : ℕ} [NeZero d]
    (Φ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ))
    (hΦ : IsKrausCPTP Φ) :
    ∃ U : Matrix.unitaryGroup ((Fin m → Fin d) × (Fin (2 * m) → Fin d)) ℂ,
      ∀ X : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ,
        Φ X = partialTraceRight
          ((U : Matrix ((Fin m → Fin d) × (Fin (2 * m) → Fin d))
            ((Fin m → Fin d) × (Fin (2 * m) → Fin d)) ℂ) *
            freshEnvironmentInput (0 : Fin (2 * m) → Fin d) X * Uᴴ)

variable {N : ℕ} [NeZero N] [NeZero d]   -- with {d m W A : ℕ}
theorem exists_selected_onsite_dilation (P : PhysicalPortLayout N W) (i : Fin N)
    (e : Fin m ↪ Fin W) (he : ∀ j, P.site (e j) = i)
    (Φ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ))
    (hΦ : IsKrausCPTP Φ) :
    ∃ U : Matrix (Fin (W + 2 * m) → Fin d) (Fin (W + 2 * m) → Fin d) ℂ,
      IsPhysicalPortUnitary (P.append (fun _ : Fin (2 * m) => i)) 0 U ∧
      discardAppendedEnvironment W (2 * m) d ∘ₗ singleKrausMap U ∘ₗ
        appendEnvironmentInput W (2 * m) d = registerChannelLift e Φ

theorem exists_onsite_appended_dilation {r : ℕ}
    (P : PhysicalPortLayout N W) (i : Fin N)
    (K : Fin r → Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)
    (hs : ∀ a, K a ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
        (Finset.univ.filter fun p ↦ P.site p = i))
    (hnorm : ∑ a, (K a)ᴴ * K a = 1) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary (P.append owner) 0 U ∧
        discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
          appendEnvironmentInput W A d = rectangularKrausMap K
```
Needs: QICLean `exists_freshEnvironment_unitary_of_equiv`, `freshEnvironmentInput`,
`partialTrace_freshEnvironmentInput`, `environmentKraus`. Definition mentioned:
```lean
def registerChannelLift (e : Fin m ↪ Fin W)
    (Φ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)) :
    Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :=
  (registerMatrixSplit e).symm.toLinearMap ∘ₗ tensorMapIdLM Φ ∘ₗ
    (registerMatrixSplit e).toLinearMap
```
(TNLean/Circuit/Channel/RegisterChannelLift.lean. In core this is `Layer.placeFamily` /
`place D K = K ⊗ 1`, so (a)/(b).) Core form of the two port lemmas: a TP `KrausGate` on a
cost-0 cell `D` equals, after prep and discard on `2|D|` fresh `PUnit`-idle sites owned by the
same spatial site, the reduced map of a unitary gate on `D ∪ env`. That is still a cost-0 cell
(down-closed fibre, G2) once the environment sites belong to the fibre.

---

## 8. TNLean/Circuit/Channel/PhysicalPortPureOutput.lean (168 lines)

Imports `PhysicalPortDilation`, `QICLean.Channel.MaximalOverlap`,
`QICLean.Channel.EnvironmentDilation`, `Mathlib.LinearAlgebra.Matrix.DotProduct`,
`TNLean.Algebra.FinSumPermutation`. Consumers: `Channel.lean`, `BoundedPortPureOutput.lean`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `exists_product_of_pure_marginal` | private thm | if a bipartite pure vector has a pure marginal, it is a product | (c)-aux | genuine linear-algebra lemma, not about circuits; move to QICLean `Channel/PartialTrace`/Schmidt area and make it public |
| `IsPhysicalPortProtocol.exists_appended_unitary_dilation_pure_output` | theorem | pure in, pure out: the dilation's joint output is `φ ⊗ η` | (c) | dilation (§3) + pure-output factorization. Used by BoundedPortPureOutput |
| `IsPhysicalPortProtocol.exists_environmentKraus_pure_output` | theorem | measuring the environment in its basis leaves `φ` in every branch | (d) | no Lean consumer (only its own file and the aggregator). In core it would be (c) "measurement of environment sites with `KrausFamily.measure`, branch outputs ∝ φ", restatable from the previous item with `Outcome.lean` |

Counts: a 0, b 0, c 2 (one auxiliary), d 1.

Verbatim:
```lean
private theorem exists_product_of_pure_marginal
    {S E : Type*} [Fintype S] [Fintype E]
    (Ω : S × E → ℂ) (φ : S → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hMarginal : partialTraceRight (vecMulVec Ω (star Ω)) = vecMulVec φ (star φ)) :
    ∃ η : E → ℂ, star η ⬝ᵥ η = 1 ∧ ∀ s e, Ω (s, e) = φ s * η e

variable {d N W : ℕ} [NeZero d] [NeZero N]
theorem IsPhysicalPortProtocol.exists_appended_unitary_dilation_pure_output
    {P : PhysicalPortLayout N W} {T : ℕ}
    {Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)}
    (hΦ : IsPhysicalPortProtocol P T Φ)
    (ψ φ : (Fin W → Fin d) → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hOutput : Φ (vecMulVec ψ (star ψ)) = vecMulVec φ (star φ)) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        ∃ η : (Fin A → Fin d) → ℂ,
          IsPhysicalPortUnitary (P.append owner) T U ∧
          discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
            appendEnvironmentInput W A d = Φ ∧
          star η ⬝ᵥ η = 1 ∧ ∀ x e,
            ((appendMatrixSplit W A d U) *ᵥ
              (fixedEnvEmbedding (0 : Fin A → Fin d) *ᵥ ψ)) (x, e) = φ x * η e

theorem IsPhysicalPortProtocol.exists_environmentKraus_pure_output
    {P : PhysicalPortLayout N W} {T : ℕ}
    {Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)}
    (hΦ : IsPhysicalPortProtocol P T Φ)
    (ψ φ : (Fin W → Fin d) → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hOutput : Φ (vecMulVec ψ (star ψ)) = vecMulVec φ (star φ)) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        ∃ η : (Fin A → Fin d) → ℂ,
          IsPhysicalPortUnitary (P.append owner) T U ∧
          rectangularKrausMap (environmentKraus (appendMatrixSplit W A d U)
            (0 : Fin A → Fin d)) = Φ ∧
          star η ⬝ᵥ η = 1 ∧ ∀ e,
            environmentKraus (appendMatrixSplit W A d U) (0 : Fin A → Fin d) e *ᵥ ψ =
              η e • φ
```
Mentioned defs (QICLean): `fixedEnvEmbedding (e₀ : E) : Matrix (S × E) S ℂ`
(`QICLean/Channel/EnvironmentEmbedding.lean`) and
`environmentKraus (U : Matrix (α × η) (α × η) ℂ) (a b : η) : Matrix α α ℂ`
(`QICLean/Channel/EnvironmentDilation.lean`). In core, `(appendMatrixSplit U) *ᵥ (fixedEnvEmbedding 0 *ᵥ ψ)`
becomes "the Kraus operator of prep ++ u applied to ψ" (`prob_vecMulVec` style), with the output
indexed by `Config (extendSystem …)`.

---

## 9. TNLean/Circuit/Channel/PhysicalPortUnitaryCompilation.lean (55 lines)

Imports `PhysicalPortDilation`, `PhysicalPortIO`. Consumers: `Channel.lean` only.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `IsDimensionBoundedLocalChannelProtocol.exists_physicalPortUnitaryIO` | theorem | bounded native protocol = discard ∘ unitary port circuit (depth `2 * clog d B * T`) ∘ prep ∘ port-code init | (c) | **compilation + dilation** headline. It is the two-line composite of §6 and §3 and has no Lean consumer, so it could also be dropped as (d) if only the parts are kept |

Counts: a 0, b 0, c 1, d 0.

Verbatim:
```lean
variable {N B T d : ℕ} [NeZero N] [NeZero d]
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPortUnitaryIO
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    let k := Nat.clog d B
    let W := N * (1 + k + k)
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary ((PortRegisters.layout N k).append owner) (2 * k * T) U ∧
        discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
          appendEnvironmentInput W A d ∘ₗ
          PortRegisters.wordInitialization (PortRegisters.portWordCode d k) =
          PortRegisters.wordInitialization (PortRegisters.portWordCode d k) ∘ₗ Ψ
```
Needs G1, G3, G4 and the dilation of §3 in core form.

---

## 10. TNLean/Circuit/Channel/NativePortLayer.lean (153 lines)

Imports `NativeRegisterWires`, `EncodedChannelLayer`, `OnsiteChannelProduct`. Consumers:
`Channel.lean`, `PhysicalProtocolCompilation.lean`, `WholeSiteChannels.lean`.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PortRegisters.nativeMatrixEquiv_complete` | theorem | regrouping the native basis preserves Kraus completeness | (b) | trace preservation moves along a blocking `LayerMap` (`forall_mapLayers`), once G3 exists. Also used in WholeSiteChannels |
| `PortRegisters.dataChannelLift_register_kraus` | theorem | lifting a placed native Kraus map = placement on its data digits | (b) | `kraus_mapSites`/`kraus_mapLayers` along blocking + idle port/scratch (G3) |
| `PortRegisters.dataChannelLift_local` | theorem | a channel on one native site has port depth 0 | (b) | a cost-0 cell maps to a cost-0 cell (inside one fibre); `total_mapLayers_le` |
| `PortRegisters.dataChannelLift_onsiteChannel` | theorem | a product onsite channel has port depth 0 | (b) | onsite families cost 0; `total_mapLayers_le`. Used by PhysicalProtocolCompilation |
| `routed_selected_pair_site` | private thm | routed data wires of bond i lie at site i+1 | (d) | internal to the next item |
| `PortRegisters.dataChannelLift_channelLayer` | theorem | a native matching channel layer has port depth ≤ 2k | (c) | **routing / compilation of one native layer to physical ports** (data → scratch at the neighbour via the ports, local gate, inverse routing). Used by PhysicalProtocolCompilation |

Counts: a 0, b 4, c 1, d 1.

Verbatim (c):
```lean
variable {N k d s r : ℕ} [NeZero N]
theorem dataChannelLift_channelLayer (hd : 0 < d) (hN : 2 ≤ N)
    (L : ChannelLayer (d ^ k) N) :
    IsPhysicalPortProtocol (layout N k) (2 * k) (dataChannelLift N k d L.map)
```
Needs: `IsPhysicalPortProtocol.of_routed_family` (PortChannelRouting),
`routingPermutation`, `routingPermutation_isPhysicalPortUnitary`,
`routingPermutation_pairData_site` (PortRegisters), `routingChannelConj_embeddedKraus`,
`ChannelLayer.exists_pairKraus`, `sum_conjTranspose_embedOp_mul`. Core restatement: the
blocking image (G3) of a one-layer circuit on the ring geometry of `Fin N`, local dimension
`d^k`, with TP gates on bonds, equals the map of a port-geometry circuit of depth ≤ 2k on
`Fin N × Fin (1+k+k)` with idle port/scratch wires. It is a routing theorem between the
"ring, native dimension" and "port geometry, qudits" restrictions.

Definitions mentioned:
```lean
def dataChannelLift (N k d : ℕ) :
    Module.End ℂ (Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) →*
      Module.End ℂ (Matrix (Fin (N * (1 + k + k)) → Fin d)
        (Fin (N * (1 + k + k)) → Fin d) ℂ) where
  toFun Φ := registerChannelLift (allData N k) (nativeChannelReindex N k d Φ)
  ...
abbrev ChannelLayer (d N : ℕ) [NeZero N] := BondChannelLayer d (ringBond (N := N))
structure BondChannelLayer (d : ℕ) (bond : β → Finset ι) where
  bonds : Finset β
  r : β → ℕ
  kraus : (b : β) → Fin (r b) → Matrix (ι → Fin d) (ι → Fin d) ℂ
  kraus_mem_supportedOperators :
      ∀ b ∈ bonds, ∀ j, kraus b j ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (bond b)
  sum_kraus : ∀ b ∈ bonds, ∑ j, (kraus b j)ᴴ * kraus b j = 1
  pairwiseDisjoint : (bonds : Set β).PairwiseDisjoint bond
```
(`dataChannelLift` is a blocking map with idle sites, G3, so (a) in core. `ChannelLayer` is one
`Layer.ofCells` on a ring geometry, G1, so (a).)

---

## Per-module verdict counts

| Module | Lines | (a) | (b) | (c) | (d) |
|---|---|---|---|---|---|
| PhysicalPort | 162 | 3 | 6 | 0 | 0 |
| PhysicalPortCodes | 200 | 5 | 4 | 0 | 13 |
| PhysicalPortDilation | 77 | 0 | 0 | 1 | 1 |
| PhysicalPortEmbedding | 97 | 2 | 2 | 0 | 0 |
| PhysicalPortEnvironmentComposition | 325 | 0 | 8 | 0 | 10 |
| PhysicalPortIO | 93 | 0 | 0 | 1 | 0 |
| PhysicalPortLocalDilation | 264 | 0 | 3 | 3 | 7 |
| PhysicalPortPureOutput | 168 | 0 | 0 | 2 (1 aux) | 1 |
| PhysicalPortUnitaryCompilation | 55 | 0 | 0 | 1 | 0 |
| NativePortLayer | 153 | 0 | 4 | 1 | 1 |
| **Total** | 1594 | 10 | 27 | 9 | 33 |

The (c) theorems to restate, 9 in all:

* `exists_appended_unitary_dilation`: the circuit dilation, the central one.
* `exists_onsite_appended_dilation` and `exists_selected_onsite_dilation`: gate-level dilation.
* `exists_qudit_freshEnvironment_unitary`: a channel lemma, to move into QICLean/Channel.
* `exists_product_of_pure_marginal`: a matrix lemma, to move into QICLean/Channel.
* `exists_appended_unitary_dilation_pure_output`.
* `exists_physicalPortIO`: compilation of a dimension-bounded protocol.
* `exists_physicalPortUnitaryIO`: the composite headline, with no consumer.
* `dataChannelLift_channelLayer`: layer routing.

The core gaps they need are G1 (port/ring geometry), G2 (down-closed cells or a lax Hom),
G3 (blocking), G4 (dimension bound), G6 (deferred discard, avoidable) and G7 (gate-level
dilation). G5 (unitary Kraus operator; depth of the adjoint) is needed by the (b) items.
