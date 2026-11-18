# Inventory B: TNLean/Circuit/Channel register / encoding modules

Source: TNLean `origin/main`, read with `git show`. Nothing was modified in either repository.

How to read the verdicts:
- **a**: a restriction of `Circuit`. The definition disappears.
- **b**: an instance of a core theorem. Deleted.
- **c**: a genuine theorem between two restrictions. Restated.
- **c-supp**: a definition or lemma that a (c) statement needs. It is kept, usually in `Channel/` or `Algebra/` rather than in `Circuit/Core`.
- **c-int**: proof-internal data of a (c) theorem. It is kept private or inlined.
- **d**: dead or duplicate. Dropped.

Core gaps are numbered G1–G9 at the end and referenced in the tables.

---

## 1. TNLean/Circuit/Channel/RegisterEncoding.lean (222 lines)

Content: completed isometric encoding and decoding of a finite basis into a larger register, using the decoder `supportCompletion` from QICLean's `Channel/SupportCompletion`. Also: the qudit-register dimension bound, and the joint encoding of two systems.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `registerEncoding` | def | `(1 : Matrix β β ℂ).submatrix id e`, the isometry of an embedding `α ↪ β` | c-supp | Matrix primitive. Becomes the onsite family `KrausFamily.single (registerEncoding e)`. Compare QICLean's `basisRegisterInjection` (Analysis/RectangularTraceNormAlgebra). |
| `registerEncoding_isIsometry` | thm | `(registerEncoding e).IsIsometry` | c-supp | Needed for the `IsTP` of that family |
| `registerEncoding_isKrausCPTP` | thm | `IsKrausCPTP (singleKrausMap (registerEncoding e))` | b | `KrausFamily.isKrausCPTP_map` with `effect_single` and the isometry |
| `registerDecoding` | def | `supportCompletion (singleKrausMap Vᴴ) (V*Vᴴ) ρ` | c-supp | The decoder. It is the content of the encoding theorem. Needs G4 to become an onsite `KrausFamily`. |
| `registerDecoding_isKrausCPTP` | thm | The decoder is CPTP for a density `ρ` | c-supp | Restated as `IsTP` of the decoder family |
| `registerDecoding_encoding` | thm | `registerDecoding e ρ (singleKrausMap (registerEncoding e) X) = X` | c | The exact retraction (decode ∘ encode = id), with no positivity assumption |
| `registerDecoding_comp_encoding` | thm | The same retraction as `∘ₗ = LinearMap.id` | d | Duplicate (linear-map form) of `registerDecoding_encoding`. Keep one. |
| `registerDecoding_encoding_reference` | thm | The retraction tensored with an identity reference `δ` | b | A reference is idle sites: `kraus_mapSites` gives `⊗ 1`, plus `tensorMapIdLM_comp`. No consumer. |
| `registerEncodedMap` | def | `enc_f ∘ Φ ∘ dec_e` | a | A three-layer composite: onsite decode, Φ, onsite encode (`comp` / `seq`) |
| `registerEncodedMap_isKrausCPTP` | thm | The composite is CPTP | b | `isKrausCPTP_map` with `Forall IsTP` |
| `registerEncodedMap_encoding` | thm | `enc ∘ Φ ∘ dec ∘ enc = enc ∘ Φ` | b | Corollary of the (c) retraction and `map_comp` |
| `le_registerDimension` | thm | `m ≤ B → m ≤ d ^ Nat.clog d B` | d | One-line wrapper around `Nat.le_pow_clog`; inline it. Consumer: PortSimulation. |
| `registerBasisEmbedding` | def | `Classical.choice` of `Fin m ↪ (Fin k → Fin d)` from `m ≤ d ^ k` | c-supp | The qudit code that the dimension-bounded compilation into qudits uses |
| `pairRegisterBasisEmbedding` | def | Joint code `Fin.append (e a) (f b)` of `α × β` into `Fin (k+k) → Fin d` | a | With per-site onsite encoding the joint code is automatic, so the flattening disappears |
| `pairRegisterBasisEmbedding_apply` | simp | rfl | d | No use |
| `registerEncoding_apply` | thm | Entries are Kronecker deltas | c-supp | Simp lemma kept with `registerEncoding` |
| `registerEncoding_pair` | thm | The joint encoding factors as a product of the two local ones | b | `Layer.kraus_apply_eq_prod`: the Kraus operator of an onsite layer is the product of its local entries |

Verbatim signatures (c and c-supp):
```lean
variable {α β : Type*} [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α]
def registerEncoding (e : α ↪ β) : Matrix β α ℂ :=
  (1 : Matrix β β ℂ).submatrix id e
theorem registerEncoding_isIsometry (e : α ↪ β) :
    (registerEncoding e).IsIsometry
def registerDecoding (e : α ↪ β) (ρ : Matrix α α ℂ) :
    Matrix β β ℂ →ₗ[ℂ] Matrix α α ℂ :=
  supportCompletion (singleKrausMap (registerEncoding e)ᴴ)
    (registerEncoding e * (registerEncoding e)ᴴ) ρ
theorem registerDecoding_isKrausCPTP (e : α ↪ β)
    {ρ : Matrix α α ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    IsKrausCPTP (registerDecoding e ρ)
theorem registerDecoding_encoding (e : α ↪ β)
    (ρ X : Matrix α α ℂ) :
    registerDecoding e ρ (singleKrausMap (registerEncoding e) X) = X
theorem registerDecoding_comp_encoding (e : α ↪ β)
    (ρ : Matrix α α ℂ) :
    registerDecoding e ρ ∘ₗ singleKrausMap (registerEncoding e) = LinearMap.id
def registerBasisEmbedding {d k m : ℕ} (h : m ≤ d ^ k) :
    Fin m ↪ (Fin k → Fin d) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using h))
theorem registerEncoding_apply {ι : Type*} [Fintype ι]
    (e : α ↪ (ι → Fin d)) (x : ι → Fin d) (a : α) :
    registerEncoding e x a = if x = e a then 1 else 0
```
What the restatement needs: `supportCompletion` (already in QICLean), and G4 to turn the decoder map into a `KrausFamily` so it can be an onsite family.

Lean consumers (import): `TNLean/Circuit/Channel.lean`, `OnsiteRegisterEncoding.lean`, `PortSimulation.lean`. By name, also `BoundedPortApproximateOutput`, `BoundedPortPureOutput`, `DataInitialization`, `EncodedChannelPlacement`, `PhysicalPortCodes` (they use `registerEncoding` and `_isIsometry`).

Counts: a 2, b 5, c 1 (+6 c-supp), d 3. Total 17.

---

## 2. TNLean/Circuit/Channel/RegisterChannelLift.lean (230 lines)

Content: the split of wire configurations along an embedding `Fin m ↪ Fin W`; the placement `registerChannelLift` of a linear map as `Φ ⊗ id`; this placement agrees with placing each Kraus operator.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `registerConfigurationSplit` | def | `(Fin W → Fin d) ≃ (Fin m → Fin d) × (complement → Fin d)` | d | Duplicate of `extendConfigEquiv (siteSplit e)` (Core/Map) and of `ManyBody.cutEquiv` |
| `registerConfigurationSplit_apply` | simp | rfl | d | Same |
| `registerConfigurationSplit_symm_comp` | thm | Restricting the glued configuration recovers the first part | d | `extendConfigEquiv_fst` |
| `agreeOff_iff_split_snd` | private thm | `AgreeOff` is equality of the complementary parts | d | `cutEquiv_snd_eq_iff` |
| `registerMatrixSplit` | def | `reindexAlgEquiv` along the split | d | Duplicate (cut coordinates) |
| `registerMatrixSplit_conjTranspose` | simp | rfl | d | Same |
| `registerMatrixSplit_embedOp` | thm | `split (embedOp e A) = A ⊗ₖ 1` | d | Duplicate of `ManyBody.reindex_cutEquiv_place` |
| `registerMatrixSplit_embedOp_reindex_complement` | thm | The same, after relabelling the complement | d | No consumer |
| `registerComplementOfSum` | def | From `q : Fin m ⊕ Fin b ≃ Fin W`, identify `Fin b` with the complement | d | `mapSites` takes an arbitrary `e : S' ≃ S ⊕ R` directly |
| `registerComplementOfSum_apply_val` | simp | rfl | d | Same |
| `registerSumConfigurationSplit` | def | Split along `q` | d | `extendConfigEquiv q.symm` |
| `registerSumConfigurationSplit_eq` | thm | Agrees with the canonical split | d | No consumer |
| `registerSumConfigurationSplit_embedOp` | thm | Along `q`, the placed operator is `A ⊗ₖ 1` | b | `Layer.kraus_mapSites` (`extendConfigEquiv`). Consumer: PhysicalPortEnvironmentComposition. |
| `registerChannelLift` | def | `split.symm ∘ tensorMapIdLM Φ ∘ split`: placement of an arbitrary linear map | d | Replaced by a core map-level placement (G2); for a Kraus family this is `(Layer.placeFamily D K).map` |
| `registerMatrixSplit_channelLift` | simp | Unfolding lemma | d | Same |
| `registerChannelLift_id` | thm | Lift of the identity is the identity | b | `Circuit.map_done` / lift of `id` (G2) |
| `registerChannelLift_comp` | thm | The lift preserves composition | b | `Circuit.map_comp` (G2) |
| `tensorMapIdLM_rectangularKrausMap` | private thm | `tensorMapIdLM (rectangularKrausMap K) = rectangularKrausMap (K ⊗ 1)` | b | General channel lemma. Not in QICLean `Channel/TensorMap`; move it there (G2). |
| `registerChannelLift_kraus` | thm | `lift (rectangularKrausMap K) = rectangularKrausMap (embedOp e ∘ K)` | b | `map_placeFamily` (G2) |
| `rectangularKrausMap_embedOp_congr` | thm | The placed map does not depend on the Kraus representation | d | No consumer. Corollary of G2. |

There are no (c) items. Lean consumers (import): `Channel.lean`, `EncodedChannelPlacement`, `NativeRegisterWires`, `RegisterEnvironment`. By name, `registerChannelLift` / `_kraus` are also used in `EncodedChannelLayer`, `NativePortLayer`, `OnsiteChannelProduct`, `PhysicalPortLocalDilation`, `WholeSiteChannels`. `registerConfigurationSplit` / `registerMatrixSplit` are used in `DataInitialization`, `EncodedChannelPlacement`, `OnsiteChannelProduct`, `PhysicalRegisterEncoding`.

Counts: a 0, b 5, c 0, d 15. Total 20.

---

## 3. TNLean/Circuit/Channel/RegisterEnvironment.lean (112 lines)

Content: appended environment wires `Fin (W + A)`. Covers product-zero initialization, discarding them by partial trace, and an unused environment changing nothing.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `appendConfigurationSplit` | def | `(Fin (W+A) → Fin d) ≃ (Fin W → Fin d) × (Fin A → Fin d)` | d | `extendConfigEquiv finSumFinEquiv.symm` |
| `appendConfigurationSplit_append` | simp | On `Fin.append` | d | Same |
| `appendMatrixSplit` | def | `reindexAlgEquiv` along it | d | Same |
| `appendMatrixSplit_embedOp` | thm | Placement on the original wires is `U ⊗ₖ 1` | b | `kraus_mapSites` |
| `appendEnvironmentInput` | def | `ρ ↦ ρ ⊗ \|0⟩⟨0\|` on the appended wires | a | Onsite dimension change: the appended sites carry basis `Unit` and get a prepare family `Unit → Fin d`, cost 0 (G8) |
| `discardAppendedEnvironment` | def | Partial trace over the appended wires | a | Onsite family `Fin d → Unit` with Kraus operators `⟨j\|` (G8) |
| `discardAppendedEnvironment_conj` | thm | Discarding `U (prep X) Uᴴ` is the system/environment formula | b | `kraus_comp` with the onsite product formula |
| `discardAppendedEnvironment_lift` | thm | prepare, `U ⊗ 1`, discard = `singleKrausMap U` | b | `kraus_comp` plus `kraus_mapSites`. Needs the one-line fact that discard after prepare is the identity onsite (G8). Consumer: PhysicalPortDilation. |

There are no (c) items. Lean consumers (import): `Channel.lean`, `PhysicalPortEnvironmentComposition`, `PhysicalPortLocalDilation`. By name, `appendEnvironmentInput` and `discardAppendedEnvironment` are also used in `BoundedPortApproximateOutput`, `BoundedPortPureOutput`, `PhysicalPortDilation`, `PhysicalPortPureOutput`, `PhysicalPortUnitaryCompilation`, so seven files in all. Those consumers become circuits whose basis types change from `Unit` to `Fin d` at the ancilla sites.

Counts: a 2, b 3, c 0, d 3. Total 8.

---

## 4. TNLean/Circuit/Channel/OnsiteRegisterEncoding.lean (147 lines)

Content: product onsite codes. Each site is encoded and decoded independently; decoding after encoding is the identity on all chain operators; an encoded onsite channel intertwines with the code.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `OnsiteChannel.ofSiteMaps` | def | Choose Kraus operators for sitewise CPTP maps | a | `OnsiteChannel` is a `Layer` with no cells (onsite dimension change). Choosing Kraus operators is G4. |
| `OnsiteChannel.ofSiteMaps_siteMap` | thm | The chosen family has the given map | b | Specification of G4 |
| `OnsiteChannel.comp` | def | Sitewise composition, with the intermediate dimension allowed to change | a | Two onsite layers composed (`comp` / `seq`) |
| `OnsiteChannel.comp_map` | thm | `(Φ.comp Ψ).map = Ψ.map ∘ₗ Φ.map` | b | `Circuit.map_comp` |
| `OnsiteChannel.map_eq_id_of_siteMap_eq_id` | thm | Identity site maps give the identity | b | Needs G3: the map of a layer depends only on the maps of its local families |
| `OnsiteChannel.encodeRegisters` | def | Onsite layer of `registerEncoding (e i)` | a | No cells, onsite dimension change `Fin m → Fin q` |
| `OnsiteChannel.encodeRegisters_siteMap` | thm | Unfolding | d | No consumer |
| `OnsiteChannel.encodeRegisters_map` | thm | The global map is `singleKrausMap (rectKronecker …)` | b | `Layer.kraus_apply_eq_prod` / `ManyBody.prodOp` |
| `OnsiteChannel.decodeRegisters` | def | Onsite layer of the decoders | a | No cells. The decoder family comes from G4. |
| `OnsiteChannel.decodeRegisters_encodeRegisters` | thm | Product decode ∘ product encode = id on every chain operator | c | The product-code retraction (restated) |
| `OnsiteChannel.decodeRegisters_encodeRegisters_reference` | thm | The same, tensored with a reference | b | `mapSites` (idle reference) + `tensorMapIdLM_comp` |
| `OnsiteChannel.encoded` | def | `registerEncodedMap` at every site | a | Onsite decode ; Φ ; onsite encode, a composite of circuits |
| `OnsiteChannel.encoded_map_encodeRegisters` | thm | `(Φ.encoded …).map ∘ₗ enc_e.map = enc_f.map ∘ₗ Φ.map` | c | Onsite-layer case of the encoding theorem (§10). Restated there. |

Verbatim signatures (c and the definitions they mention):
```lean
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m n q r : ℕ}
-- TNLean/Circuit/Channel/Conversion.lean
structure OnsiteChannel (d e : ℕ) (ι : Type*) where
  r : ι → ℕ
  kraus : (i : ι) → Fin (r i) → Matrix (Fin e) (Fin d) ℂ
  sum_kraus : ∀ i, ∑ j, (kraus i j)ᴴ * kraus i j = 1
noncomputable def map (Φ : OnsiteChannel d e ι) :
    Matrix (ι → Fin d) (ι → Fin d) ℂ →ₗ[ℂ] Matrix (ι → Fin e) (ι → Fin e) ℂ :=
  rectangularKrausMap Φ.krausOp
-- this module
noncomputable def ofSiteMaps
    (Φ : ι → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ))
    (hΦ : ∀ i, IsKrausCPTP (Φ i)) : OnsiteChannel m n ι
noncomputable def encodeRegisters (e : ι → (Fin m ↪ Fin q)) : OnsiteChannel m q ι where
  r _ := 1
  kraus i _ := registerEncoding (e i)
noncomputable def decodeRegisters (e : ι → (Fin m ↪ Fin q))
    (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) : OnsiteChannel q m ι :=
  ofSiteMaps (fun i => registerDecoding (e i) (ρ i))
    (fun i => registerDecoding_isKrausCPTP (e i) (hρ i) (htr i))
theorem decodeRegisters_encodeRegisters (e : ι → (Fin m ↪ Fin q))
    (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    (decodeRegisters e ρ hρ htr).map ∘ₗ (encodeRegisters e).map = LinearMap.id
noncomputable def encoded (Φ : OnsiteChannel m n ι)
    (e : ι → (Fin m ↪ Fin q)) (f : ι → (Fin n ↪ Fin r))
    (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) : OnsiteChannel q r ι :=
  ofSiteMaps (fun i => registerEncodedMap (e i) (f i) (ρ i) (Φ.siteMap i)) …
theorem encoded_map_encodeRegisters (Φ : OnsiteChannel m n ι)
    (e : ι → (Fin m ↪ Fin q)) (f : ι → (Fin n ↪ Fin r))
    (ρ : ι → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    (Φ.encoded e f ρ hρ htr).map ∘ₗ (encodeRegisters e).map =
      (encodeRegisters f).map ∘ₗ Φ.map
```
What the restatement needs:
- G4, the decoder as a `KrausFamily`.
- G3, the map of an onsite layer is the tensor product of its local maps. This turns the local retraction into the global one.
- In core form: for the onsite layers `enc c` and `dec c ρ`, `((enc c).comp (dec c ρ)).map = LinearMap.id` (or `Circuit.seq`).

Lean consumers (import): `Channel.lean`, `EncodedChannelPlacement`, `PhysicalPortCodes`, `RegroupedProtocol`. By name, also `OnsiteChannelProduct` (uses `ofSiteMaps`, `comp_map`, `map_eq_id_of_siteMap_eq_id`), `DataInitialization`, `PhysicalPortIO`, `PhysicalProtocolCompilation` (use `encodeRegisters`).

Counts: a 5, b 5, c 2, d 1. Total 13.

---

## 5. TNLean/Circuit/Channel/PhysicalRegisterEncoding.lean (128 lines)

Content: transports native encoders and decoders to the physical wires. The ports and scratch wires are kept as an explicit identity reference.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PortRegisters.DataReference` | abbrev | Configurations of the wires outside the data registers | d | This is `(r : R) → W r`, the idle sites of `mapSites` |
| `PortRegisters.physicalEncoding` | def | `split.symm ∘ tensorMapIdLM (nativeMatrixEquiv ∘ E)` | a | `mapSites` (idle sites = ports and scratch) of the encoding circuit after blocking (G6) |
| `PortRegisters.physicalDecoding` | def | The reverse | a | Same |
| `PortRegisters.physicalEncoding_isKrausCPTP` | thm | CPTP is preserved | b | `forall_mapSites` + `isKrausCPTP_map` |
| `PortRegisters.physicalDecoding_isKrausCPTP` | thm | Same | b | Same |
| `PortRegisters.physicalDecoding_encoding` | thm | `D ∘ E = id → phys D ∘ phys E = id` | b | `map_mapSites` + `map_comp` (G2, G9) |
| `PortRegisters.dataChannelLift_physicalEncoding` | thm | Intertwining `Φ ∘ E = F ∘ Ψ` is transported to the physical wires | b | Same (G2, G9). Consumer: PhysicalProtocolCompilation. |

There are no (c) items. Lean consumers (import): `Channel.lean`, `DataInitialization`, `PhysicalProtocolCompilation`. By name, also `PhysicalPortIO` (uses `physicalEncoding`).

Counts: a 2, b 4, c 0, d 1. Total 7.

---

## 6. TNLean/Circuit/Channel/PortRegisters.lean (233 lines)

Content: the layout `1 port + k data + k scratch` qudits per site on `Fin (N * (1+k+k))`. Also a routing permutation that moves the left data register into the right scratch register on every selected ring bond, at a cost of `k` port layers.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PortRegisters.layout` | def | `PhysicalPortLayout N (N*(1+k+k))`, with slot 0 as the port | a | Ports as sites (G7). Sites are `Fin N × Slot`; cost-0 cells are site fibres, cost-1 cells are port pairs on ring bonds (G1). |
| `PortRegisters.wire` | def | `finProdFinEquiv (i, s)` | d | Flattening artifact. With sites `Fin N × Slot` it is the identity. |
| `PortRegisters.site_wire` | simp | `site (wire i s) = i` | d | Becomes `Prod.fst` |
| `dataSlot`, `scratchSlot` | private def | Slot arithmetic | d | Replaced by `Slot = Unit ⊕ Fin k ⊕ Fin k` |
| `PortRegisters.data` | def | `Fin k ↪ wires` at site `i` | d | Coordinate: `(i, .data t)` |
| `PortRegisters.scratch` | def | Same, for scratch | d | Coordinate |
| `PortRegisters.site_data` | simp | `site (data i t) = i` | d | Trivial |
| `PortRegisters.site_scratch` | simp | Same | d | Trivial |
| `PortRegisters.data_ne_scratch` | thm | Data and scratch wires differ | d | Trivial (`Sum.inl ≠ Sum.inr`) |
| `PortRegisters.selection` | def | Data digit `t` at sites in `K`, scratch digit elsewhere | c-int | Routing data |
| `PortRegisters.selection_apply` | simp | rfl | c-int | |
| `PortRegisters.site_selection` | simp | Selection stays at its site | c-int | Hypothesis of `register_matching` |
| `PortRegisters.selection_ranges_disjoint` | thm | Distinct digits select disjoint wires | c-int | Hypothesis of `registerPermutation_apply` |
| `PortRegisters.pairData` | def | Both data registers of `i ≠ j` as `Fin (k+k) ↪ wires` | d | Region `{i,j} × data`. The ordered pair flattening disappears with Sites regions and configurations. |
| `PortRegisters.pairData_left` | simp | | d | |
| `PortRegisters.pairData_right` | simp | | d | |
| `PortMatching.right_notMem` | thm | The right end of a selected bond starts no other selected bond | c-int | A ring-matching lemma; belongs with the ring geometry (G1) |
| `PortRegisters.routingPermutation` | def | `registerPermutation (selection K) (PortMatching.perm K hK)` | c-int | |
| `PortRegisters.data_notMem_selection` | thm | Data at sites outside `K` is not selected | c-int | |
| `PortRegisters.routingPermutation_data_left` | thm | `data i t ↦ scratch (i+1) t` | c-int | |
| `PortRegisters.routingPermutation_data_of_notMem` | thm | Data outside `K` is fixed | c-int | |
| `PortRegisters.routingPermutation_pairData_site` | thm | Both data registers of a selected bond land at site `i+1` | c | Routing: the landing-site half (used with the next row) |
| `PortRegisters.routingPermutation_isPhysicalPortUnitary` | thm | The routing permutation is a port-unitary of depth `k` | c | Routing over a matching, with depth equal to the register length |
| `PortRegisters.pairData_isPhysicalPortProtocol` | thm | Any channel on the two data registers of one bond has port depth `≤ 2k` | d | No consumer. Subsumed by the layer-level `matchingChannel_isPhysicalPortProtocol` (PortSimulation) and `dataChannelLift_channelLayer` (NativePortLayer), which use the two (c) rows directly. |

Verbatim signatures (c and the definitions they mention):
```lean
-- TNLean/Circuit/Channel/PhysicalPort.lean
structure PhysicalPortLayout (N W : ℕ) where
  site : Fin W → Fin N
  port : Fin N ↪ Fin W
  site_port : ∀ i, site (port i) = i
inductive IsPhysicalPortUnitary (P : PhysicalPortLayout N W) : ℕ →
    Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ → Prop
  | onsite (i : Fin N) {U} (hU : U ∈ unitary _) (hs : U ∈ ManyBody.supportedOperators
      (fun _ ↦ Fin d) (Finset.univ.filter fun p ↦ P.site p = i)) : IsPhysicalPortUnitary P 0 U
  | onsitePermutation (π : Equiv.Perm (Fin W)) (hπ : ∀ x, P.site (π x) = P.site x) :
      IsPhysicalPortUnitary P 0 (permOp π)
  | layer (L : RingLayer d N) : IsPhysicalPortUnitary P 1 (embedOp P.port L.op)
  | mul … : IsPhysicalPortUnitary P (T + S) (U * V)
  | mono … (hTS : T ≤ S) : IsPhysicalPortUnitary P S U
-- TNLean/Circuit/Channel/PortRouting.lean / PortMatching.lean
noncomputable def registerPermutation (e : Fin k → (Fin N ↪ Fin W)) … -- (signature head)
noncomputable def PortMatching.perm (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) : Equiv.Perm (Fin N) :=
  K.noncommProd (fun i => Equiv.swap i (i + 1)) (swap_commute K hK)
-- this module
def layout (N k : ℕ) : PhysicalPortLayout N (N * (1 + k + k)) where
  site w := (finProdFinEquiv.symm w).1
  port := { toFun := fun i => finProdFinEquiv (i, (⟨0, by omega⟩ : Fin (1 + k + k))), … }
def data (i : Fin N) : Fin k ↪ Fin (N * (1 + k + k))       -- toFun t := wire i (dataSlot t)
def scratch (i : Fin N) : Fin k ↪ Fin (N * (1 + k + k))    -- toFun t := wire i (scratchSlot t)
def selection (K : Finset (Fin N)) (t : Fin k) : Fin N ↪ Fin (N * (1 + k + k)) where
  toFun i := if i ∈ K then data i t else scratch i t
def pairData (i j : Fin N) (hij : i ≠ j) :
    Fin (k + k) ↪ Fin (N * (1 + k + k))
noncomputable def routingPermutation (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) :
    Equiv.Perm (Fin (N * (1 + k + k))) :=
  registerPermutation (selection K) (PortMatching.perm K hK)
theorem routingPermutation_pairData_site (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) {i : Fin N}
    (hi : i ∈ K) (hne : i ≠ i + 1) (a : Fin (k + k)) :
    (layout N k).site (routingPermutation K hK (pairData i (i + 1) hne a)) = i + 1
theorem routingPermutation_isPhysicalPortUnitary (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) :
    IsPhysicalPortUnitary (d := d) (layout N k) k (permOp (routingPermutation K hK))
-- (d, for reference)
theorem pairData_isPhysicalPortProtocol (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) {i : Fin N}
    (hi : i ∈ K) (hne : i ≠ i + 1)
    (A : Fin r → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (hA : ∑ a, (A a)ᴴ * A a = 1) :
    IsPhysicalPortProtocol (layout N k) (2 * k)
      (rectangularKrausMap fun a => embedOp (pairData i (i + 1) hne a) (A a))
```
What the restatement needs:
- G7, a port geometry on `Fin N × Slot`: cost-0 cells are whole site fibres; cost-1 cells are `{(i, port), (i+1, port)}`.
- G1, ring bonds.
- Restated form: an unbranched circuit (each layer is swaps on port cells and onsite swaps on fibres) of depth `≤ k` whose Kraus operator is `permOp routingPermutation`. Together with landing, this gives `≤ 2k` per pair layer.

Lean consumers (import): `Channel.lean`, `NativeRegisterWires`, `PortSimulation`. By name, `layout N k` is used in `BoundedPortApproximateOutput`, `BoundedPortPureOutput`, `NativePortLayer`, `PhysicalPortCodes`, `PhysicalPortIO`, `PhysicalPortUnitaryCompilation`, `PhysicalProtocolCompilation`, `PortSimulation`, `WholeSiteChannels`. `routingPermutation*` and `pairData*` are used in `NativePortLayer` and `PortSimulation`. `scratch` is used in `PhysicalPortCodes`.

Counts: a 1, b 0, c 2 (+9 c-int), d 13 (`dataSlot` and `scratchSlot` counted separately). Total 25.

---

## 7. TNLean/Circuit/Channel/NativeRegisterWires.lean (202 lines)

Content: a native alphabet `Fin (d ^ k)` is identified with its `k` qudit digits at each site (blocking). Covers native channels and operators placed on the physical data wires, and placement commuting with blocking.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `PortRegisters.selectedData` | def | Data digits of the sites `e : Fin s ↪ Fin N`, as `Fin (s*k) ↪ wires` | d | Coordinate flattening; becomes the region `e(Fin s) × data` |
| `PortRegisters.selectedData_apply` | simp | | d | |
| `PortRegisters.allData` | def | `selectedData (refl)` | d | Region of all data slots |
| `PortRegisters.allData_apply` | simp | | d | |
| `PortRegisters.groupedConfigurations` | def | `(Fin (N*k) → Fin d) ≃ (Fin N → Fin (d^k))` via `finFunctionFinEquiv` | a | Blocking `Fin N × Fin k → Fin N`, where the basis at a site is the configurations of its fibre, then `≃ Fin (d^k)` (G6) |
| `PortRegisters.dataConfiguration` | def | Native label read from the data wires | d | Internal |
| `PortRegisters.selectedData_configuration` | simp | | d | Internal |
| `PortRegisters.allData_configuration` | simp | | d | Internal |
| `PortRegisters.nativeMatrixEquiv` | def | `reindexAlgEquiv` along the blocking | a | Matrix part of the blocking map (G6) |
| `PortRegisters.nativeMatrixEquiv_apply` | simp | rfl | d | |
| `PortRegisters.nativeMatrixEquiv_conjTranspose` | simp | rfl | d | |
| `PortRegisters.dataOperator` | def | `embedOp allData (nativeMatrixEquiv A)` | a | `mapSites` (idle = ports and scratch) after blocking |
| `PortRegisters.dataOperator_apply` | thm | Entries | d | |
| `agreeOff_selectedData_iff` | private thm | | d | |
| `PortRegisters.dataOperator_embedOp` | thm | Blocking a native operator placed on sites `e` is placement on those sites' data digits | c | Blocking commutes with placement (regrouping). Restated as a lemma of the blocking map (G6). |
| `PortRegisters.nativeChannelReindex` | def | Conjugation by `nativeMatrixEquiv` on endomorphisms | a | Map part of blocking |
| `PortRegisters.nativeChannelReindex_kraus` | thm | Kraus operators go through the same equivalence | b | Kraus lemma of the blocking map (G6) |
| `PortRegisters.dataChannelLift` | def (`→*`) | `registerChannelLift allData ∘ nativeChannelReindex` | a | Blocking, then `mapSites`. The monoid-hom laws are `map_done` / `map_comp`. |
| `PortRegisters.dataChannelLift_kraus` | thm | Placed Kraus operators | b | `kraus_mapSites` with G2 and G6 |

Verbatim signatures (c and the definitions they mention):
```lean
variable {d k N s r : ℕ}
def selectedData (e : Fin s ↪ Fin N) : Fin (s * k) ↪ Fin (N * (1 + k + k)) :=
  finProdFinEquiv.symm.toEmbedding.trans
    { toFun := fun p : Fin s × Fin k => data (e p.1) p.2, … }
def allData (N k : ℕ) : Fin (N * k) ↪ Fin (N * (1 + k + k)) :=
  selectedData (Function.Embedding.refl (Fin N))
def groupedConfigurations (N k d : ℕ) : (Fin (N * k) → Fin d) ≃ (Fin N → Fin (d ^ k)) where
  toFun x i := finFunctionFinEquiv (fun t => x (finProdFinEquiv (i, t)))
  invFun x p := finFunctionFinEquiv.symm (x (finProdFinEquiv.symm p).1) (finProdFinEquiv.symm p).2
def nativeMatrixEquiv (N k d : ℕ) :
    Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (N * k) → Fin d) (Fin (N * k) → Fin d) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (groupedConfigurations N k d).symm
def dataOperator (A : Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) :
    Matrix (Fin (N * (1 + k + k)) → Fin d) (Fin (N * (1 + k + k)) → Fin d) ℂ :=
  embedOp (allData N k) (nativeMatrixEquiv N k d A)
theorem dataOperator_embedOp (e : Fin s ↪ Fin N)
    (A : Matrix (Fin s → Fin (d ^ k)) (Fin s → Fin (d ^ k)) ℂ) :
    dataOperator (embedOp e A) = embedOp (selectedData e) (nativeMatrixEquiv s k d A)
-- TNLean/Circuit/SiteEmbedding.lean
noncomputable def embedOp (e : κ → ι) (X : Matrix (κ → Fin d) (κ → Fin d) ℂ) : … -- = ManyBody.place on the image
```
What the restatement needs:
- G6, a blocking map `β : S → S'`, where the system at `s'` is `RegionConfig X (β⁻¹ s')` (optionally followed by a basis equivalence such as `finFunctionFinEquiv`).
- Restated as: `blockMatrix (place D K) = place (β⁻¹ D) (blockMatrix K)`.
- A circuit-level `Circuit.block` with `kraus_block`.

Lean consumers (import): `Channel.lean`, `NativePortLayer`, `PhysicalRegisterEncoding`, `SiteBlocking`. By name, also `DataInitialization`, `PhysicalPortCodes`, `WholeSiteChannels` (`nativeMatrixEquiv`, `allData`, `groupedConfigurations`, `dataOperator_embedOp`, `nativeChannelReindex`) and `PhysicalProtocolCompilation` (`dataChannelLift`).

Counts: a 5, b 2, c 1, d 11. Total 19.

---

## 8. TNLean/Circuit/Channel/EncodedChannelLayer.lean (165 lines)

Content: a native ring `ChannelLayer` on `Fin m`, under sitewise codes `Fin m ↪ Fin q`, gives a `ChannelLayer` on `Fin q` with the same bonds that intertwines with the product code.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `matching_intertwine` | private thm | Intertwining of each factor gives intertwining of the `noncommProd` | b | `Layer.map_ofCells` (map = composite of placed maps) plus induction |
| `ChannelLayer.pairEmbedding` | private def | `Fin 2 ↪ Fin N` for bond `{i, i+1}`, `2 ≤ N` | d | The ring-geometry cell (G1) |
| `ChannelLayer.image_univ_pairEmbedding` | private thm | Its image is `ringBond i` | d | Same |
| `ChannelLayer.exists_pairKraus` | thm | Supported global Kraus operators come from normalized two-site Kraus operators (`0 < m`) | a | Disappears: a core `Layer` stores its gates as Kraus families on the cell. Consumer: NativePortLayer. |
| `ChannelLayer.exists_encodedRegisters` | thm | `∃ L' : ChannelLayer q N, L'.bonds = L.bonds ∧ L'.map ∘ₗ enc = enc ∘ₗ L.map` | c | Encoding one pair layer (restated) |

Verbatim signatures:
```lean
variable {N m q : ℕ} [NeZero N]
-- TNLean/Circuit/Channel/Layer.lean: structure BondChannelLayer (d : ℕ) (bond : β → Finset ι)
--   (fields bonds, r, kraus, kraus_mem_supportedOperators, sum_kraus, pairwiseDisjoint);
--   ChannelLayer d N is its ring specialization (bond = ringBond).
theorem ChannelLayer.exists_encodedRegisters (L : ChannelLayer m N) (hN : 2 ≤ N) (hm : 0 < m)
    (c : Fin N → (Fin m ↪ Fin q))
    (ρ : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    ∃ L' : ChannelLayer q N, L'.bonds = L.bonds ∧
      L'.map ∘ₗ (OnsiteChannel.encodeRegisters c).map =
        (OnsiteChannel.encodeRegisters c).map ∘ₗ L.map
-- (a, for reference)
theorem ChannelLayer.exists_pairKraus (L : ChannelLayer m N) (hN : 2 ≤ N) (hm : 0 < m)
    {i : Fin N} (hi : i ∈ L.bonds) :
    ∃ A : Fin (L.r i) → Matrix (Fin 2 → Fin m) (Fin 2 → Fin m) ℂ,
      (∀ a, L.kraus i a = embedOp (pairSites i (i + 1)) (A a)) ∧
      ∑ a, (A a)ᴴ * A a = 1
```
What the restatement needs:
- G1, the ring geometry.
- G4, a `KrausFamily` for `enc_cell ∘ g ∘ dec_cell`: `KrausFamily.comp`, or a choice from `IsKrausCPTP`. This keeps the encoded gate a single gate on the same cell, so the layer has the same cells and costs.
- G3, the lift of local intertwining (from `EncodedChannelPlacement`).
- Core form: for `L : Layer Γ KrausGate X X` (constant system `fun _ ↦ Fin m`), `L.encode c ρ : Layer Γ KrausGate (fun _ ↦ Fin q) (fun _ ↦ Fin q)` with the same cells, and `(encLayer.comp (L.encode …)).map = (L.comp encLayer).map`.
- `0 < m` and `2 ≤ N` become unnecessary: the gates are already local, so no extraction is needed.

Lean consumers (import): `Channel.lean`, `EncodedChannelProtocol`, `NativePortLayer` (uses `exists_pairKraus`).

Counts: a 1, b 1, c 1, d 2. Total 5.

---

## 9. TNLean/Circuit/Channel/EncodedChannelPlacement.lean (134 lines)

Content: the product code factors across a selected register and its complement, so local intertwining with the code lifts to the whole chain.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `rectKronecker_split_apply` | private thm | Entrywise split of a product operator | d | Internal to the next row |
| `reindex_rectKronecker_registerSplit` | thm | Product operator = selected ⊗ complement after the split | d | Duplicate of `ManyBody.reindex_cutEquiv_prodOp`. Consumer: OnsiteChannelProduct. |
| `registerMatrixSplit_encodeRegisters` | thm | The global encoder splits as selected ⊗ complement | b | `Layer.kraus_eq_submatrix` (factorization along a union of blocks) |
| `tensorMapId_singleKraus_intertwine` | private thm | `Ψ ∘ V = V ∘ Φ → (Ψ ⊗ id) ∘ (V ⊗ W) = (V ⊗ W) ∘ (Φ ⊗ id)` | b | General channel lemma (Channel/TensorMap) |
| `registerChannelLift_encodeRegisters` | thm | Local intertwining with the code on `e` lifts to the chain | b | With G3 (map-level factorization of an onsite layer along a region) and G2. Only consumer: EncodedChannelLayer. |

There are no (c) items. Lean consumers (import): `Channel.lean`, `EncodedChannelLayer`, `OnsiteChannelProduct`.

Counts: a 0, b 3, c 0, d 2. Total 5.

---

## 10. TNLean/Circuit/Channel/EncodedChannelProtocol.lean (139 lines)

Content: a word of onsite channels and pair layers on one fixed alphabet. Every dimension-bounded native protocol compiles to such a word with the same number of pair layers, intertwining exactly with the sitewise codes.

| Name | Kind | Content | Verdict | Reason |
|---|---|---|---|---|
| `FixedRegisterOperation` | abbrev | `OnsiteChannel q q (Fin N) ⊕ ChannelLayer q N` | a | A layer of a circuit with constant system `fun _ ↦ Fin q` on the ring geometry (with or without cells) |
| `FixedRegisterOperation.map` | def | The channel of one operation | a | `Layer.krausFamily.map` |
| `FixedRegisterOperation.depth` | def | 0 for onsite, 1 for a pair layer | a | `Layer` depth (cost-0 onsite, cost-1 bond cells) |
| `FixedRegisterOperation.wordMap` | def | `(ops.map map).prod` | a | `(Circuit.seq Ls).map` |
| `FixedRegisterOperation.wordDepth` | def | Sum of depths | a | `Circuit.depth`, `total_seq` |
| `FixedRegisterOperation.wordMap_isLocalChannelProtocol` | thm | A word is a native protocol | d | Both are the same `Circuit` in core. No consumer. |
| `registerFallbackDensity` | def | `\|0⟩⟨0\|` on `Fin m`, `0 < m` | c-supp | The fixed off-code state of the decoder. Could be any density; keep a small helper. Consumer: PhysicalPortIO. |
| `registerFallbackDensity_posSemidef` | thm | | c-supp | |
| `trace_registerFallbackDensity` | thm | | c-supp | |
| `boundedAlphabetCode` | def | `Fin.castLEEmb (hm.trans hB)` | d | Wrapper; inline `Fin.castLEEmb`. Consumers: PhysicalPortIO, PhysicalProtocolCompilation. |
| `IsDimensionBoundedLocalChannelProtocol.exists_fixedRegisterWord` | thm | Every protocol with all local dimensions `≤ B ≤ q` compiles to a fixed-alphabet word of the same depth, intertwining with the codes | c | Dimension-bounded conversion (restated) |

Verbatim signatures (c and the definitions they mention):
```lean
variable {N q B d e : ℕ} [NeZero N]
-- TNLean/Circuit/Channel/DimensionBoundedConversion.lean
inductive IsDimensionBoundedLocalChannelProtocol (B : ℕ) :
    {d e : ℕ} → ℕ →
    (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) → Prop
  | onsite {d e : ℕ} (Φ : OnsiteChannel d e (Fin N))
      (hd : 0 < d ∧ d ≤ B) (he : 0 < e ∧ e ≤ B) :
      IsDimensionBoundedLocalChannelProtocol B 0 Φ.map
  | layer {d e T : ℕ} {Ψ}
      (hΨ : IsDimensionBoundedLocalChannelProtocol B T Ψ) (L : ChannelLayer e N) :
      IsDimensionBoundedLocalChannelProtocol B (T + 1) (L.map ∘ₗ Ψ)
  | onsite_comp {d e f T : ℕ} {Ψ}
      (hΨ : IsDimensionBoundedLocalChannelProtocol B T Ψ)
      (Φ : OnsiteChannel e f (Fin N)) (hf : 0 < f ∧ f ≤ B) :
      IsDimensionBoundedLocalChannelProtocol B T (Φ.map ∘ₗ Ψ)
theorem IsDimensionBoundedLocalChannelProtocol.dimension_bounds {T : ℕ} {Ψ}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) :
    (0 < d ∧ d ≤ B) ∧ (0 < e ∧ e ≤ B)
-- this module
abbrev FixedRegisterOperation (q N : ℕ) [NeZero N] :=
  Sum (OnsiteChannel q q (Fin N)) (ChannelLayer q N)
noncomputable def FixedRegisterOperation.map (op : FixedRegisterOperation q N) :
    Module.End ℂ (Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ) :=
  op.elim OnsiteChannel.map BondChannelLayer.map
def FixedRegisterOperation.depth (op : FixedRegisterOperation q N) : ℕ := op.elim (fun _ => 0) (fun _ => 1)
noncomputable def FixedRegisterOperation.wordMap (ops : List (FixedRegisterOperation q N)) :
    Module.End ℂ (Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ) :=
  (ops.map map).prod
def FixedRegisterOperation.wordDepth (ops : List (FixedRegisterOperation q N)) : ℕ :=
  (ops.map depth).sum
noncomputable def registerFallbackDensity {m : ℕ} (hm : 0 < m) : Matrix (Fin m) (Fin m) ℂ :=
  vecMulVec (Pi.single ⟨0, hm⟩ 1) (star (Pi.single ⟨0, hm⟩ 1))
def boundedAlphabetCode (hB : B ≤ q) {m : ℕ} (hm : m ≤ B) : Fin m ↪ Fin q :=
  Fin.castLEEmb (hm.trans hB)
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
```
What the restatement needs:
- G5, a bound on the intermediate dimensions as a predicate or function on circuits: every system along every branch has `0 < card (X s) ≤ B`. Positivity is needed for the fallback density.
- G4 and G3 (per-layer encoding, §8).
- G1 (ring).
- Core form: for an unbranched (or general) `c : Circuit Γ KrausGate X Z` with `Forall IsTP` and `c.DimBounded B`, there is `c' : Circuit Γ KrausGate (fun _ ↦ Fin q) (fun _ ↦ Fin q)` with `c'.depth ≤ c.depth` (equality in TNLean) and `(enc_X.comp c').map = (c.comp enc_Z).map`.
- The induction over the `IsDimensionBounded…` constructors becomes structural induction on `Circuit`. With branching, the encoding goes branch by branch, since a layer map keeps the branch structure, so it works for branching circuits as well.

Lean consumers (import): `Channel.lean`, `PhysicalProtocolCompilation` (uses `FixedRegisterOperation`, `wordMap`, `wordDepth`, `boundedAlphabetCode`, `exists_fixedRegisterWord`). By name, also `PhysicalPortIO` (`registerFallbackDensity*`, `boundedAlphabetCode`).

Counts: a 5, b 0, c 1 (+3 c-supp), d 2. Total 11.

---

## Core gaps (needed by the restatements above)

- **G1. Ring geometry.** No `Geometry` on `Fin N` with cells `ringBond i = {i, i+1}` of cost 1. `Circuit/Geometry/Basic` only mentions it in its docstring. `PortMatching.right_notMem` and the private `pairEmbedding` belong there.
- **G2. Map-level placement.** No `placeMap D Φ := reindex(cutEquiv)⁻¹ ∘ tensorMapIdLM Φ ∘ reindex(cutEquiv)` with `(Layer.placeFamily D K).map = placeMap D K.map` (representation independence). Also missing: the channel lemma `tensorMapIdLM (rectangularKrausMap K) = rectangularKrausMap (fun j ↦ K j ⊗ₖ 1)`, which is private in TNLean and absent from QICLean's `Channel/TensorMap`. These replace `registerChannelLift` (used by seven TNLean files).
- **G3. A layer's map is the tensor product of its local maps.** There is a Kraus-level factorization (`Layer.kraus_eq_submatrix`) and a Heisenberg one (`Layer.dual_place`), but no Schrödinger map-level version. It is needed for:
  - the product decode ∘ encode = id;
  - `map_eq_id_of_siteMap_eq_id`;
  - lifting local intertwining (`registerChannelLift_encodeRegisters`).

  It also implies that the map of a layer depends only on the maps of its gates and onsite families.
- **G4. Kraus families from maps, or composition of Kraus families.** `KrausFamily` has `single`, `adjoint`, `map`, `effect`, `IsTP`, but no `comp` (with `(K.comp L).map = L.map ∘ₗ K.map`) and no choice of a family from `IsKrausCPTP Φ`. It is needed to:
  - make the completed decoder (`supportCompletion`) an onsite family;
  - make `enc ∘ g ∘ dec` one gate on the same cell, so that depth and cells are preserved.
- **G5. Bounded intermediate dimension** as a predicate or function on circuits. Already listed in the brief as missing.
- **G6. Blocking map `S → S'`** grouping sites, with the system at `s'` the configurations of its fibre, followed by a basis equivalence (`finFunctionFinEquiv`). It needs its matrix equivalence, a placement compatibility lemma (`dataOperator_embedOp`), and `kraus_block` for circuits. Already listed in the brief as missing.
- **G7. Port geometry.** Sites `Fin N × Slot` (`Slot = port | data (Fin k) | scratch (Fin k)`); cost-0 cells are whole site fibres; cost-1 cells are port pairs on ring bonds. Nothing named "port" exists. Free onsite permutations are cost-0 fibre gates.
- **G8. Ancilla preparation and discarding as onsite families.** Missing: `KrausFamily.prepare a : KrausFamily Unit β` (`|a⟩`) and `KrausFamily.discard : KrausFamily β Unit` (`⟨j|`), with `IsTP` and with discard ∘ prepare = id. These replace `appendEnvironmentInput` and `discardAppendedEnvironment`, which seven TNLean files consume.
- **G9. Map of a moved circuit, and moving composites.** `kraus_mapSites` exists. Missing:
  - a map-level `map_mapSites : (c.mapSites e W h φ).map = placeMap … c.map` (the map tensored with the identity on idle sites);
  - `mapSites` commuting with `comp` / `append`.

  These would delete `physicalDecoding_encoding` and `dataChannelLift_physicalEncoding` outright.

## Verdict counts per module

| Module | Lines | a | b | c | c-supp / c-int | d | Total |
|---|---|---|---|---|---|---|---|
| RegisterEncoding | 222 | 2 | 5 | 1 | 6 | 3 | 17 |
| RegisterChannelLift | 230 | 0 | 5 | 0 | 0 | 15 | 20 |
| RegisterEnvironment | 112 | 2 | 3 | 0 | 0 | 3 | 8 |
| OnsiteRegisterEncoding | 147 | 5 | 5 | 2 | 0 | 1 | 13 |
| PhysicalRegisterEncoding | 128 | 2 | 4 | 0 | 0 | 1 | 7 |
| PortRegisters | 233 | 1 | 0 | 2 | 9 | 13 | 25 |
| NativeRegisterWires | 202 | 5 | 2 | 1 | 0 | 11 | 19 |
| EncodedChannelLayer | 165 | 1 | 1 | 1 | 0 | 2 | 5 |
| EncodedChannelPlacement | 134 | 0 | 3 | 0 | 0 | 2 | 5 |
| EncodedChannelProtocol | 139 | 5 | 0 | 1 | 3 | 2 | 11 |
| **Total** | 1712 | 23 | 28 | 8 | 18 | 53 | 130 |

The 8 genuine (c) theorems to restate:
1. `registerDecoding_encoding`: completed-decoder retraction.
2. `OnsiteChannel.decodeRegisters_encodeRegisters`: product-code retraction.
3. `OnsiteChannel.encoded_map_encodeRegisters`: onsite-layer encoding.
4. `PortRegisters.routingPermutation_isPhysicalPortUnitary`: routing of depth `k`.
5. `PortRegisters.routingPermutation_pairData_site`: routing lands both registers at site `i+1`.
6. `PortRegisters.dataOperator_embedOp`: blocking commutes with placement.
7. `ChannelLayer.exists_encodedRegisters`: encoding one pair layer.
8. `IsDimensionBoundedLocalChannelProtocol.exists_fixedRegisterWord`: dimension-bounded conversion to a fixed alphabet.

Items 3, 7 and 8 merge naturally into one core theorem, "encoding a dimension-bounded circuit into a constant alphabet", with 1 and 2 as its lemmas.
