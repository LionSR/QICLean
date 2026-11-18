3C.2 inventory: TNLean channel stack (38 modules of `TNLean/Circuit/Channel` plus `Measurement/AdaptiveConversion`, TNLean origin/main 75fc22288) against the QICLean core at 28bd64e (#1116).

Method:
- Four agents produced per-declaration verdict tables, one per group: A channel core, B registers, C physical ports, D routing and compilation.
- Four more agents restated every (c) item in the core over one shared prelude of the missing notions.
- I re-ran every file myself. Each typechecks with `lake env lean` against 28bd64e, with only `declaration uses sorry` warnings: A 23, B 16, C 12, D 21.
- Everything is on the branch `inventory/3c2-restatements` (commit 03a1f78, off main, no PR, scratch only and not built), under `scratch/inventory-3c2/`:
  - the four restatement files `Restate_{A,B,C,D}.lean`, each with `Prelude.lean` copied in at the top;
  - their reports `Restate_*.md`;
  - the verdict tables `inv_{A,B,C,D}.md`;
  - this text.
- Each (c) item is quoted verbatim from TNLean, with its file, directly above its core statement.
- To check: `lake env lean scratch/inventory-3c2/Restate_X.lean` from a checkout at 28bd64e.

## 1. Verdicts

The 39 modules break down as A 10, B 10, C 10, D 9.

| Group | (a) restriction | (b) core instance | (c) restate | kept support | (d) dead/dup |
|---|---|---|---|---|---|
| A channel core | 28 | 54 | 18 | – | 46 |
| B registers | 23 | 28 | 8 | 18 | 53 |
| C physical ports | 10 | 27 | 9 | – | 33 |
| D routing/compile | 8 | 60 | 12 | 10 | 11 |
| Total | 69 | 169 | 47 | 28 | 143 |

How the columns were counted:
- (c) includes A's c* items: theorems about one class rather than a comparison of two, still restated once.
- "Kept support" is definitions and lemmas that (c) statements name, such as `registerEncoding`/`registerDecoding`, the `PortMatching.perm` lemmas and `regroupColor`. They stay as definitions in Channel, Sites or Geometry.
- Private proof data counts under (b).
- Some (c) items merge, so there are fewer core statements than (c) items:
  - one light-cone factorization theorem subsumes A's `dual_mul` and `trace_mul_mul_eq_*` family;
  - one blocking theorem `exists_blocked` gives both `exists_regrouped`;
  - one encoding theorem `Circuit.exists_encoded_of_isDimBounded` gives B items 1, 2 and 8. Items 3 and 7 stay as the one-layer lemma `Layer.exists_encoded`, because folding them in would lose "same cells".

Per-module counts:
- A:

  | Module | a | b | c | d |
  |---|---|---|---|---|
  | Layer | 11 | 13 | 6 | 13 |
  | Conversion | 6 | 16 | 3 | 9 |
  | Feedforward | 1 | 3 | 0 | 0 |
  | WholeSiteChannels | 0 | 2 | 2 | 3 |
  | OnsiteChannelProduct | 1 | 2 | 0 | 6 |
  | SiteBlocking | 4 | 4 | 4 | 3 |
  | DataInitialization | 1 | 1 | 1 | 5 |
  | ApproximateConversion | 1 | 5 | 1 | 5 |
  | AsymptoticConversion | 2 | 4 | 1 | 0 |
  | DimensionBoundedConversion | 1 | 4 | 0 | 2 |

- B:

  | Module | a | b | c | support | d |
  |---|---|---|---|---|---|
  | RegisterEncoding | 2 | 5 | 1 | 6 | 3 |
  | RegisterChannelLift | 0 | 5 | 0 | 0 | 15 |
  | RegisterEnvironment | 2 | 3 | 0 | 0 | 3 |
  | OnsiteRegisterEncoding | 5 | 5 | 2 | 0 | 1 |
  | PhysicalRegisterEncoding | 2 | 4 | 0 | 0 | 1 |
  | PortRegisters | 1 | 0 | 2 | 9 | 13 |
  | NativeRegisterWires | 5 | 2 | 1 | 0 | 11 |
  | EncodedChannelLayer | 1 | 1 | 1 | 0 | 2 |
  | EncodedChannelPlacement | 0 | 3 | 0 | 0 | 2 |
  | EncodedChannelProtocol | 5 | 0 | 1 | 3 | 2 |

- C:

  | Module | a | b | c | d |
  |---|---|---|---|---|
  | PhysicalPort | 3 | 6 | 0 | 0 |
  | PhysicalPortCodes | 5 | 4 | 0 | 13 |
  | PhysicalPortDilation | 0 | 0 | 1 | 1 |
  | PhysicalPortEmbedding | 2 | 2 | 0 | 0 |
  | PhysicalPortEnvironmentComposition | 0 | 8 | 0 | 10 |
  | PhysicalPortIO | 0 | 0 | 1 | 0 |
  | PhysicalPortLocalDilation | 0 | 3 | 3 | 7 |
  | PhysicalPortPureOutput | 0 | 0 | 2 | 1 |
  | PhysicalPortUnitaryCompilation | 0 | 0 | 1 | 0 |
  | NativePortLayer | 0 | 4 | 1 | 1 |

- D:

  | Module | a | b | c | support | d |
  |---|---|---|---|---|---|
  | PortMatching | 1 | 5 | 1 | 4 | 4 |
  | PortRouting | 2 | 13 | 2 | 0 | 1 |
  | PortChannelRouting | 0 | 8 | 2 | 0 | 0 |
  | PortSimulation | 2 | 5 | 1 | 1 | 1 |
  | PhysicalProtocolCompilation | 0 | 3 | 1 | 0 | 0 |
  | RegroupedProtocol | 1 | 16 | 3 | 5 | 5 |
  | BoundedPortPureOutput | 0 | 0 | 1 | 0 | 0 |
  | BoundedPortApproximateOutput | 0 | 0 | 1 | 0 | 0 |
  | AdaptiveConversion | 2 | 10 | 0 | 0 | 0 |

Two modules are notable:
- **AsymptoticConversion** has no Lean consumer. It is (d) if `ch33_local_quantum_circuits_approximate` is not carried over.
- **Measurement/AdaptiveRound and Measurement/Channel** (from your 3C.3 note) collapse to `Circuit.map` and `isKrausCPTP_map`. Section 5 covers what `AdaptiveRound` uses.

## 2. The classes (the (a) items), as restrictions of `Circuit`

The prelude (top of each file) defines these classes:
- `IsProtocol Γ T Φ`: unbranched, plain gates, trace-preserving local families, depth ≤ T, `map = Φ`.
  - On `ring N` between `Qudits (Fin N) d` and `Qudits (Fin N) e` this is `IsLocalChannelProtocol`.
  - On `portGeometry P` it is `IsPhysicalPortProtocol`.
- `IsUnitaryCircuit Γ T U`: on the port geometry, this is `IsPhysicalPortUnitary`.
- `IsBoundedProtocol Γ B T Φ`: `IsProtocol` plus `Circuit.IsDimBounded B`, every intermediate basis of size in [1, B]. This is `IsDimensionBoundedLocalChannelProtocol`.
- `IsAdaptiveProtocol Γ T Φ`: as `IsProtocol` with branching allowed. This is `IsAdaptiveChannelProtocol`.

The layer types translate as follows:
- `OnsiteChannel` is a layer with no cells.
- `ChannelLayer`/`RingLayer` is `Layer.ofCells` on `ring N`.
- `BondChannelLayer` is a layer of any geometry.

`Config (Qudits (Fin N) d)` is definitionally `Fin N → Fin d`, so TNLean's matrices typecheck unchanged.

One generalisation: the core allows non-uniform intermediate systems. TNLean's classes are uniform at every time step, so a (c) theorem with a class hypothesis becomes stronger. None of the restatements needed uniformity.

## 3. Hypothesis changes against the source (faithfulness)

No restatement adds a hypothesis that its ring or port corollary cannot discharge. The changes are:
- **Added `hpos`: every cell has positive cost** (group A, general-geometry forms). Core depth counts layers using a cell of positive cost, while TNLean counts layers. The ring corollaries discharge it with `ring_cost_pos`, so the source statements carry no new hypothesis.
- **`channelCircuitDual_mul_of_disjoint_lightCone` adds `IsUnbranched` and `Forall IsTP`.** TNLean's layer lists have both by construction.
- **Dropped `PosSemidef` in `trace_mul_mul_eq_*`.** Only trace 1 is used.
- **Dropped hypotheses that served TNLean encodings:**
  - `2 ≤ N`, `0 < m`: `exists_pairKraus`, `pairData` injective;
  - `[NeZero d]`, `hd`: the `Fin (d^k)` digit encoding;
  - `i ≠ i+1`: flattened `pairData`.
  The docstrings say which hypothesis served which encoding.
- **Narrowed, the one case: `of_routed_family`** (PortChannelRouting). The commuting family becomes the gates of one `Layer.ofCells`, so commutation becomes disjointness of cells. Both consumers, `NativePortLayer` and `PortSimulation`, fit. Under the faithfulness rule this is a scope restriction and needs a paper-gap note before a `\leanok` on the source label.
- **Two group A statements whose premises the agents did not verify:**
  - `IsBoundedProtocol.dimension_bounds` assumes trace-preserving layers have nonempty index types;
  - `disjoint_iterate_neighbourhood_of_isSeparatedBy` assumes the iterated core neighbourhood on `ring N` is TNLean's ring ball.

## 4. Core gaps

Each gap is a definition (some with `sorry` bodies) in a prelude or gaps section of the files.

- **Geometry → `Circuit/Geometry`**:
  - `ring N`, the open chain `chain N` and `IsSeparatedBy`, with separation 2T ⇒ disjoint T-fold neighbourhoods.
  - The port geometry `portGeometryOf site port` on any wire type. Its cost-0 cells are all finsets inside one fibre (down-closed); this is needed so `Geometry.Hom` works for appended wires. Its cost-1 cells are the port ring bonds.
  - `appendGeometry` on `V ⊕ Fin A` (replaces `PhysicalPortLayout.append`), and the register ring.
- **Sites → `ManyBody/Sites`**:
  - `Qudits`.
  - The embedding identification. The general form `RegionConfig X (D.map ι) ≃ RegionConfig (X ∘ ι) D` gives your `D = univ` case.
  - Blocking: `blockSystem f X` (basis at `s'` = configurations of the fibre), `blockConfigEquiv`, `blockRegionConfigEquiv`, and "blocking commutes with `place`". This is B item 6.
  - The site-permutation operator `relabelOp` (TNLean `permOp`).
  - Placement at the level of maps: `(placeFamily D K).map` as the tensor product with the identity, and the Schrödinger-picture factorization of a layer (G2/G3 of B).
- **Core → `Circuit/Core`**:
  - an onsite-layer constructor (no cells) and the one-layer circuit;
  - `IsDimBounded` with `comp`, `mono` and `mapLayers` lemmas;
  - light cones: trace duality `tr(c.map ρ · A) = tr(ρ · c.dual A)`, multiplicativity of `dual` on operators with disjoint light cones, and the product-input factorization (G1–G3 of A);
  - `map_step` and `map_append` (Schrödinger picture);
  - preparation and discard onsite families `PUnit → Fin d` and `Fin d → PUnit`, and moving between uniform systems on different site sets (`freshInput`, `discardEnvironment` in C);
  - functoriality of `mapSites` and `map_mapSites`;
  - unbranched substitution (each layer replaced by an unbranched circuit, depth ≤ K·depth, map preserved; section 6);
  - the adjoint of an unbranched unitary circuit, beyond `seq`. This gives `IsPairProduct.star` for `conjugate_permOp`.
  - Already announced for 3C.3: `seq_append`, unitarity of the unique Kraus operator, depth of `seqAdjoint`.
- **Channel → `Channel/`**:
  - a Kraus family chosen from `IsKrausCPTP`, and composition of Kraus families (the decoder as an onsite family);
  - gate-level fresh-environment dilation (C G7);
  - `exists_qudit_freshEnvironment_unitary`, moved to `Channel/EnvironmentDilation`;
  - `exists_product_of_pure_marginal`, a matrix lemma.
- **Analysis**: the trace norm on any finite index (`Config`) and its contractivity under `Circuit.map`. `traceNorm` exists only on `Fin D`.

## 5. Consumers whose statements must survive

- **`MPS/Preparation/BlockUnitary` and `QuantitativeSitePermutation`** each use only `isPairProduct_permOp_swap` (lines 112 and 93), and nothing from the `PortMatching` namespace.
  - Core form: `isPairProduct_permOp_swap (i j : Fin N) : IsUnitaryGateCircuit (chain N) (2 * N) (relabelOp d (Equiv.swap i j))`.
  - A proved-equivalence statement `isUnitaryGateCircuit_chain_iff` shows the class is `IsPairProduct` verbatim, so TNLean can redefine `IsPairProduct` as it.
  - Their closure lemmas map as `one` = `done`, `mul` = `comp` with `gateCount_comp` (note `kraus (c.comp c') = c'.kraus * c.kraus`), and `list_prod` = a fold of `comp`.
  - `star`, used by `conjugate_permOp`, is the one missing piece: the adjoint gap above.
- **`Measurement/AdaptiveRound`** uses `IsAdaptiveChannelProtocol` with its `.instrument`/`.onsite` constructors, `IsLocalChannelProtocol.adaptive` and `.comp`. These become `Circuit.step`, an onsite layer, forgetting `IsUnbranched`, and `Circuit.comp`.

## 6. Your question: substitution on branching circuits

Not needed; unbranched substitution suffices:
- `IsDimensionBoundedLocalChannelProtocol`, `IsLocalChannelProtocol` and the port classes have no branching.
- `exists_physicalPortSimulation` compiles words, `List (FixedRegisterOperation q N)`, at the map level (`dataChannelLift` is a monoid hom; `dataChannelLift_channelLayer` handles one layer).
- Both `BoundedPort*` theorems go through `exists_physicalPortIO`, with the same unbranched hypothesis.
- The only branching class, `IsAdaptiveChannelProtocol`, is named only in `Measurement/AdaptiveConversion` and `AdaptiveRound`. No port, regrouping or dimension-bound file uses it.
- A branching substitution would also need each compiled layer's branches matched to the layer's outcomes, which TNLean never provides. Blocking could be done at the Kraus level, since merged gates keep product outcomes, but nothing requires it.

## 7. Map's `extendRegionEquiv` and the Sites identification

They are one notion. Map's `extendRegionEquiv e W X D : RegionConfig (extendSystem e W X) (D.map (siteEmb e)) ≃ RegionConfig X D` splits into two steps:
1. the general identification `RegionConfig X' (D.map ι) ≃ RegionConfig (X' ∘ ι) D` for an embedding `ι`, here `siteEmb e`;
2. the sitewise cast `extendSystem e W X ∘ siteEmb e = X`, which is `Sum.elim X W (e (e.symm (inl s)))`, so it holds only propositionally. This is the private `extendSiteEquiv`.

The old `regionSiteEquiv` was `D.equivMap`, already replaced by Mathlib's `Finset.equivMap`, and the old `liftRegionEquiv` is today's `extendRegionEquiv`.

Your `RegionConfig X (Finset.univ.map e) ≃ Config (X ∘ e)` is step 1 at `D = univ`. Recommendation: put the general-`D` form in `ManyBody/Sites`. `extendRegionEquiv` then becomes that composed with the sitewise cast, and the private cast lemmas of `Core/Map` reduce to the cast. #1116 unchanged, as asked.

## 8. Target layout and import layers

| Module | Contents | From |
|---|---|---|
| `Circuit/Geometry/Ring.lean` | `ring`, `chain`, separation and neighbourhood lemmas | A, D |
| `Circuit/Geometry/Port.lean` | `PhysicalPortLayout`, `portGeometryOf`, `appendGeometry`, register layout | C, D |
| `Circuit/Model/Protocol.lean` | `IsProtocol`, `IsUnitaryCircuit`, `IsBoundedProtocol` (with `IsDimBounded` in Core), `IsAdaptiveProtocol`, closure lemmas as one-liners (or none, they are (b)) | A, D |
| `Circuit/Model/Conversion.lean` | `IsConversion`, the factorization corollaries on the ring, blocked conversions | A |
| `Circuit/Model/Approximate.lean` | `IsApproxConversion`/`IsAsymptoticConversion` and `.trans` | A |
| `Circuit/Model/PairProduct.lean` | `IsUnitaryGateCircuit`, `isPairProduct_permOp_swap` (consumer-facing) | D |
| `Circuit/Compile/Blocking.lean` | `exists_blocked`, `exists_regrouped_layers`, `exists_regrouped(_bounded)`, the SiteBlocking (c) items | A, D |
| `Circuit/Compile/Encoding.lean` | `Layer.exists_encoded`, `Circuit.exists_encoded_of_isDimBounded`, register round trips | B |
| `Circuit/Compile/Routing.lean` | `routingPermutation`, `selected_layer`, `register_matching`, `of_register_routing`, `of_routed_family` | B, D |
| `Circuit/Compile/PortSimulation.lean` | `dataChannelLift_channelLayer`, `matchingChannel_…`, `wholeSite_*`, `exists_physicalPortSimulation` | A, C, D |
| `Circuit/Compile/Dilation.lean` | `exists_selected_onsite_dilation`, `exists_onsite_appended_dilation`, `exists_appended_unitary_dilation(_pure_output)` | C |
| `Circuit/Protocol/Ports.lean` | `exists_physicalPortIO`, `exists_physicalPortUnitaryIO`, `exists_physicalPort_pure_output`, `…_approximate_output` | C, D |
| `Circuit/Protocol/Adaptive.lean` | adaptive class instances for AdaptiveRound | D |

Import layers (the `docs/import_structure.md` table and `check_import_layers.py`):
- `Circuit/Model`: matrix foundations, channels, Sites, Gates, Circuits (Core, Geometry).
- `Circuit/Compile`: the same plus `Circuit/Model`.
- `Circuit/Protocol`: the same plus `Circuit/Model` and `Circuit/Compile`.
- Nothing in Core, Geometry, Gate, Algorithm or Party imports these. Sites gains `Qudits`, the embedding identification, blocking and `relabelOp`.

## 9. Blueprint chapter 33

The four TNLean files move into the QICLean blueprint as one part after the circuits chapters:
- `ch33_local_quantum_circuits_channels` becomes the classes as restrictions, the light-cone factorization, and blocking/regrouping.
- `_physical_ports` becomes the port geometry, routing, port simulation and dilation.
- `_approximate` becomes approximate and asymptotic conversion (needs the trace-norm gap). Its asymptotic half has no Lean consumer; drop it there, or keep it as a corollary.
- `_adaptive` becomes adaptive protocols as branching circuits; every result is (b), so it is a short section with `\lean` to the core.

In each:
- Definitions of the (a) classes become definitions stated as restrictions.
- (b) results lose their own `\lean`/`\leanok` and cite the core theorem.
- (c) results keep their labels, with `\lean` to the restated statements.
- `of_routed_family` gets a scope-restriction note.

TNLean keeps a stub chapter pointing to the QICLean part, and its labels used by later chapters stay as cross-references.

## 10. Proposed order for the port

1. Sites PR: `Qudits`, the embedding identification, blocking, `relabelOp` (with the `Q n` replacement).
2. Geometry PR: `ring`, `chain`, `portGeometryOf`/`appendGeometry`.
3. Core PR: onsite layer, `IsDimBounded`, prepare/discard, `map_step`/`map_append`, `mapSites` functoriality, unbranched substitution, light-cone factorization.
4. Model.
5. Compile, in two PRs: blocking and encoding, then routing, simulation and dilation.
6. Protocol.

The Channel and Analysis gaps (Kraus composition, dilation, trace norm) go in with the first PR that needs them.
