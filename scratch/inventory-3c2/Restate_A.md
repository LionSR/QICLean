# Restatement, group A (channel core)

File: /tmp/claude-0/-home-user-QICLean/c52878a5-a12c-59c1-8785-bc49c23526e9/scratchpad/inv/Restate_A.lean
(Prelude copied byte for byte, then `namespace Inventory.A`; nothing in either repository was edited.)

## Table

| TNLean name | TNLean file | core statement (`Inventory.A.`) | changes of hypotheses | gaps used |
|---|---|---|---|---|
| `BondChannelLayer.dual_mul` | Channel/Layer | `Layer.dual_mul_of_disjoint_lightCone` | disjoint `bondNeighbourhood`s become disjoint one-layer `L.lightCone`s, which is weaker because `Layer.lightCone_subset_neighbourhood`; TP is now `L.Forall ev IsTP` (it was a structure field); any gate family, any systems `X → Y` | G2 |
| `OnsiteChannel.dual_mul` | Channel/Conversion | `Layer.dual_mul_of_cells_eq_empty` | none (`OnsiteChannel` is a layer with `cells = ∅`; its TP field becomes `Forall IsTP`) | G2 |
| `channelCircuitDual_mul_of_disjoint_lightCone` | Channel/Layer | `Circuit.dual_mul_of_disjoint_lightCone` | `lightCone bond X Ls.length` becomes `c.lightCone R`; adds `IsUnbranched` and `Forall IsTP` (TNLean's layer lists are unbranched and TP by construction) | G2 |
| (core theorem, subsumes the rows above and below) | — | `Circuit.trace_map_prodOp_mul_mul` | input `prodOp σ` with `tr σₛ = 1`; disjoint `c.lightCone`s | G1, G2, G3 |
| `IsBondChannelPreparedInDepth.trace_mul_mul_eq` | Channel/Layer | `IsConversion.trace_mul_mul_eq` | `Ls.length = T` becomes depth `≤ T`; `PosSemidef σᵢ` dropped (only `tr σᵢ = 1` is used, as in the Conversion version); `hpos` added, the core form of "bonds cost one"; light cone `lightCone bond X T` becomes `Γ.neighbourhood^[T] R` | G1–G3 |
| `IsLocalChannelProtocol.exists_dual` (also covers the ring `ChannelLayer.dual_mul` and `channelCircuitDual_mul`) | Channel/Conversion (Layer) | `IsProtocol.exists_dual` | generalized to any geometry with `hpos`; the ring is `Γ = ring N` with `ring_cost_pos`; `neighbourhood X T` becomes `(ring N).neighbourhood^[T] X` | G1, G2, G4 |
| `trace_mul_mul_eq_of_isLocalChannelConversion` and `trace_mul_mul_eq_of_isChannelPreparedInDepth` | Channel/Conversion, Channel/Layer | `trace_mul_mul_eq_of_isConversion_ring` (one statement for both) | `finKronecker σ₀` becomes `prodOp σ₀`; for the Layer version `PosSemidef` is dropped and `d' = d`; intermediate systems need not be uniform (a larger class) | G1–G4 (`IsSeparatedBy`) |
| `preimage_siteBlock_neighbourhood_subset` | Channel/SiteBlocking | `preimage_ringBlock_neighbourhood_subset` | none; TNLean's ring ball becomes the iterated `(ring _).neighbourhood` | G4, G5 (`ringBlock`) |
| `IsLocalChannelProtocol.exists_dual_comp_blockSites` | Channel/SiteBlocking | `IsProtocol.exists_dual_comp_block` | generalized to any blocking `f : S → S'` and any coarse geometry with `hpos`; `[NeZero d]` dropped because it served the digit encoding `Fin (d^k)`, which `blockSystem` replaces; `blockSites` becomes `blockMatrix` | G1, G2, G5 |
| `IsBlockedLocalChannelConversion.exists_dual` | Channel/SiteBlocking | `IsBlockedConversion.exists_dual_ring` | `[NeZero d]` dropped (same reason); the blocked basis is `blockSystem (ringBlock M k) _`, not `Fin (d^k)` | G1, G2, G4, G5 |
| `trace_mul_mul_eq_of_isBlockedLocalChannelConversion` | Channel/SiteBlocking | `trace_mul_mul_eq_of_isBlockedConversion_ring` | none beyond the encoding (`finKronecker` becomes `prodOp`) | G1–G5 |
| `wholeSite_onsiteChannel` | Channel/WholeSiteChannels | `wholeSite_onsiteChannel` | any layout `P` instead of `layout N k`; `hd : 0 < d` dropped (digit encoding); `nativeChannelReindex` becomes `unblockMap P.site`; `OnsiteChannel` becomes `onsiteLayer` with TP families | G5, G9, G10 |
| `wholeSite_local` | Channel/WholeSiteChannels | `wholeSite_local` | `IsKrausCPTP Φ` is given as a TP Kraus family `K`; the register embedding `e` with every register at site `i` becomes the site `i` itself (`e` is injective, so it names that one block); `hd` dropped | G5, G9, G10 |
| `wordInitialization_data_eq_physicalEncoding` | Channel/DataInitialization | `map_onsiteEmbedding_comp` | restated as the class fact: two onsite layers of embedding isometries equal one onsite layer of the composite embedding. The port coordinate identity `dataWordCode c = prep.trans enc` and the wire picture (`unblockMap`) are not stated | G11 (`embeddingMatrix`), G9 |
| `IsApproxLocalChannelConversion.trans` | Channel/ApproximateConversion | `IsApproxConversion.trans` | none (Hermitian `ρ, σ` kept); generalized to any geometry and systems; `∃ S ≤ T` is absorbed into `IsProtocol`'s depth `≤ T` | G7 (`cfgTraceNorm`) |
| `IsAsymptoticLocalChannelConversion.trans` | Channel/AsymptoticConversion | `IsAsymptoticConversion.trans` | none | G7 |
| `IsDimensionBoundedLocalChannelProtocol.dimension_bounds` | Channel/DimensionBoundedConversion | `IsBoundedProtocol.dimension_bounds` | stated for any geometry (inventory verdict b) | G6 (Prelude `IsDimBounded`) |
| `.mono_bound` | same | `IsBoundedProtocol.mono_bound` | none (b) | G6 |
| `.comp` | same | `IsBoundedProtocol.comp` | none (b) | G6 |
| `IsLocalChannelProtocol.exists_dimension_bound` | same | `IsProtocol.exists_dimension_bound` | `hd : 0 < d` becomes `∀ s, Nonempty (X s)` (b) | G6 |

Items not restated:
- Feedforward and OnsiteChannelProduct have no (c) items.
- `IsLocalChannelPhaseEquivalent.*` is a definition plus formal consequences of `.trans`.
- `tensorMapId_comp_zeroDataReferencePrep` is (b).

## Gap definitions added (section `/-! ### Gaps -/` of `Inventory.A`)

- `IsSeparatedBy`: G4. TNLean's ring separation, copied verbatim (needs `open Fin.CommRing`).
- `disjoint_iterate_neighbourhood_of_isSeparatedBy` (stated, `sorry`): G4. Separation `2T` gives disjoint `T`-fold neighbourhoods in `ring N`.
- `ring_cost_pos` (proved): G4. Every ring bond has positive cost.
- `IsConversion`: an exact conversion of depth ≤ T. This is a class restriction (TNLean's `IsLocalChannelConversion`), not a gap.
- `onsiteLayer`: G9/G3. A layer with no cells and given onsite families. The core has no named constructor.
- `embeddingMatrix`: G11. The isometry of an embedding (TNLean's `registerEncoding`).
- `blockMatrix`: G5. A matrix as a matrix of `blockSystem f X`, via `blockConfigEquiv`.
- `unblockMap`: G5. A map of the blocked system read on the fine system.
- `IsBlockedConversion`: G5. A conversion after blocking.
- `ringBlock`: G4/G5. TNLean's `siteBlock`.
- `siteWires`: G10. The wires of a site of a port layout.
- `cfgTraceNorm`: G7. The trace norm on any finite index type, through `Fintype.equivFin` and `Matrix.traceNorm`.
- `IsApproxConversion`: an approximate conversion (class restriction, using G7).
- `IsAsymptoticConversion`: asymptotic conversion on rings (TNLean definition over the core class).

## Typecheck

```
$ cd /home/user/QICLean && PATH=$HOME/.elan/bin:$PATH lake env lean /tmp/claude-0/-home-user-QICLean/c52878a5-a12c-59c1-8785-bc49c23526e9/scratchpad/inv/Restate_A.lean
Restate_A.lean:21:18: warning: declaration uses `sorry`
Restate_A.lean:124:18: warning: declaration uses `sorry`
Restate_A.lean:146:8: warning: declaration uses `sorry`
Restate_A.lean:247:8: warning: declaration uses `sorry`
Restate_A.lean:265:8: warning: declaration uses `sorry`
Restate_A.lean:284:8: warning: declaration uses `sorry`
Restate_A.lean:296:8: warning: declaration uses `sorry`
Restate_A.lean:328:8: warning: declaration uses `sorry`
Restate_A.lean:367:8: warning: declaration uses `sorry`
Restate_A.lean:403:8: warning: declaration uses `sorry`
Restate_A.lean:428:8: warning: declaration uses `sorry`
Restate_A.lean:455:8: warning: declaration uses `sorry`
Restate_A.lean:491:8: warning: declaration uses `sorry`
Restate_A.lean:523:8: warning: declaration uses `sorry`
Restate_A.lean:552:8: warning: declaration uses `sorry`
Restate_A.lean:571:8: warning: declaration uses `sorry`
Restate_A.lean:597:8: warning: declaration uses `sorry`
Restate_A.lean:628:8: warning: declaration uses `sorry`
Restate_A.lean:650:8: warning: declaration uses `sorry`
Restate_A.lean:675:8: warning: declaration uses `sorry`
Restate_A.lean:687:8: warning: declaration uses `sorry`
Restate_A.lean:698:8: warning: declaration uses `sorry`
Restate_A.lean:713:8: warning: declaration uses `sorry`
```
(Paths are shortened here; the real output gives the full scratchpad path.) There are 23 warnings, all `declaration uses sorry`, and no errors. Lines 21 and 124 are the Prelude's own sorrys (`regionConfigMapEquiv`, `blockConfigEquiv`). `git status` in QICLean is clean.

Caveats:
- The statements were typechecked, not proved.
- The light-cone forms take disjoint *light cones* or *neighbourhoods*. They are not checked against TNLean beyond the reading in the inventory.
- `IsBoundedProtocol.dimension_bounds` relies on TP families forcing nonempty layer indices (otherwise `IsDimBounded` would not reach the output). This was argued, not checked.
