# Restate_B: group B (registers and encodings), the (c) items restated

File: /tmp/claude-0/-home-user-QICLean/c52878a5-a12c-59c1-8785-bc49c23526e9/scratchpad/inv/Restate_B.lean
(it starts with Prelude.lean byte for byte, checked with `cmp`, followed by `namespace Inventory.B`).

## Table

| # | TNLean name | TNLean file | Core statement (`Inventory.B.`) | Hypothesis changes | Gaps used |
|---|---|---|---|---|---|
| 1 | `registerDecoding_encoding` | RegisterEncoding | `registerDecoding_encoding` | none. Stated on maps, with `(KrausFamily.single (registerEncoding e)).map` in place of `singleKrausMap`; no positivity of `ρ` needed, as in the source | `registerEncoding`, `registerDecoding` (c-supp, real bodies) |
| 2 | `OnsiteChannel.decodeRegisters_encodeRegisters` | OnsiteRegisterEncoding | `map_encodeCircuit_comp_decodeCircuit`: `((encodeCircuit Γ e).comp (decodeCircuit Γ e ρ hρ htr)).map ev = id` | none (keeps `hρ`, `htr`). Generalised from `Fin m ↪ Fin q` on `ι` to any systems `X s ↪ Y s` on any geometry | onsite layer, one-layer circuit, G4 decoder |
| 3 | `OnsiteChannel.encoded_map_encodeRegisters` | OnsiteRegisterEncoding | `Layer.exists_encoded`, the case with no cells | none. TNLean's explicit `Φ.encoded` becomes `∃ L'` with `L'.cells = ∅ = L.cells`; TP of `Φ` (built into `OnsiteChannel`) becomes `hL` | onsite layer, one-layer circuit, G4 (for the proof) |
| 7 | `ChannelLayer.exists_encodedRegisters` | EncodedChannelLayer | `Layer.exists_encoded`, the case `Γ = ring N`, `X = Y`, `e = f` | dropped `2 ≤ N` and `0 < m`: they only served `exists_pairKraus` (extracting two-site Kraus operators from global supported ones). Core gates are already local. `L'.bonds = L.bonds` becomes `L'.cells = L.cells`; TP built into `ChannelLayer` becomes `hL` | same as 3 |
| 8 | `IsDimensionBoundedLocalChannelProtocol.exists_fixedRegisterWord` | EncodedChannelProtocol | **core theorem** `Circuit.exists_encoded_of_isDimBounded` (any geometry, any systems); plus the class-level ring form `IsBoundedProtocol.exists_fixedRegisterWord` | dropped `2 ≤ N` (as in 7). The codes are arbitrary `e`, `f` (TNLean's `boundedAlphabetCode = Fin.castLEEmb` is one instance, so the conclusion is stronger). The depth equality `wordDepth = T` becomes `c'.depth = c.depth` (core theorem) and `depth ≤ T` (class form, because `IsBoundedProtocol` bounds depth). Branching is allowed, with `c.IsUnbranched → c'.IsUnbranched` added to the conclusion | `Circuit.IsDimBounded` (Prelude G5), `ring`, `IsBoundedProtocol`/`IsProtocol` (Prelude), plus the gaps used by 3 and 7 |
| 4 | `PortRegisters.routingPermutation_isPhysicalPortUnitary` | PortRegisters | `routingPermutation_isUnitaryCircuit`: `IsUnitaryCircuit (portGeometry (portRegisterLayout N k)) k (sitePermOp (routingPermutation K hK))` on `Qudits (Fin (N*(1+k+k))) d` | none. `ringBond` becomes `(ring N).cell` | `sitePermOp`, `portRegisterLayout`, `dataWire`/`scratchWire`, `matchingPerm`, `selection`, `routingPermutation` (TNLean definitions carried over as statement data) |
| 5 | `PortRegisters.routingPermutation_pairData_site` | PortRegisters | `site_routingPermutation_dataWire` (a conjunction, one conjunct for the data wires of site `i` and one for those of site `i+1`) | dropped `i ≠ i + 1`: it only made the flattened `pairData : Fin (k+k) ↪ wires` injective. The two registers are quantified separately (`dataWire i t`, `dataWire (i+1) t`) | same as 4 |
| 6 | `PortRegisters.dataOperator_embedOp` | NativeRegisterWires | `reindex_blockConfigEquiv_place`: blocking along `f : S → S'` commutes with `place` (region `D'` ↦ preimage) | none on the core content. Two encodings are split off: the basis relabelling `finFunctionFinEquiv : (Fin k → Fin d) ≃ Fin (d^k)`, and the placement of the data wires among the port and scratch wires (idle sites, i.e. transitivity of placement). TNLean's `e : Fin s ↪ Fin N` with operator `A` is the case `D' = univ.map e` (via the Prelude's `regionConfigMapEquiv`) | `blockSystem`, `blockConfigEquiv` (Prelude G6), `blockRegionConfigEquiv` (new G6) |

How the merge came out. Item 8 is the one core theorem. Its proof is a structural induction on `Circuit`, with `Layer.exists_encoded` (items 3 and 7) as the step and items 1 and 2 as the retraction lemmas. The fallback densities come from `0 < card` inside `IsDimBounded`. Items 3 and 7 are kept as a separate layer lemma, not folded into the circuit theorem. The circuit theorem only gives `depth` equality, so folding them in would lose their exact conclusion: one layer with the same cells. Folding them in is possible only by adding a "same shape layer by layer" predicate on circuits; I did not add one. Item 3 is the no-cell case of `Layer.exists_encoded`, and item 7 is the ring, same-alphabet case.

## Definitions added (all in `Inventory.B`, sections `Gaps*` at the top of the namespace)

- `registerEncoding` (c-supp, real body): the isometry `(1).submatrix id e` of `e : α ↪ β`.
- `registerDecoding` (c-supp, real body): `Matrix.supportCompletion (single Vᴴ).map (V Vᴴ) ρ`.
- `registerDecoder` (**G4**, sorry): a `KrausFamily β α` for the completed decoder of a density `ρ`. Specs: `map_registerDecoder` (sorry) and `isTP_registerDecoder` (sorry, TNLean `registerDecoding_isKrausCPTP`).
- `onsiteLayer` (**gap: layer with no cells**, real body): `cells := ∅`, onsite families `K s`. This is TNLean's `OnsiteChannel`, with the dimension allowed to change.
- `layerCircuit` (**gap: one-layer circuit**, real body): `.step L fun _ ↦ .done Y`.
- `encodeCircuit` / `decodeCircuit` ((a) items, real bodies): the onsite code and decoder as one-layer circuits.
- `sitePermOp` (**gap: site-permutation operator**, real body): TNLean `permOp`, `|x⟩ ↦ |x ∘ π⁻¹⟩`.
- `portRegisterLayout`, `dataWire`, `scratchWire` (statement data, real bodies): TNLean's `layout`, `data` and `scratch` coordinates.
- `matchingPerm` (statement data, the commutation proof is `sorry`): TNLean `PortMatching.perm`, over `(ring N).cell`.
- `selection` (c-int, the injectivity proof is `sorry`) and `routingPermutation` (c-int, real body): TNLean's definitions.
- `blockRegionConfigEquiv` (**G6**, sorry): the region form of the Prelude's `blockConfigEquiv`.

## Typecheck

```
$ cd /home/user/QICLean && PATH=$HOME/.elan/bin:$PATH lake env lean /tmp/claude-0/-home-user-QICLean/c52878a5-a12c-59c1-8785-bc49c23526e9/scratchpad/inv/Restate_B.lean
```
Exit code 0. Output: 16 lines, all `warning: declaration uses 'sorry'`, at lines 21, 124, 160, 165, 171, 246, 252, 272, 289, 307, 341, 378, 394, 420, 437, 460. Lines 21 and 124 come from the Prelude (`regionConfigMapEquiv`, `blockConfigEquiv`); the other 14 come from this group. There are no other messages. Neither repository was modified (`git status` in QICLean is clean).
