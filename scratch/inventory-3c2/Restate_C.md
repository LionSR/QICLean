# Group C (physical ports): restatement in the circuit core

File: /tmp/claude-0/-home-user-QICLean/c52878a5-a12c-59c1-8785-bc49c23526e9/scratchpad/inv/Restate_C.lean
(Prelude copied verbatim, then `namespace Inventory.C`.)

## Table

| TNLean name | TNLean file | core statement name | changes of hypotheses | gaps used |
|---|---|---|---|---|
| `exists_qudit_freshEnvironment_unitary` | PhysicalPortLocalDilation | `exists_qudit_freshEnvironment_unitary` | `Φ` with `IsKrausCPTP Φ` becomes `K : KrausFamily` with `K.IsTP` (the equivalent Kraus form, which is the form a gate takes); conclusion about `K.map`. Otherwise verbatim (`Fin m → Fin d` = `Config (Qudits (Fin m) d)` by definition) | none |
| `exists_product_of_pure_marginal` (private) | PhysicalPortPureOutput | `exists_product_of_pure_marginal` | none (verbatim, made public) | none |
| `exists_selected_onsite_dilation` | PhysicalPortLocalDilation | `exists_selected_onsite_dilation` | dropped the enumeration `e : Fin m ↪ Fin W` with `he` (TNLean encoding): it becomes a cell `D` with `hD : ∀ w ∈ D, P.site w = i`, and `m = D.card`. `IsKrausCPTP Φ` becomes a TP gate `K : KrausGate D …`; `registerChannelLift e Φ` becomes the one-gate circuit `Circuit.seq [Layer.single (.inl ⟨D, i, hD⟩) K]` | G1 `portGeometryOf`, `appendGeometry`; `freshInput`, `discardEnvironment` |
| `exists_onsite_appended_dilation` | PhysicalPortLocalDilation | `exists_onsite_appended_dilation` | operators `K a` in `supportedOperators` of the fibre with `∑ Kᴴ K = 1` become a TP gate on the fibre cell (`kraus_single` is the identification); `rectangularKrausMap K` becomes the map of the one-gate circuit | same as above |
| `IsPhysicalPortProtocol.exists_appended_unitary_dilation` | PhysicalPortDilation | `exists_appended_unitary_dilation` | none: `IsPhysicalPortProtocol P T Φ` becomes `IsProtocol (portGeometry P) T Φ`, `IsPhysicalPortUnitary (P.append owner) T U` becomes `IsUnitaryCircuit (appendGeometry P.site P.port owner) T U` on wires `Fin W ⊕ Fin A` (no `Fin (W + A)` encoding), `singleKrausMap U` becomes `(KrausFamily.single U).map` | G1/G2 `appendGeometry`; `freshInput Function.Embedding.inl`, `discardEnvironment` |
| `IsPhysicalPortProtocol.exists_appended_unitary_dilation_pure_output` | PhysicalPortPureOutput | `exists_appended_unitary_dilation_pure_output` | none; `appendMatrixSplit U *ᵥ (fixedEnvEmbedding 0 *ᵥ ψ)` at `(x, e)` becomes `U *ᵥ freshVector inl d ψ` at a configuration `z` of `Fin W ⊕ Fin A`, and `φ x * η e` becomes `φ (z ∘ inl) * η (z ∘ inr)` (no split equivalence) | as above, and `freshVector` |
| `PortRegisters.dataChannelLift_channelLayer` | NativePortLayer | `dataChannelLift_channelLayer` | `L : ChannelLayer (d ^ k) N` becomes `Layer.ofCells cells hcells g` on `ring N` with every `g b` TP (identity elsewhere, as in `BondChannelLayer`); `layout N k` (wires `Fin (N * (1 + k + k))`) becomes `registers N k` (wires `Fin N × Fin (1 + k + k)`). `hd`, `hN` kept | G1 `registers`; G3 `dataLift` |
| `IsDimensionBoundedLocalChannelProtocol.exists_physicalPortIO` | PhysicalPortIO | `exists_physicalPortIO` | none: `IsDimensionBoundedLocalChannelProtocol B T Ψ` becomes `IsBoundedProtocol (ring N) B T Ψ` (G4 in the Prelude); `wordInitialization (portWordCode d k)` becomes `freshInput (portWire N k) d` (input on the port wire `(i, 0)`, every other wire at `0`); `let k` inlined as `Nat.clog d B` | G1 `registers`, `portWire`; `freshInput` |
| `IsDimensionBoundedLocalChannelProtocol.exists_physicalPortUnitaryIO` | PhysicalPortUnitaryCompilation | `exists_physicalPortUnitaryIO` | none; same translations as the two above; wires `(Fin N × Fin (1 + k + k)) ⊕ Fin A` | G1 `appendGeometry Prod.fst (portWire N k) owner`; `freshInput` (twice), `discardEnvironment` |

## Gap definitions added (section `### Gaps`)

* `portGeometryOf site port : Geometry V`: G1 port geometry on any wire type (cost-0 cells are all finsets inside one fibre, i.e. down-closed, G2; cost-1 ring bonds on the ports). `portGeometry_eq` (proved): Prelude's `portGeometry P = portGeometryOf P.site P.port`.
* `appendGeometry site port owner : Geometry (V ⊕ Fin A)`: G1 `PhysicalPortLayout.append`, new wire `a` at site `owner a`, same ports.
* `portWire N k : Fin N ↪ Fin N × Fin (1 + k + k)`: the port wire `(i, 0)` (concrete).
* `registers N k : Geometry (Fin N × Fin (1 + k + k))`: G1 `PortRegisters.layout N k` without the `Fin (N * …)` encoding (concrete).
* `freshInput ι d`: change of site set along `ι : V ↪ V'`, input on `ι V`, other wires prepared at `0` (`appendEnvironmentInput`; `wordInitialization (portWordCode d k)` for `ι = portWire`). Concrete, linearity proved. In the core it would be a cost-0 onsite `PUnit → Fin d` layer on idle sites after `mapSites`, but the core has no map between configurations of uniform systems on different site sets.
* `freshVector ι d ψ`: the vector form, `ψ ⊗ |0⟩` (concrete).
* `discardEnvironment V R d`: partial trace over the wires `R` of `V ⊕ R` (`discardAppendedEnvironment`; in the core a cost-0 onsite `Fin d → PUnit` layer). Concrete, linearity proved.
* `dataLift N k d`: G3 blocking (`dataChannelLift`), a native `Fin (d ^ k)` ring channel acting on the `k` data wires of each site via `Fin (d ^ k) ≃ (Fin k → Fin d)`, identity on port and scratch wires. Body `sorry`.

Prelude notions used: `Qudits`, `ring`, `PhysicalPortLayout`, `portGeometry`, `IsProtocol`, `IsUnitaryCircuit`, `IsBoundedProtocol` (G4 `Circuit.IsDimBounded`), `IsUnitaryLocal`. `blockSystem`/`blockConfigEquiv` are not used: the data wires are a sub-block of each site, not a partition of the sites, so `dataLift` is stated directly.

## Typecheck

Command:
    cd /home/user/QICLean && PATH=$HOME/.elan/bin:$PATH lake env lean /tmp/claude-0/-home-user-QICLean/c52878a5-a12c-59c1-8785-bc49c23526e9/scratchpad/inv/Restate_C.lean

Output (complete):
    …/Restate_C.lean:21:18: warning: declaration uses `sorry`
    …/Restate_C.lean:124:18: warning: declaration uses `sorry`
    …/Restate_C.lean:208:18: warning: declaration uses `sorry`
    …/Restate_C.lean:234:8: warning: declaration uses `sorry`
    …/Restate_C.lean:254:8: warning: declaration uses `sorry`
    …/Restate_C.lean:277:8: warning: declaration uses `sorry`
    …/Restate_C.lean:304:8: warning: declaration uses `sorry`
    …/Restate_C.lean:332:8: warning: declaration uses `sorry`
    …/Restate_C.lean:363:8: warning: declaration uses `sorry`
    …/Restate_C.lean:389:8: warning: declaration uses `sorry`
    …/Restate_C.lean:412:8: warning: declaration uses `sorry`
    …/Restate_C.lean:439:8: warning: declaration uses `sorry`
(…/ = /tmp/claude-0/-home-user-QICLean/c52878a5-a12c-59c1-8785-bc49c23526e9/scratchpad/inv/.)
Lines 21 and 124 are the Prelude's `regionConfigMapEquiv` and `blockConfigEquiv`; line 208 is `dataLift`; the other 9 are the 9 restated theorems. No errors. Neither repository was edited.
