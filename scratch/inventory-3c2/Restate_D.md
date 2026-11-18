# Group D restated (routing and compilation)

File: /tmp/claude-0/-home-user-QICLean/c52878a5-a12c-59c1-8785-bc49c23526e9/scratchpad/inv/Restate_D.lean
(Prelude verbatim, then `namespace Inventory.D`). Neither repository was edited (QICLean `git status` clean).

## Table

| TNLean name | TNLean file | core statement | hypothesis changes | gaps used |
|---|---|---|---|---|
| `isPairProduct_permOp_swap` | Channel/PortMatching | `isPairProduct_permOp_swap` (+ support `isUnitaryGateCircuit_chain_iff`) | none | `chain`, `relabelOp`, `IsUnitaryGateCircuit` |
| `IsPhysicalPortUnitary.selected_layer` | Channel/PortRouting | `selected_layer` | `L : RingLayer d N` becomes any `Layer (ring N)` with `L.Forall ev IsUnitaryLocal` (generalised: unitary onsite families allowed); `embedOp e L.op` becomes `embedAlong d e (L.kraus ev i)` for every index `i` | `embedAlong` |
| `IsPhysicalPortUnitary.register_matching` | Channel/PortRouting | `register_matching` | the swap layer of the matching `K, hK` is generalised to any `k` unitary ring layers `L t`; `permOp (registerPermutation e (perm K hK))` becomes the product of the moved Kraus operators. TNLean's statement is the instance `L t = swap layer of K`, which needs the (b) lemmas `layer_op` and `embedOp_permOp_viaEmbedding` | `embedAlong` |
| `IsPhysicalPortProtocol.of_register_routing` | Channel/PortChannelRouting | `of_register_routing` | none (`K : Fin r → Matrix`, `∑ KᴴK = 1` is `K : KrausFamily`, `K.IsTP`) | `relabelOp`, `placeAlongFamily`, `embedAlong` |
| `IsPhysicalPortProtocol.of_routed_family` | Channel/PortChannelRouting | `of_routed_family` | the commuting family `F` on `s` with `hcomm` becomes the gates of one `Layer.ofCells` on any geometry on the wires (commutation is now disjointness of cells); `hF` per member becomes `hg` per placed gate. This is narrower than TNLean (arbitrary commuting endomorphisms), but it covers both consumers (NativePortLayer, PortSimulation) | `relabelConj`, `relabelOp` |
| `PortRegisters.matchingChannel_isPhysicalPortProtocol` | Channel/PortSimulation | `matchingChannel_isPhysicalPortProtocol` | dropped `hN : 2 ≤ N` (it only made `pairData i (i+1)` an embedding); `A, hA` on `K` become a `Layer.ofCells` of TP gates on `registerRing N k` | `portLayout`, `dataWires`, `registerRing` |
| `IsDimensionBoundedLocalChannelProtocol.exists_physicalPortSimulation` | Channel/PhysicalProtocolCompilation | `exists_physicalPortSimulation` | none dropped. The proofs `m, n ≤ d^k` (TNLean: `h.dimension_bounds` with `Nat.le_pow_clog`) are returned as `∃ hm hn`, not `let` | `portLayout`, `dataWires`, `DataReference`, `portEncoding`; Prelude `IsBoundedProtocol` |
| `ChannelLayer.exists_regrouped_layers` | Channel/RegroupedProtocol | `exists_regrouped_layers` | `ChannelLayer d (M*k)` becomes `Layer.ofCells K hK g` with TP gates; the output `List (ChannelLayer (d^k) M)` becomes layers on `ring M` over `blockSystem` with TP families; `channelCircuitMap` becomes `(seq Ls).map`; the `Fin (d^k)` encoding is dropped | `siteBlock`, `blockedMap`; Prelude `blockSystem`, `blockConfigEquiv` |
| `IsDimensionBoundedLocalChannelProtocol.exists_regrouped` | Channel/RegroupedProtocol | `exists_regrouped_bounded` | the end systems are generalised from `Fin d`/`Fin e` to any `X Z` | `siteBlock`, `blockedMap` |
| `IsLocalChannelProtocol.exists_regrouped` | Channel/RegroupedProtocol | `exists_regrouped` | dropped `hd : 0 < d` (it only served TNLean's route through `exists_dimension_bound`); the ends are generalised to any `X Z` | `siteBlock`, `blockedMap` |
| (support) | — | `exists_blocked` | the single blocking theorem on circuits (depth `≤ (2∣3)·depth`, `IsDimBounded B → IsDimBounded (B^k)`, `map` read through the blocking); the two `exists_regrouped` theorems are its corollaries | `siteBlock`, `blockedMap` |
| `IsDimensionBoundedLocalChannelProtocol.exists_physicalPort_pure_output` | Channel/BoundedPortPureOutput | `exists_physicalPort_pure_output` | none; `registerEncoding (wordCodeConfiguration (portWordCode d k))` becomes `portWordEncoding`, `wordInitialization` becomes `singleKrausMap V`, and `appendMatrixSplit W A d U` becomes `U.submatrix envSplit.symm envSplit.symm` | `portLayout`, `appendLayout`, `envSplit`, `appendEnvironmentInput`, `discardAppendedEnvironment`, `portWordEncoding` |
| `IsDimensionBoundedLocalChannelProtocol.exists_physicalPort_approximate_output` | Channel/BoundedPortApproximateOutput | `exists_physicalPort_approximate_output` | as above; `chainTraceNorm` (trace norm after reindexing to `Fin`) becomes QICLean's `rectangularTraceNorm` | same as above |

Generalisations (selected_layer, register_matching, the regrouping ends) weaken hypotheses and so give stronger statements. No restatement adds a hypothesis. The one narrowing is `of_routed_family`.

## Gap definitions added (section `### Gaps`)

- `chain N`: the open-chain geometry, cells `{p, p+1}` of cost 1 (TNLean's `IsNeighbourGate` cells).
- `relabelOp d σ`: TNLean's `permOp σ` on `Config (Qudits V d)`, verbatim (gap 3).
- `IsUnitaryGateCircuit Γ K U`: the gate-count analogue of `IsUnitaryCircuit`; on `chain n` it is `IsPairProduct`.
- `embedAlong d e A`: TNLean's `embedOp e A` for a uniform system, `place (univ.map e)` through `regionConfigMapEquiv` (gap 8).
- `placeAlongFamily d e K`: a Kraus family moved along `e` (gap 8).
- `relabelConj d σ Φ`: TNLean's `routingChannelConj σ Φ` (gap 8).
- `portLayout N k`: TNLean's `PortRegisters.layout` (proof fields `sorry`) (gap 9).
- `dataWires N k i`: the `k` data wires of site `i` (gap 9).
- `registerRing N k`: the ring whose cell `i` is the data wires of `i` and `i+1`, at cost 1 (gaps 1+9).
- `DataReference N k d`: the configurations of the port and scratch wires (gap 9).
- `portEncoding N k d c`: TNLean's `physicalEncoding (encodeRegisters (fun _ ↦ c)).map` (body `sorry`) (gap 9).
- `portWordEncoding N k d`: TNLean's `registerEncoding (wordCodeConfiguration (portWordCode d k))` (body `sorry`) (gap 9).
- `appendLayout P owner`: TNLean's `PhysicalPortLayout.append` (gap 7).
- `envSplit W A d`: `Config (Fin (W+A))` as `Config (Fin W) × Config (Fin A)` (gap 7).
- `appendEnvironmentInput W A d`: prepare the environment in `0` (gap 7).
- `discardAppendedEnvironment W A d`: partial trace over the environment (body `sorry`) (gap 7).
- `siteBlock M k`: the block of a site of `Fin (M*k)` (gap 4).
- `blockedMap f F`: a map read on `blockSystem f` through `blockConfigEquiv` (TNLean's `regroupChannel` without the `Fin (d^k)` encoding) (gap 4).

## Typecheck

    cd /home/user/QICLean && PATH=$HOME/.elan/bin:$PATH lake env lean /tmp/claude-0/-home-user-QICLean/c52878a5-a12c-59c1-8785-bc49c23526e9/scratchpad/inv/Restate_D.lean

The output is 21 lines, all `warning: declaration uses 'sorry'`, at lines 21, 124, 188, 215, 225, 230, 252, 283, 289, 310, 330, 352, 374, 398, 431, 449, 470, 494, 515, 555 and 608. There are no errors, and the exit code is 0. The full output is in Restate_D.out next to the file.

## Q1: `isPairProduct_permOp_swap` consumers

- `TNLean/Circuit/QuantitativeSitePermutation.lean:93`, in
  `theorem isPairProduct_permOp (τ : Equiv.Perm (Fin n)) : IsPairProduct d n (2 * n ^ 2) (permOp τ)`.
  The theorem rewrites `τ` as `(swapFactors τ).prod`, applies `permOp_list_prod`, then
  `IsPairProduct.mono` and `IsPairProduct.list_prod`. Each factor is closed by
  `obtain ⟨i, j, _, rfl⟩ := hswap σ hσ; exact isPairProduct_permOp_swap i j`.
  The next theorem, `IsPairProduct.conjugate_permOp`, gives
  `IsPairProduct d n (K + 4 * n ^ 2) (permOp τ * U * (permOp τ)ᴴ)` from `(hτ.mul hU).mul hτ.star`.
- `TNLean/MPS/Preparation/BlockUnitary.lean:112`, in
  `theorem isPairProduct_permOp_routePerm (n a : ℕ) : ∀ j, IsPairProduct d n (j * (2 * n)) (permOp (routePerm n a j))`.
  The step case is `(isPairProduct_permOp_routePerm n a j).mul ?_`, with
  `· exact isPairProduct_permOp_swap _ _` and `IsPairProduct.one` for the other branch.

Core restatement:
`theorem isPairProduct_permOp_swap {d N : ℕ} (i j : Fin N) : IsUnitaryGateCircuit (chain N) (2 * N) (relabelOp d (Equiv.swap i j))`.

Both statements stay expressible as written, for three reasons:
- `Config (Qudits (Fin n) d)` is definitionally `Fin n → Fin d`.
- `relabelOp` is `permOp` verbatim.
- `isUnitaryGateCircuit_chain_iff` says that `IsUnitaryGateCircuit (chain n) K U` is `IsPairProduct d n K U` verbatim, so `IsPairProduct` can be re-defined as that class.

The closure lemmas the consumers use map onto the core as follows:
- `one` is `done`.
- `mul` is `comp` with `gateCount_comp`; mind the order, since `kraus (c.comp c') = c'.kraus * c.kraus`.
- `mono` is immediate.
- `list_prod` folds `comp`.
- `star` needs the adjoint of an arbitrary unbranched unitary circuit. The core has this only for `seq` (`seqAdjoint`, `kraus_seqAdjoint`). This is a small extra gap: an unbranched unitary circuit may change basis types in the middle.

## Q2: branching substitution

Only unbranched substitution is needed. The evidence:
- The inductive `IsDimensionBoundedLocalChannelProtocol` (constructors `onsite`, `layer`, `onsite_comp`) has no branching.
- The same holds for `IsLocalChannelProtocol` and for the port classes (`IsPhysicalPortUnitary`, `IsPhysicalPortProtocol` with `mul`/`comp`).
- The compiler in `exists_physicalPortSimulation` works on lists. Its words are `List (FixedRegisterOperation q N)`, combined with `wordMap` and `wordDepth`. `dataChannelLift` is a monoid hom on `Module.End` (`lift_word_cons`), and `dataChannelLift_channelLayer` compiles each layer at the map level.
- `exists_physicalPort_pure_output` and `exists_physicalPort_approximate_output` go through `exists_physicalPortIO`, which uses the same predicate.
- The only branching protocol is `IsAdaptiveChannelProtocol` (its `instrument` constructor branches on onsite outcome tuples).
- `IsAdaptiveChannelProtocol` and `IsAdaptiveChannelConversion` are named only in `Measurement/AdaptiveConversion.lean` and `Measurement/AdaptiveRound.lean`. No port, regrouping or dimension-bound file imports or names them.
- The other `Measurement/*` files (`Protocol`, `Rounds`, `Channel`, `CoherentRounds`, `GHZ`, `Asymptotic`, `PreparedComposition`) never touch ports or regrouping.

So the core needs `compile : (each layer ↦ unbranched circuit) → unbranched circuit` with `depth ≤ K · depth`, plus map equality (`map_comp`).

A branching version would be strictly stronger. Each compiled layer would need an outcome-level correspondence: a map from its branches to `L.Index` with, fibrewise, `∑_{p ↦ i} K_p ρ K_pᴴ = K_i ρ K_iᴴ`. TNLean's map-level `dataChannelLift` does not supply that. Blocking (`exists_blocked`) could be done at the Kraus level, because merged gates keep product outcomes, but nothing requires it.
