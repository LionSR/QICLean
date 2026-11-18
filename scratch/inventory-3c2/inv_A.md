# Inventory, group A: TNLean `Circuit/Channel` core-channel modules

Source: `/home/user/lionsr/tnlean` at `origin/main`, read with `git show`; nothing in either repository was modified.
Verdicts: (a) a restriction of `Circuit`, whose definition disappears; (b) an instance of a core theorem, deleted; (c) a genuine theorem between restrictions, restated; (d) dead or duplicate, dropped.
(c\*) is an extra label. It marks a genuine theorem about one class of circuits, not a comparison of two classes. It still has to be restated once in the core, so its signature is given verbatim like a (c) item.

## Core gaps found (referenced below as G1–G11)

- **G1** Schrödinger–Heisenberg trace duality is missing. The core has no `trace (c.map ev ρ * A) = trace (ρ * c.dual ev A)`, and no `KrausFamily.trace_map_mul` in `Channel/KrausFamily`. It is trivial, but every factorization or `exists_dual` statement uses it.
- **G2** Multiplicativity of the Heisenberg picture on separated operators is missing. TNLean proves this as `BondChannelLayer.dual_mul`, `OnsiteChannel.dual_mul` and `channelCircuitDual_mul_of_disjoint_lightCone`. The core statement would be `Layer.dual ev (A*B) = Layer.dual ev A * Layer.dual ev B` when the one-step light cones of `A` and `B` are disjoint, and the same for an unbranched TP circuit with disjoint `Circuit.lightCone`s. `LayerDual.dual_place` is the computation it needs. With G2 comes the factorization theorem `tr(ρ AB) = tr(ρA) tr(ρB)` for a product input `ManyBody.prodOp σ`.
- **G3** The map of a layer with no cells on a product operator is missing. It should map `prodOp m` to `prodOp (fun s ↦ (k s).map (m s))` (TNLean `OnsiteChannel.map_rectKronecker`). It is needed so that product inputs stay product inputs through onsite layers, and for the trace of a product density.
- **G4** There is no ring geometry. The core needs a `Geometry (Fin N)` with bond cells `{k, k+1}` of cost 1. It also needs the fact that the iterated `Geometry.neighbourhood` is the ring ball `neighbourhood X r`, and that `IsSeparatedBy X Y (2T)` gives disjoint `T`-neighbourhoods. TNLean has all of this in `TNLean/Circuit/Geometry.lean`; `QICLean/Circuit/Geometry/Basic.lean` only mentions rings in prose. Check whether `ManyBody/Sites/Lattice` chain intervals can supply the ball.
- **G5** There is no blocking map `S → S'` (already noted in the brief). It would take a system to the system whose basis at `s'` is the configurations of the fibre, with `Config` and `prodOp` equivalences and a `LayerMap` that sends onsite families of the fine system to cost-0 cells of the fine system. It is needed by SiteBlocking (`blockSites`, `blockKronecker`, `blockSites_rectKronecker`, the support transport) and by WholeSiteChannels.
- **G6** There is no bound on intermediate basis sizes as a function on circuits (already noted). It is needed by DimensionBoundedConversion.
- **G7** There is no trace norm on `Matrix (Config X) (Config X) ℂ`. `QICLean.traceNorm` is defined only on `Matrix (Fin D) (Fin D) ℂ` (`Analysis/SchattenNorm.lean:66`). There is also no contractivity of `Circuit.map` for Hermitian inputs, which is Wolf Thm 8.16 via `isKrausCPTP_map`. Both are needed by ApproximateConversion.
- **G8** There is no `Circuit.map_step` or `map_append` in the Schrödinger picture: `(step L next).map ev ρ = ∑ i, (next i).map ev (K_i ρ K_iᴴ)`. Only `dual_step` exists. Feedforward statements need it.
- **G9** There is no lemma that moves onsite families into cost-0 single-site cells. It would read: a layer whose free-site families are `k s` equals `ofCells` on cost-0 singleton cells, so `map_ofCells` factors it into one placement per site. This is TNLean `OnsiteChannel.map_eq_prod_onSites_singleton`.
- **G10** There are no ports. The missing piece is a geometry on wires with one cost-0 cell per site (all of its wires) and cost-1 cells on port pairs (already noted: "nothing named port"). WholeSiteChannels and DataInitialization need it.
- **G11** Concrete local families are missing: attaching an ancilla `KrausFamily α (α × β)` and the partial trace `KrausFamily (α × β) α`. With arbitrary basis types these need no `finProdFinEquiv` encoding. They belong in `Channel/KrausFamily` or `Core/Outcome` if anything restated needs them.

---

## 1. `TNLean/Circuit/LocalCircuit.lean` (433 lines; read only as context)

The module defines `BondLayer d bond`: unitary gates `gate b`, global matrices supported on `bond b`, on pairwise disjoint bonds. A layer's operator is `op`, a circuit's is `circuitOp`. It also defines `IsBondCircuitOfDepth`, `IsBondPreparedInDepth` and the ring abbreviations `RingLayer`, `IsLocalCircuitOfDepth` and `IsPreparedInDepth`. The geometry `bond : β → Finset ι`, `bondNeighbourhood`, `lightCone bond X r`, `ringBond`, `neighbourhood X r` and `IsSeparatedBy` come from `TNLean/Circuit/Geometry.lean`. Channel/Layer generalizes `BondLayer` by replacing each unitary with a Kraus family of global matrices supported on the bond. The site basis is uniform (`ι → Fin d`) and branching is not possible.

## 2. `TNLean/Circuit/Channel/Layer.lean` (659 lines)

Lean consumers (import): `TNLean/Circuit/Channel.lean` (umbrella), `Channel/Conversion.lean`, `Channel/PhysicalPort.lean`.
Declarations used outside this module:
- `commute_rectangularKrausMap` in `PortSimulation`.
- `BondChannelLayer` in `EncodedChannelProtocol` and `NativePortLayer`.
- `gateMap` in `EncodedChannelLayer`, `NativePortLayer` and `RegroupedProtocol`.
- `channelCircuitMap` in `Conversion` and `RegroupedProtocol`.
- `BondLayer.toChannelLayer` and `channelCircuitMap_map_toChannelLayer` in `Measurement/AdaptiveRound`.
- `ChannelLayer` in many modules: Conversion, DimensionBounded, EncodedChannelLayer, EncodedChannelProtocol, NativePortLayer, RegroupedProtocol, Measurement/AdaptiveConversion.
- `IsChannelPreparedInDepth` in `Conversion`.

Every other declaration is used only here. The blueprint (`ch33_local_quantum_circuits_channels.tex`) cites `channelCircuitDual_mem_supportedOperators_lightCone`, `IsBondChannelPreparedInDepth.trace_mul_mul_eq` and `trace_mul_mul_eq_of_isChannelPreparedInDepth`.

| name | kind | content | verdict | reason |
|---|---|---|---|---|
| `trace_rectKronecker_eq_one` | private thm | trace of a product of densities is 1 | d | helper; core has `prodOp` (needs G3 trace variant) |
| `krausMap_apply` | private thm | unfolding | d | helper |
| `commute_rectangularKrausMap` | thm | Kraus maps with commuting operators commute | d | core fixes an order instead (`map_ofCells`); used by `PortSimulation`, so if that module's restatement needs it, it is a `KrausFamily` lemma |
| `trace_rectangularKrausMap_mul` | thm | `tr(Φ(ρ)A) = tr(ρ Φ†(A))` for Kraus maps | b (after G1) | becomes `KrausFamily.trace_map_mul` |
| `IsHeisenbergLocal` (+`.mono`, `.one`, `.mul`) | structure + 3 thms | a dual "acts on `S`" | d | superseded by `LayerDual.dual_place` and the blocks; no outside use |
| `isHeisenbergLocal_rectangularKrausMap` | thm | dual of a TP family supported on `S` acts on `S` | d | same; core `dual_place` |
| `trace_noncommProd_mul` | thm | duality of commuting products | d | helper for the noncommProd presentation |
| `BondChannelLayer` | structure | channels (Kraus families of global matrices supported on bonds) on disjoint bonds, TP by field | a | `Layer Γ KrausGate X X` with uniform system `fun _ ↦ Fin d`, no onsite change (identity at free sites), every gate TP (`Layer.Forall ev IsTP`), cells = bonds |
| `BondChannelLayer.gateMap`, `.gateDual` | defs | per-bond map and dual | a | `KrausGate` / `placeFamily` |
| `.gateMap_commute`, `.gateDual_commute` | thms | commutation of bond channels | d | not needed with ordered `map_ofCells` |
| `.map` | def | layer channel as `noncommProd` | a | `Layer.krausFamily.map` / `map_ofCells` |
| `.partialDual`, `.dual` | defs | dual of a sub-layer / layer | a | `Layer.dual` |
| `.gateMap_isKrausCPTP`, `.map_isKrausCPTP` | thms | CPTP | b | `Layer.isTP_krausFamily` + `KrausFamily.isKrausCPTP_map` |
| `.trace_map_mul` | thm | layer duality | b (after G1) | |
| `.partialDual_isHeisenbergLocal`, `.partialDual_eq_filter_mul`, private `partialDual_filter_*` | thms | splitting the dual near/far | d | core `LayerDual.kraus_eq_submatrix` / `dual_place` |
| `.partialDual_mem_supportedOperators`, `.dual_mem_supportedOperators` | thms | one-layer light cone | b | `Layer.dual_mem_supportedOperators_lightCone` |
| `.dual_mul` | thm | dual multiplicative when one-step neighbourhoods are disjoint | c\* (G2) | no core counterpart |
| `channelCircuitMap` | def | composite of layers, head first | a | unbranched `Circuit.seq` on the bond geometry; `Circuit.map` |
| `channelCircuitDual` | def | composite of duals | a | `Circuit.dual` |
| `channelCircuitMap_isKrausCPTP`, `trace_channelCircuitMap`, `posSemidef_channelCircuitMap` | thms | CPTP, trace, positivity | b | `Circuit.isKrausCPTP_map`, `trace_map` |
| `trace_channelCircuitMap_mul` | thm | circuit duality | b (after G1) | |
| `channelCircuitDual_mem_supportedOperators_lightCone` | thm | backward light cone of radius `Ls.length` | b | `Circuit.dual_mem_supportedOperators_lightCone` + `lightCone_subset_neighbourhood` |
| `channelCircuitDual_mul_of_disjoint_lightCone` | thm | dual multiplicative on disjoint light cones | c\* (G2) | |
| `conjMonoidHom` | def | `U ↦ (X ↦ UXU†)` monoid hom | d | helper |
| `BondLayer.toChannelLayer`, `.toChannelLayer_map` | def/thm | unitary layer as channel layer | b | core has a single type; unitary gates are `KrausFamily.single`, `Forall ev IsUnitary` |
| `channelCircuitMap_map_toChannelLayer` | thm | channel of unitary circuit = conjugation by `circuitOp` | b | `Circuit.dual_eq_of_subsingleton` / `kraus_seq` with `nonempty_unique_index` |
| `IsBondChannelPreparedInDepth` | def | `ρ = channelCircuitMap Ls (⊗σᵢ)`, `Ls.length = T` | a | a circuit of depth ≤ T applied to `prodOp σ` (ideally state it as "depth ≤ T", not `length = T`) |
| `IsBondChannelPreparedInDepth.trace_mul_mul_eq` | thm | factorization beyond disjoint light cones | c\* (G1, G2, G3) | |
| `ChannelLayer` | abbrev | ring specialization | a | ring geometry (G4) |
| `ChannelLayer.dual_mem_supportedOperators`, `ChannelLayer.dual_mul` | thms | ring versions | b / c\* | instance of the bond versions once G4 exists |
| `channelCircuitDual_mem_supportedOperators` (ring) | thm | ring light cone `neighbourhood X Ls.length` | b (after G4) | |
| `channelCircuitDual_mul` (ring) | thm | ring multiplicativity | c\* instance (G2, G4) | |
| `IsChannelPreparedInDepth` | abbrev | ring specialization | a | |
| `IsChannelPreparedInDepth.posSemidef` | thm | output is a density | b | `isKrausCPTP_map` + G3 trace of product |
| `trace_mul_mul_eq_of_isChannelPreparedInDepth` | thm | factorization at ring distance > 2T | c\* (ring instance of the bond one; G4) | |

Verbatim signatures of the (c\*) items and the definitions they mention:

```lean
structure BondChannelLayer (d : ℕ) (bond : β → Finset ι) where
  bonds : Finset β
  r : β → ℕ
  kraus : (b : β) → Fin (r b) → Matrix (ι → Fin d) (ι → Fin d) ℂ
  kraus_mem_supportedOperators :
      ∀ b ∈ bonds, ∀ j, kraus b j ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (bond b)
  sum_kraus : ∀ b ∈ bonds, ∑ j, (kraus b j)ᴴ * kraus b j = 1
  pairwiseDisjoint : (bonds : Set β).PairwiseDisjoint bond

theorem BondChannelLayer.dual_mul [Fintype β] (L : BondChannelLayer d bond) {X Y : Finset ι}
    (hXY : Disjoint (bondNeighbourhood bond X) (bondNeighbourhood bond Y))
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y) :
    L.dual (A * B) = L.dual A * L.dual B

noncomputable def channelCircuitDual :
    List (BondChannelLayer d bond) → Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ)

theorem channelCircuitDual_mul_of_disjoint_lightCone [Fintype β]
    (Ls : List (BondChannelLayer d bond))
    {X Y : Finset ι} (hXY : Disjoint (lightCone bond X Ls.length) (lightCone bond Y Ls.length))
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y) :
    channelCircuitDual Ls (A * B) = channelCircuitDual Ls A * channelCircuitDual Ls B

def IsBondChannelPreparedInDepth (T : ℕ) (ρ : Matrix (ι → Fin d) (ι → Fin d) ℂ) : Prop :=
  ∃ Ls : List (BondChannelLayer d bond), Ls.length = T ∧
    ∃ σ : ι → Matrix (Fin d) (Fin d) ℂ, (∀ i, (σ i).PosSemidef ∧ trace (σ i) = 1) ∧
      ρ = channelCircuitMap Ls (rectKronecker σ)

theorem IsBondChannelPreparedInDepth.trace_mul_mul_eq [Fintype β] {T : ℕ}
    {ρ : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hρ : IsBondChannelPreparedInDepth bond T ρ)
    {X Y : Finset ι} (hXY : Disjoint (lightCone bond X T) (lightCone bond Y T))
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y) :
    trace (ρ * (A * B)) = trace (ρ * A) * trace (ρ * B)

abbrev ChannelLayer (d N : ℕ) [NeZero N] := BondChannelLayer d (ringBond (N := N))
abbrev IsChannelPreparedInDepth (T : ℕ) (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : Prop :=
  IsBondChannelPreparedInDepth ringBond T ρ

theorem trace_mul_mul_eq_of_isChannelPreparedInDepth {T : ℕ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ} (hρ : IsChannelPreparedInDepth T ρ)
    {X Y : Finset (Fin N)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y) :
    trace (ρ * (A * B)) = trace (ρ * A) * trace (ρ * B)
```

Definitions mentioned, from `TNLean/Circuit/Geometry.lean`:
- `def bondNeighbourhood (X : Finset ι) : Finset ι := X ∪ (Finset.univ.filter fun b ↦ (bond b ∩ X).Nonempty).biUnion bond`. This is identical to `Geometry.neighbourhood`.
- `def lightCone (X : Finset ι) : ℕ → Finset ι | 0 => X | r + 1 => bondNeighbourhood bond (lightCone X r)`.
- `def ringBond (k : Fin N) : Finset (Fin N) := {k, k + 1}`.
- `def neighbourhood (X : Finset (Fin N)) (r : ℕ)`.
- `def IsSeparatedBy (X Y : Finset (Fin N)) (s : ℕ) : Prop := ∀ x ∈ X, ∀ y ∈ Y, ∀ m : ℤ, |m| ≤ s → y ≠ x + (m : Fin N)`.

Restatement needs: one core theorem, factorization for an unbranched circuit with TP local families applied to `prodOp σ`, with disjoint `Circuit.lightCone`s. It needs G1, G2 and G3. The ring corollary needs G4.

Counts: a 11, b 13, c\* 6, d 13 (a few instance rows count twice because they pair with gaps).

## 3. `TNLean/Circuit/Channel/Conversion.lean` (595 lines)

Lean consumers (import): umbrella, `ApproximateConversion`, `DimensionBoundedConversion`, `Feedforward`, `OnsiteRegisterEncoding`, `SiteBlocking`.

Names used outside:
- `OnsiteChannel` in about 15 modules: DataInitialization, DimensionBounded, EncodedChannel*, Feedforward, NativePortLayer, OnsiteChannelProduct, OnsiteRegisterEncoding, PhysicalPortCodes, PhysicalPortIO, PhysicalProtocolCompilation, RegroupedProtocol, WholeSiteChannels, Measurement/Adaptive*.
- `krausOp` and `sum_krausOp` in `Feedforward` and `AdaptiveRound`.
- `map_rectKronecker` in `OnsiteChannelProduct`, `OnsiteRegisterEncoding` and `RegroupedProtocol`.
- `id_map` in `EncodedChannelProtocol`, `PhysicalPortCodes` and `Adaptive*`.
- `IsLocalChannelProtocol` in Approx, Asymptotic, DimensionBounded, EncodedChannelProtocol, RegroupedProtocol, SiteBlocking and `Adaptive*`.
- `channelCircuitMap_comp` in `AdaptiveRound`.
- `exists_dual` and `exists_isKrausCPTP` in `SiteBlocking`.
- `IsLocalChannelConversion` in Approx, RegroupedProtocol, SiteBlocking, `Measurement/AdaptiveConversion` and `Measurement/Protocol`.
- `trace_mul_mul_eq_of_isLocalChannelConversion` in `SiteBlocking` and `Measurement/Protocol`.

`ancillaKraus*`, `attachZero`, `discardKraus`, `attach_siteMap_apply`, `discard_siteMap_*`, `siteDual*`, `dual_*Kronecker` and `map_finKronecker` have no outside use. The bare names `attach` and `discard` collide with other APIs, so their grep hits are not real uses.
The blueprint `ch33_local_quantum_circuits_channels.tex` cites `IsLocalChannelConversion` and `trace_mul_mul_eq_of_isLocalChannelConversion`.

| name | kind | content | verdict | reason |
|---|---|---|---|---|
| `rectangularKrausMap_rectKronecker_rectKronecker` | thm | product Kraus map on product operator | b (after G3) | |
| `OnsiteChannel d e ι` | structure | per-site Kraus family `Fin d → Fin e`, TP field | a | a `Layer` with no cells (every site free), onsite families `KrausFamily (Fin d) (Fin e)`, uniform system; TP via `Forall IsTP` |
| `.siteMap`, `.siteDual`, `.krausOp`, `.map`, `.dual` | defs | its maps / Kraus operators | a | `KrausFamily.map`, `Layer.kraus`, `Layer.dual` |
| `.sum_krausOp`, `.map_isKrausCPTP` | thms | TP / CPTP | b | `Layer.isTP_krausFamily` |
| `.map_rectKronecker`, `.dual_rectKronecker`, `.map_finKronecker`, `.dual_finKronecker` | thms | product → product | b (after G3) | |
| `.siteDual_one` | thm | dual unital | b | `KrausFamily.IsTP` def |
| `.trace_map_mul` | thm | duality | b (after G1) | |
| `.dual_mem_supportedOperators` | thm | onsite dual preserves support `X` | b | `Layer.dual_mem_supportedOperators_lightCone` with no cells (lightCone = R) |
| `.dual_mul` | thm | onsite dual multiplicative on disjoint supports | c\* instance of G2 | |
| `OnsiteChannel.id`, `.id_map` | def/thm | identity | b | `Circuit.done` / identity families, `map_done` |
| `ancillaKraus`, `ancillaKraus_apply`, `conjTranspose_ancillaKraus_mul` | def/thms | `x ↦ x ⊗ v` with `finProdFinEquiv` | d | encoding is unnecessary with arbitrary basis types; G11 if needed |
| `attach`, `attach_siteMap_apply`, `attachZero` | defs/thm | attach ancilla density at every site | d (G11) | concrete family, not circuit theory; no outside Lean use |
| `discardKraus`, `discard`, `discard_siteMap_apply`, `discard_siteMap_attach_siteMap` | defs/thms | partial trace over the ancilla | d (G11) | same |
| `IsLocalChannelProtocol` | inductive (on maps) | `Φ_T ∘ L_T ∘ ⋯ ∘ L_1 ∘ Φ_0` | a | unbranched circuit on the ring geometry (G4): sites `Fin N`, uniform system `fun _ ↦ Fin d_t` changing only through no-cell layers; cell layers preserve the system; all families TP; depth ≤ T |
| `.isKrausCPTP` | thm | CPTP | b | `isKrausCPTP_map` |
| `.comp` | thm | depths add | b | `comp` + `depth_comp` |
| `.channelCircuitMap_comp` | thm | append a channel circuit | b | `depth_comp` + `total_seq_le` |
| `.exists_dual` | thm | dual with duality, ring light cone, multiplicativity | b + c\* | duality G1, light cone (b) with G4, multiplicativity G2 |
| `IsLocalChannelConversion` | def | `∃ T' ≤ T, ∃ Ψ, protocol ∧ Ψ ρ = σ` | a | `∃ c` in the class, `c.depth ≤ T`, `c.map ev ρ = σ` |
| `.refl`, `.mono`, `.trans` | thms | preorder with additive depth | b | `done`, `comp`, `depth_comp` |
| `.exists_isKrausCPTP`, `.density` | thms | channel; density to density | b | `isKrausCPTP_map`, `trace_map` |
| `isLocalChannelConversion_circuit` | thm | attach, circuit, discard is depth T | b | `comp`, `depth_comp` |
| `IsChannelPreparedInDepth.exists_isLocalChannelConversion` | thm | preparation is a conversion from a product | d | duplicate after the definitions merge |
| `trace_mul_mul_eq_of_isLocalChannelConversion` | thm | factorization at ring distance > 2T | c\* (G1–G4) | the general form of the Layer.lean factorization; with onsite dimension changes it is the one to restate |

Verbatim signatures of the (c\*) items and the definitions they mention:

```lean
structure OnsiteChannel (d e : ℕ) (ι : Type*) where
  r : ι → ℕ
  kraus : (i : ι) → Fin (r i) → Matrix (Fin e) (Fin d) ℂ
  sum_kraus : ∀ i, ∑ j, (kraus i j)ᴴ * kraus i j = 1

theorem OnsiteChannel.dual_mul (Φ : OnsiteChannel d e ι) {X Y : Finset ι} (hXY : Disjoint X Y)
    {A B : Matrix (ι → Fin e) (ι → Fin e) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) Y) :
        Φ.dual (A * B) = Φ.dual A * Φ.dual B

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

theorem IsLocalChannelProtocol.exists_dual {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ] Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsLocalChannelProtocol T Ψ) :
    ∃ Ψ' : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ] Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ,
      (∀ ρ A, trace (Ψ ρ * A) = trace (ρ * Ψ' A)) ∧
      (∀ X : Finset (Fin N), ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
        Ψ' A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (neighbourhood X T)) ∧
      (∀ X Y : Finset (Fin N), Disjoint (neighbourhood X T) (neighbourhood Y T) →
        ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
            ∀ B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) Y,
          Ψ' (A * B) = Ψ' A * Ψ' B)

def IsLocalChannelConversion {d' : ℕ} (T : ℕ) (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (σ : Matrix (Fin N → Fin d') (Fin N → Fin d') ℂ) : Prop :=
  ∃ T' ≤ T, ∃ Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ] Matrix (Fin N → Fin d')
    (Fin N → Fin d') ℂ,
    IsLocalChannelProtocol T' Ψ ∧ Ψ ρ = σ

theorem trace_mul_mul_eq_of_isLocalChannelConversion {d' T : ℕ}
    {σ₀ : Fin N → Matrix (Fin d) (Fin d) ℂ} (hσ₀ : ∀ i, trace (σ₀ i) = 1)
    {σ : Matrix (Fin N → Fin d') (Fin N → Fin d') ℂ}
    (h : IsLocalChannelConversion T (finKronecker σ₀) σ)
    {X Y : Finset (Fin N)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin N → Fin d') (Fin N → Fin d') ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d') X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d') Y) :
    trace (σ * (A * B)) = trace (σ * A) * trace (σ * B)
```

The section variables are `{N : ℕ} [NeZero N]`.

Notes:
- The factorization only needs `trace (σ₀ i) = 1`, not positivity. In the core, an unbranched TP circuit with any per-site system (not uniform `Fin d`) gives the general form. The ring form follows from G4.
- The paper-gap scope note `psc21_local_channel_phase_scope.tex` (enlarged sites, unit-cost layers, no feedforward) goes away as a restriction. In the core, enlarged sites are allowed and branching exists. The gap to the source becomes a statement about the class (the G6 bound, or ports G10).

Counts: a 6, b 16, c\* 3, d 9.

## 4. `TNLean/Circuit/Channel/Feedforward.lean` (106 lines)

Lean consumers (import): umbrella, `Measurement/AdaptiveConversion.lean`, `Measurement/Channel.lean`. `feedforwardMap` and all three theorems are used in `Measurement/AdaptiveConversion`, and `feedforwardMap` also in `Measurement/AdaptiveRound`. The blueprint `ch33_local_quantum_circuits_adaptive.tex` cites `feedforwardMap_isKrausCPTP`.

| name | kind | content | verdict | reason |
|---|---|---|---|---|
| `OnsiteChannel.feedforwardMap` | def | `∑_J Ψ J ∘ (K_J · K_Jᴴ)`, the onsite instrument with an outcome-dependent continuation | a | `Circuit.step L next` with `L` a no-cell layer (index = outcome tuple per free site) and `next : L.Index → Circuit` (branching); restriction: the continuation is a circuit, whereas TNLean allows an arbitrary CPTP `Ψ J` |
| `feedforwardMap_isKrausCPTP` | thm | CPTP when each continuation is CPTP | b | `Circuit.isKrausCPTP_map` (measurement with feedback summed) |
| `feedforwardMap_const` | thm | constant continuation = composition | b | `comp` = `append` with a constant continuation, `map_comp` |
| `comp_feedforwardMap` | thm | post-composition enters every branch | b | `append` / `comp` associativity, `kraus_append` (Schrödinger form needs G8) |

The (b) verdicts hold only if the Measurement modules (another group) restate their continuations as circuits. If an arbitrary-channel continuation is really needed, the CPTP fact is a plain `KrausFamily` lemma, not circuit theory. G8 (`map_step`) would make all three one-liners.

Counts: a 1, b 3, c 0, d 0.

## 5. `TNLean/Circuit/Channel/WholeSiteChannels.lean` (112 lines)

Lean consumers (import): umbrella, `Channel/PhysicalPortCodes.lean`, which uses `wholeSite_onsiteChannel`. Nothing else is used outside. The blueprint `ch33_local_quantum_circuits_physical_ports.tex` cites `wholeSite_onsiteChannel`. The module imports `NativePortLayer`; the port and register vocabulary is in other groups' modules.

| name | kind | content | verdict | reason |
|---|---|---|---|---|
| `PortRegisters.blockDigits` | def | embedding of the wires of selected sites | d | coordinate helper; absorbed by G5/G10 |
| `blockDigits_apply` | thm | simp | d | |
| private `allData_comp_blockDigits` | thm | helper | d | |
| `nativeMatrixEquiv_embedOp` | thm | digit grouping commutes with placement | b (after G5) | naturality of the blocking map with placement (`mapSites`-style) |
| `nativeChannelReindex_register_kraus` | thm | reindexed lifted Kraus channel = Kraus channel on wire blocks | b (after G5) | `kraus_mapLayers` for the blocking map |
| `wholeSite_local` | thm | a CPTP map on one complete site block is a depth-0 physical-port protocol | c (G5, G10) | regrouping: a gate on a blocked site = a gate on a cost-0 site cell of the wire geometry |
| `wholeSite_onsiteChannel` | thm | an onsite channel on blocked sites (`d^(1+k+k)`) is a depth-0 physical-port protocol on wires | c (G5, G9, G10) | regrouping plus onsite-to-cell; in the core it is `depth_mapLayers ≤` for a layer of cost-0 cells |

Verbatim signatures of the (c) items and the definitions they mention:

```lean
theorem wholeSite_local (hd : 0 < d) (e : Fin s ↪ Fin N)
    (Φ : Module.End ℂ (Matrix (Fin s → Fin (d ^ (1 + k + k)))
      (Fin s → Fin (d ^ (1 + k + k))) ℂ))
    (hΦ : IsKrausCPTP Φ) (i : Fin N) (he : ∀ a, e a = i) :
    IsPhysicalPortProtocol (layout N k) 0
      (nativeChannelReindex N (1 + k + k) d (registerChannelLift e Φ))

theorem wholeSite_onsiteChannel (hd : 0 < d)
    (Φ : OnsiteChannel (d ^ (1 + k + k)) (d ^ (1 + k + k)) (Fin N)) :
    IsPhysicalPortProtocol (layout N k) 0
      (nativeChannelReindex N (1 + k + k) d Φ.map)
```

The section variables are `{N s w d k r : ℕ}` and `[NeZero N]`; the namespace is `QuantumCircuit.PortRegisters`.

Mentioned definitions, from other modules:

```lean
-- PhysicalPort.lean
structure PhysicalPortLayout (N W : ℕ) where
  site : Fin W → Fin N
  port : Fin N ↪ Fin W
  site_port : ∀ i, site (port i) = i
inductive IsPhysicalPortUnitary (P : PhysicalPortLayout N W) : ℕ →
    Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ → Prop
  | onsite (i : Fin N) {U} (hU : U ∈ unitary _) (hs : U ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
          (Finset.univ.filter fun p ↦ P.site p = i)) : IsPhysicalPortUnitary P 0 U
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
      (hU : IsPhysicalPortUnitary P T U) : IsPhysicalPortProtocol P T (singleKrausMap U)
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
-- PortRegisters.lean
def layout (N k : ℕ) : PhysicalPortLayout N (N * (1 + k + k))   -- site w := (finProdFinEquiv.symm w).1, port i := (i, 0)
-- NativeRegisterWires.lean
def groupedConfigurations (N k d : ℕ) : (Fin (N * k) → Fin d) ≃ (Fin N → Fin (d ^ k))
def nativeMatrixEquiv (N k d : ℕ) :
    Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (N * k) → Fin d) (Fin (N * k) → Fin d) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (groupedConfigurations N k d).symm
def nativeChannelReindex (N k d : ℕ) :
    Module.End ℂ (Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) →*
      Module.End ℂ (Matrix (Fin (N * k) → Fin d) (Fin (N * k) → Fin d) ℂ)
-- RegisterChannelLift.lean
def registerChannelLift (e : Fin m ↪ Fin W)
    (Φ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)) :
    Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)
```

How `IsPhysicalPortProtocol` maps onto the core:
- It is a restriction of the "ports" kind: sites are the wires `Fin W`, with a cost-0 cell per spatial site (all of its wires) and cost-1 cells on port pairs `{port k, port (k+1)}`.
- `onsitePermutation` is a cost-0 site-cell gate.
- Every family is TP, and the circuit is unbranched.
- Its `layer` constructor is a cost-1 ring layer moved along `mapSites` (`siteSplit P.port`).

With that in place, `wholeSite_*` says that mapping a no-cell (onsite) layer on the blocked system along the blocking map (G5) gives a layer of gates on cost-0 site cells, so its depth is 0. This is the "regrouping" (c) item. Once G5 exposes `depth_mapLayers_le`, it can reduce to a cost lemma of the blocking `LayerMap`.

Counts: a 0, b 2, c 2, d 3.

## 6. `TNLean/Circuit/Channel/OnsiteChannelProduct.lean` (144 lines)

Lean consumers (import): umbrella, `Channel/NativePortLayer.lean`.
Names used outside:
- `singletonSite` in `NativePortLayer` and `WholeSiteChannels`.
- `map_eq_prod_onSites_singleton` in `NativePortLayer` and `WholeSiteChannels`.
- `oneSite` in `NativePortLayer` and `WholeSiteChannels`.
- `onSites_singleton_map_eq_lift` in `NativePortLayer` and `WholeSiteChannels`.

The bare names `map_congr` and `oneSite` collide with unrelated declarations elsewhere.

| name | kind | content | verdict | reason |
|---|---|---|---|---|
| `singletonSite`, `singletonSite_apply`, `range_singletonSite` | def/thms | `Fin 1 ↪ Fin N` at `i` | d | core places on `Finset` regions; `Layer.single` on `{i}` |
| `registerMatrixSplit_rectKronecker` | thm | split of a product matrix | d | helper; core `kraus_eq_submatrix` / `place` |
| `OnsiteChannel.map_congr` | thm | equal site maps give equal maps | d | trivial in the core (families are data) |
| `OnsiteChannel.onSites`, `onSites_siteMap` | def/thm | apply only at sites in `s` | a | layer with the given families on `s`, identity elsewhere |
| `onSites_univ_map`, `onSites_empty_map`, `onSites_insert_map`, `prod_onSites_singleton` | thms | algebra of `onSites` | d | helpers for the next row |
| `map_eq_prod_onSites_singleton` | thm | onsite channel = ordered product of single-site factors | b (after G9) | `map_ofCells` on cost-0 singleton cells |
| `oneSite`, `oneSite_siteMap` | def/thm | the site channel as a `Fin 1` register | d | core uses `KrausFamily` on `RegionConfig X {i}` / `siteEquiv` |
| `onSites_singleton_map_eq_lift` | thm | one-site factor = `registerChannelLift (singletonSite i)` | b | `Layer.kraus_single` / `placeFamily` |

Counts: a 1, b 2, c 0, d 6.

## 7. `TNLean/Circuit/Channel/SiteBlocking.lean` (413 lines)

Lean consumers (import): umbrella, `Channel/RegroupedProtocol.lean`.
`RegroupedProtocol` uses `siteBlock`, `blockSites`, `blockSites_isKrausCPTP`, `blockSites_symm_isKrausCPTP`, `blockSites_rectKronecker`, `blockSites_mem_supportedOperators` and `IsBlockedLocalChannelConversion`. The other declarations have no outside use. The blueprint `ch33_local_quantum_circuits_channels.tex` cites `IsBlockedLocalChannelConversion` and `trace_mul_mul_eq_of_isBlockedLocalChannelConversion`.

| name | kind | content | verdict | reason |
|---|---|---|---|---|
| `siteBlock`, `siteBlock_finProdFinEquiv` | def/thm | the block of a site of `Fin (M*k)` | a | the fibre map of the blocking `S → S'` (G5) |
| `blockSites` | def | `M_d^{⊗Mk} ≃ₐ M_{d^k}^{⊗M}` relabelling | a (G5) | the `Config` equivalence of the blocking map |
| `blockSites_apply`, `groupedConfigurations_symm_apply_finProdFinEquiv`, `toLinearMap_blockSites` | thms | unfolding | d | |
| `blockSites_isKrausCPTP`, `blockSites_symm_isKrausCPTP`, `trace_blockSites` | thms | relabelling is a channel | b (G5) | a reindexing channel; generic |
| `blockKronecker`, `trace_blockKronecker`, `blockKronecker_one` | def/thms | `⊗ₜ nₜ` on one block | a (G5) | `prodOp` on the fibre |
| `blockSites_rectKronecker` | thm | blocking maps a product to a product of blocks | b (G5) | `prodOp` under the blocking equivalence; needed for factorization after blocking |
| `blockSites_mem_supportedOperators`, `blockSites_symm_mem_supportedOperators` | thms | supports transported by blocking/unblocking | b (G5) | support transport of the blocking map, the analogue of `lightCone_mapSites` |
| `finProdFinEquiv_add_intCast` | thm | moving a block by `m` moves its sites by `k*m` | d | geometry helper for the next row |
| `preimage_siteBlock_neighbourhood_subset` | thm | preimage of the block-`r`-ball ⊆ the `k*r`-ball | c (G4, G5) | a geometry fact relating the blocked ring and the fine ring; needed for the radius-`kT` light cone |
| `IsLocalChannelProtocol.exists_dual_comp_blockSites` | thm | dual of protocol ∘ blocking: duality, light cone on fine sites of the `T`-ball, multiplicativity | c (G1, G2, G5) | |
| `IsBlockedLocalChannelConversion` | def | `IsLocalChannelConversion T (blockSites M k d ρ) σ` | a | a circuit on the blocked ring applied after blocking; with G5 it is a circuit on the blocked system with the blocking as an input relabelling |
| `.blockSites`, `.mono`, `.trans`, `.exists_isKrausCPTP`, `.density` | thms | basic closure | b | `comp`, `depth_comp`, `isKrausCPTP_map` |
| `.exists_dual` | thm | light cone of radius `k*T` in the fine chain | c (G1, G2, G4, G5) | |
| `trace_mul_mul_eq_of_isBlockedLocalChannelConversion` | thm | factorization at block distance > 2T for blocked product inputs | c (G1–G5) | |

Verbatim signatures of the (c) items and the definitions they mention:

```lean
def siteBlock (i : Fin (M * k)) : Fin M := (finProdFinEquiv.symm i).1

def blockSites (M k d : ℕ) :
    Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ ≃ₐ[ℂ]
      Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ :=
  (nativeMatrixEquiv M k d).symm

theorem preimage_siteBlock_neighbourhood_subset [NeZero M] [NeZero k] (X : Finset (Fin M))
    (r : ℕ) :
    (Finset.univ.filter fun p ↦ siteBlock (k := k) p ∈ neighbourhood X r) ⊆
      neighbourhood (Finset.univ.filter fun p ↦ siteBlock (k := k) p ∈ X) (k * r)

theorem IsLocalChannelProtocol.exists_dual_comp_blockSites [NeZero M] [NeZero d] {T : ℕ}
    {Ψ : Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ →ₗ[ℂ]
      Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsLocalChannelProtocol T Ψ) :
    ∃ Ψ' : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ,
      (∀ ρ A, trace (Ψ (blockSites M k d ρ) * A) = trace (ρ * Ψ' A)) ∧
      (∀ X : Finset (Fin M), ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
        Ψ' A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
          (Finset.univ.filter fun p ↦ siteBlock p ∈ neighbourhood X T)) ∧
      (∀ X Y : Finset (Fin M), Disjoint (neighbourhood X T) (neighbourhood Y T) →
        ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
            ∀ B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) Y,
          Ψ' (A * B) = Ψ' A * Ψ' B)

def IsBlockedLocalChannelConversion [NeZero M] (k : ℕ) [NeZero k] (T : ℕ)
    (ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ)
    (σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ) : Prop :=
  IsLocalChannelConversion T (blockSites M k d ρ) σ

theorem IsBlockedLocalChannelConversion.exists_dual [NeZero d] {T : ℕ}
    {ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedLocalChannelConversion k T ρ σ) :
    ∃ Ψ' : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ,
      (∀ A, trace (σ * A) = trace (ρ * Ψ' A)) ∧
      (∀ X : Finset (Fin M), ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
        Ψ' A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
          (neighbourhood (Finset.univ.filter fun p ↦ siteBlock (k := k) p ∈ X) (k * T))) ∧
      (∀ X Y : Finset (Fin M), Disjoint (neighbourhood X T) (neighbourhood Y T) →
        ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X,
            ∀ B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) Y,
          Ψ' (A * B) = Ψ' A * Ψ' B)
-- (namespace variables: [NeZero M] [NeZero k] {e' : ℕ})

theorem trace_mul_mul_eq_of_isBlockedLocalChannelConversion [NeZero M] [NeZero k] {T : ℕ}
    {σ₀ : Fin (M * k) → Matrix (Fin d) (Fin d) ℂ} (hσ₀ : ∀ i, trace (σ₀ i) = 1)
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedLocalChannelConversion k T (finKronecker σ₀) σ)
    {X Y : Finset (Fin M)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) Y) :
    trace (σ * (A * B)) = trace (σ * A) * trace (σ * B)
```

`groupedConfigurations` is listed under §5. `IsLocalChannelProtocol`, `IsLocalChannelConversion` and `IsSeparatedBy` are listed under §2–3.

Notes:
- With G5, the light cone of the blocked circuit mapped down to the fine sites comes from `lightCone_mapLayers` and `lightCone_subset_neighbourhood` in the geometry of "pairs of adjacent blocks". That reduces `exists_dual` to the geometry comparison `preimage_siteBlock_neighbourhood_subset` plus G1 and G2. The factorization theorem then reduces to the unblocked factorization (G2) plus `blockSites_rectKronecker` (a blocked product input is a product input).
- The source compilation of a blocked gate into fewer than 2q² nearest-neighbour gates (`main.tex` line 289) is not formalized. That compilation would be a genuine (c) item; it is a "Scope restriction" and still open.

Counts: a 4, b 4, c 4, d 3.

## 8. `TNLean/Circuit/Channel/DataInitialization.lean` (153 lines)

Lean consumers (import): umbrella, `Channel/PhysicalPortIO.lean`, which uses `zeroDataReferencePrep`, `wordInitialization_data_eq_physicalEncoding` and `tensorMapId_comp_zeroDataReferencePrep`. The blueprint `ch33_local_quantum_circuits_physical_ports.tex` cites `wordInitialization_data_eq_physicalEncoding`.

| name | kind | content | verdict | reason |
|---|---|---|---|---|
| private `registerEncoding_map_single`, `reindex_single_eq`, `data_word_split` | thms | matrix-unit helpers | d | |
| `PortRegisters.bareDataCode`, `nativeWordCode_bareDataCode` | def/thm | the local data code without port/scratch digits | d | coordinates |
| `zeroDataReferencePrep` | def | `X ↦ X ⊗ |0⟩⟨0|` on the port/scratch reference | a | a no-cell layer of ancilla-preparing onsite isometries (basis change `Fin d → Fin d × ref`); G11 |
| `wordInitialization_data_eq_physicalEncoding` | thm | product data initializer = physical encoding ∘ zero-reference prep | c (encoding; G5, G10, G11) | relates two presentations of the same onsite isometry; in the core, likely a definitional equality of onsite families plus the blocking map, so it may collapse to (b) |
| `tensorMapId_comp_zeroDataReferencePrep` | thm | `(Ψ ⊗ id) ∘ prep = prep ∘ Ψ` | b | naturality of an ancilla on idle sites; `kraus_mapSites` (idle sites `R`) / `extendSystem` |

Verbatim signatures:

```lean
def zeroDataReferencePrep :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix ((Fin N → Fin d) × DataReference N k d)
        ((Fin N → Fin d) × DataReference N k d) ℂ :=
  (Matrix.kroneckerBilinear (R := ℂ)).flip
    (single (0 : DataReference N k d) 0 (1 : ℂ))

theorem wordInitialization_data_eq_physicalEncoding (c : Fin d ↪ Fin (d ^ k)) :
    wordInitialization (N := N) (dataWordCode c) =
      physicalEncoding (OnsiteChannel.encodeRegisters (fun _ : Fin N => c)).map ∘ₗ
        zeroDataReferencePrep
-- variables {N k d : ℕ} [NeZero d], namespace QuantumCircuit.PortRegisters
```

Mentioned definitions, from other modules:

```lean
abbrev DataReference (N k d : ℕ) :=
  {w : Fin (N * (1 + k + k)) // w ∉ Set.range (allData N k)} → Fin d
def physicalEncoding
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) :
    Matrix (α × DataReference N k d) (α × DataReference N k d) ℂ →ₗ[ℂ]
      Matrix (Fin (N * (1 + k + k)) → Fin d) (Fin (N * (1 + k + k)) → Fin d) ℂ :=
  (registerMatrixSplit (allData N k)).symm.toLinearMap ∘ₗ
    tensorMapIdLM ((nativeMatrixEquiv N k d).toLinearMap ∘ₗ E)
def wordInitialization (c : Fin d ↪ (Fin w → Fin d)) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (N * w) → Fin d) (Fin (N * w) → Fin d) ℂ :=
  singleKrausMap (registerEncoding (wordCodeConfiguration c))
def dataWordCode (c : Fin d ↪ Fin (d ^ k)) : Fin d ↪ (Fin (1 + k + k) → Fin d)
  -- x ↦ Fin.append (Fin.append 0 (digits (c x))) 0
noncomputable def OnsiteChannel.encodeRegisters (e : ι → (Fin m ↪ Fin q)) : OnsiteChannel m q ι
  -- r _ := 1, kraus i _ := registerEncoding (e i)
def registerEncoding (e : α ↪ β) : Matrix β α ℂ := (1 : Matrix β β ℂ).submatrix id e
def wordCodeConfiguration (c : Fin d ↪ (Fin w → Fin d)) :
    (Fin N → Fin d) ↪ (Fin (N * w) → Fin d)
def allData (N k : ℕ) : Fin (N * k) ↪ Fin (N * (1 + k + k))
```

In the core, the per-site isometry `Fin d → (port, data, scratch)` is one onsite `KrausFamily.single`, and a basis change is allowed. Preparing the zero reference and encoding are then one layer. The theorem survives only as a coordinate identity between the wire picture (G10) and the blocked picture (G5). Whether it is still needed depends on how `PhysicalPortIO` (another group) is restated.

Counts: a 1, b 1, c 1, d 5.

## 9. `TNLean/Circuit/Channel/ApproximateConversion.lean` (173 lines)

Lean consumers (import): umbrella, `AsymptoticConversion`, `BoundedPortApproximateOutput`. The latter uses `chainTraceNorm`. `IsApproxLocalChannelConversion` is used by `AsymptoticConversion`. The blueprint `ch33_local_quantum_circuits_approximate.tex` cites `IsApproxLocalChannelConversion`.

| name | kind | content | verdict | reason |
|---|---|---|---|---|
| `chainTraceNorm` | def | trace norm after `Fintype.equivFin` | d (G7) | replaced by a trace norm on any finite index type |
| `chainTraceNorm_nonneg`, `_zero`, `_eq_zero_iff`, `_add_le` | thms | norm axioms | d (G7) | general facts about that norm |
| `IsLocalChannelProtocol.chainTraceNorm_map_le` | thm | trace-norm contractivity on Hermitian inputs (Wolf 8.16) | b (G7) | `isKrausCPTP_map` + `QICLean.Analysis.TraceNormContractivity` |
| `IsApproxLocalChannelConversion` | def | `∃ S ≤ T, ∃ Ψ protocol, ‖Ψ ρ - σ‖₁ ≤ ε` | a | `∃ c` in the class, `c.depth ≤ T ∧ ‖c.map ev ρ - σ‖₁ ≤ ε` |
| `IsLocalChannelConversion.approx`, `.refl`, `.mono` | thms | exact ⇒ approximate; monotone | b | |
| `.trans` | thm | depths and errors add (Hermitian inputs) | c\* (G7) | genuine composition theorem for approximate conversion by circuits; restate once for any class closed under `comp` |
| `isApproxLocalChannelConversion_zero_iff` | thm | zero error ⇔ exact | b | from `_eq_zero_iff` |

Verbatim signatures:

```lean
def chainTraceNorm (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : ℝ :=
  traceNorm (equivReindexMap (Fintype.equivFin (Fin N → Fin d)) A)

def IsApproxLocalChannelConversion (T : ℕ) (ε : ℝ)
    (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) : Prop :=
  ∃ S ≤ T, ∃ Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ,
    IsLocalChannelProtocol S Ψ ∧ chainTraceNorm (Ψ ρ - σ) ≤ ε

theorem IsApproxLocalChannelConversion.trans {T₁ T₂ : ℕ} {ε₁ ε₂ : ℝ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {τ : Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (h₁ : IsApproxLocalChannelConversion T₁ ε₁ ρ σ)
    (h₂ : IsApproxLocalChannelConversion T₂ ε₂ σ τ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    IsApproxLocalChannelConversion (T₁ + T₂) (ε₁ + ε₂) ρ τ
-- variables {d e f N : ℕ} [NeZero N]
```

Counts: a 1, b 5, c\* 1, d 5.

## 10. `TNLean/Circuit/Channel/AsymptoticConversion.lean` (154 lines)

Lean consumers (import): only the umbrella `TNLean/Circuit/Channel.lean`. No Lean declaration uses either definition. The blueprint `ch33_local_quantum_circuits_approximate.tex` and the paper-gap note `psc21_local_channel_phase_scope.tex` cite both.

| name | kind | content | verdict | reason |
|---|---|---|---|---|
| `IsAsymptoticLocalChannelConversion` | def | `ε N → 0`, eventually depth ≤ `C (1 + log (N+1))^k` | a | a family relation over circuits of the class, by depth and approximate conversion |
| `.refl` | thm | | b | |
| `.trans` | thm | composes for eventually Hermitian families | c\* (via §9 `.trans`) | generic once approximate `.trans` is restated; polylog arithmetic only |
| `IsLocalChannelPhaseEquivalent`, `.refl`, `.symm`, `.trans`, `.equivalence` | def/thms | mutual conversion is an equivalence | a / b | definition plus formal consequences of `.trans` |

There are no Lean consumers. The definitions are kept only because of the blueprint chapter on local-channel phases. If that chapter is restated, the definition is one line over the core relation and `.trans` follows from §9. Otherwise the module is (d) no use.

Verbatim signatures:

```lean
def IsAsymptoticLocalChannelConversion
    (ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (σ : (N : ℕ) → Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) : Prop :=
  ∃ (k : ℕ) (C : ℝ) (ε : ℕ → ℝ), 0 ≤ C ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ᶠ (N : ℕ) in atTop, ∀ [NeZero N], ∃ T : ℕ,
      (T : ℝ) ≤ C * (1 + Real.log ((N : ℝ) + 1)) ^ k ∧
      IsApproxLocalChannelConversion T (ε N) (ρ N) (σ N)

theorem IsAsymptoticLocalChannelConversion.trans
    {ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : (N : ℕ) → Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {τ : (N : ℕ) → Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (h₁ : IsAsymptoticLocalChannelConversion ρ σ)
    (h₂ : IsAsymptoticLocalChannelConversion σ τ)
    (hρ : ∀ᶠ N in atTop, (ρ N).IsHermitian)
    (hσ : ∀ᶠ N in atTop, (σ N).IsHermitian) :
    IsAsymptoticLocalChannelConversion ρ τ

def IsLocalChannelPhaseEquivalent
    (ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (σ : (N : ℕ) → Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) : Prop :=
  IsAsymptoticLocalChannelConversion ρ σ ∧ IsAsymptoticLocalChannelConversion σ ρ

theorem IsLocalChannelPhaseEquivalent.equivalence : Equivalence (fun
    (ρ σ : {ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ //
      ∀ᶠ N in atTop, (ρ N).IsHermitian}) ↦ IsLocalChannelPhaseEquivalent ρ.1 σ.1)
```

Counts: a 2, b 4, c\* 1, d 0. The whole module becomes (d) if the blueprint chapter is not carried over.

## 11. `TNLean/Circuit/Channel/DimensionBoundedConversion.lean` (134 lines)

Lean consumers (import): umbrella, `EncodedChannelProtocol`, `RegroupedProtocol`.
- `IsDimensionBoundedLocalChannelProtocol` is used in `BoundedPortApproximateOutput`, `BoundedPortPureOutput`, `EncodedChannelProtocol`, `PhysicalPortIO`, `PhysicalPortUnitaryCompilation`, `PhysicalProtocolCompilation` and `RegroupedProtocol`.
- `toIsLocalChannelProtocol` and `exists_dimension_bound` are used in `RegroupedProtocol`.
- `dimension_bounds` is used in `EncodedChannelProtocol`, `PhysicalPortIO` and `PhysicalProtocolCompilation`.

The blueprint (`ch33_local_quantum_circuits_channels.tex`, `..._physical_ports.tex`) cites `IsDimensionBoundedLocalChannelProtocol` and `exists_dimension_bound`.

| name | kind | content | verdict | reason |
|---|---|---|---|---|
| `IsDimensionBoundedLocalChannelProtocol B` | inductive | a protocol whose input, output and every intermediate local dimension lie in `(0, B]` | a (G6) | restriction "bounded intermediate dimension": `c.maxLocalDim ≤ B` (plus positivity) on the §3 class |
| `.toIsLocalChannelProtocol` | thm | forget the bound | d | trivial once the bound is a predicate on the circuit, not a separate inductive |
| `.dimension_bounds` | thm | endpoints bounded | b (G6) | from the definition of the bound function |
| `.mono_bound` | thm | larger budget | b (G6) | |
| `.comp` | thm | same budget, depths add | b (G6) | needs a `maxLocalDim_comp = max` lemma alongside `depth_comp` |
| `OnsiteChannel.output_dimension_pos` | thm | TP onsite family cannot map to an empty site | d (or a `KrausFamily` lemma) | `KrausFamily.IsTP` with nonempty input forces a nonempty output |
| `IsLocalChannelProtocol.exists_dimension_bound` | thm | every finite protocol has some bound | b (G6) | a function on circuits is always finite: `⟨c.maxLocalDim, le_rfl⟩` |

Verbatim signatures (definition for the class referenced by many (c) items of other groups):

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
-- variables {N B C d e f : ℕ} [NeZero N]

theorem IsLocalChannelProtocol.exists_dimension_bound {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsLocalChannelProtocol T Ψ) (hd : 0 < d) :
    ∃ B, IsDimensionBoundedLocalChannelProtocol B T Ψ
```

The constructor names `onsite`, `layer` and `onsite_comp` come from the induction cases in the source.

The core bound (G6) should be a function, say `Circuit.maxLocalDim`. It would be the sup over branches and layers of `Fintype.card (X s)` for every intermediate system and site. It should come with `_comp` (max), `_mapLayers` and `_mono` lemmas. The resource point in the docstring stays: the bound must be uniform, chosen before `N`. So downstream (c) theorems should take `B` as a hypothesis `c.maxLocalDim ≤ B` quantified outside `N`.

Counts: a 1, b 4, c 0, d 2.

---

## Per-module verdict counts

| module | lines | a | b | c / c\* | d |
|---|---|---|---|---|---|
| Channel/Layer | 659 | 11 | 13 | 0 / 6 | 13 |
| Channel/Conversion | 595 | 6 | 16 | 0 / 3 | 9 |
| Channel/Feedforward | 106 | 1 | 3 | 0 | 0 |
| Channel/WholeSiteChannels | 112 | 0 | 2 | 2 | 3 |
| Channel/OnsiteChannelProduct | 144 | 1 | 2 | 0 | 6 |
| Channel/SiteBlocking | 413 | 4 | 4 | 4 | 3 |
| Channel/DataInitialization | 153 | 1 | 1 | 1 | 5 |
| Channel/ApproximateConversion | 173 | 1 | 5 | 0 / 1 | 5 |
| Channel/AsymptoticConversion | 154 | 2 | 4 | 0 / 1 (module is d if the blueprint is dropped) | 0 |
| Channel/DimensionBoundedConversion | 134 | 1 | 4 | 0 | 2 |

Rows that group several declarations count as one.

## What has to be restated (summary)

1. **Light-cone factorization** for an unbranched circuit with TP local families on a product input. It is stated once in the core and needs G1, G2 and G3. It subsumes:
   - `IsBondChannelPreparedInDepth.trace_mul_mul_eq`
   - `trace_mul_mul_eq_of_isChannelPreparedInDepth`
   - `trace_mul_mul_eq_of_isLocalChannelConversion`
   - `BondChannelLayer.dual_mul`, `OnsiteChannel.dual_mul`, `channelCircuitDual_mul_of_disjoint_lightCone`

   The ring corollaries need G4.
2. **Blocking (regrouping)** needs G5:
   - `preimage_siteBlock_neighbourhood_subset`
   - `exists_dual_comp_blockSites` / `IsBlockedLocalChannelConversion.exists_dual`
   - `trace_mul_mul_eq_of_isBlockedLocalChannelConversion`
   - `wholeSite_local` / `wholeSite_onsiteChannel`, which also need ports (G10) and G9
3. **Encoding:** `wordInitialization_data_eq_physicalEncoding` (G5, G10, G11). It may collapse to a definitional equality.
4. **Approximate composition:** `IsApproxLocalChannelConversion.trans` (G7), and `IsAsymptoticLocalChannelConversion.trans`, which is formal once (4) exists. Only needed if the phase chapter is kept.
5. **Dimension-bounded class:** `IsDimensionBoundedLocalChannelProtocol` becomes a predicate `maxLocalDim ≤ B` (G6). Its lemmas become (b).

Everything else is either the core class itself (the circuit on the ring geometry with uniform per-site systems, TP families, unbranched except for Feedforward) or a core instance. That covers `comp`/`depth_comp`, `isKrausCPTP_map`, `trace_map`, `dual_mem_supportedOperators_lightCone`, `map_ofCells`, `kraus_single` and `mapSites`. The rest is coordinate helpers made unnecessary by arbitrary basis types.
