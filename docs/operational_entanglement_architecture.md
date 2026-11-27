# Operational Entanglement Architecture (Separable Operations, Finite-Round LOCC, and Distillation)

This design note specifies how QICLean should organize general operational entanglement theory—product-Kraus separable operations, PPT preservation, finite-round finite-outcome LOCC, Bell/maximally entangled overlap bounds, and entanglement distillation rates—on top of QICLean's existing `Channel`, `ManyBody.Sites`, and `Circuit` layers.

Existing declarations and import constraints below are a source-level inventory. Proposed signatures and equivalences are design sketches, not checked Lean code; implementation must recheck elaboration, conventions, and all stated mathematical implications. Planned declarations are explicitly marked **Planned**.

---

## Verified implementation checkpoint

The curated `feature/nptent-foundations` branch now contains checked implementations of:

- `Algebra.Matrix.InvariantBlocks`: fiber-supported PSD reduction and symmetry transport.
- `Analysis.Order.RationalCertificate`: data-only rational Gram/LDL checkers with kernel soundness; regression tests include all 27 small Appendix A blocks.
- `Analysis.Order.FiniteKroneckerOrder`: heterogeneous tensor stability of symmetric order intervals.
- `Spectral.Projection.TwoForms`: the full two-form split, including singular, noncommuting and zero cases.
- `Channel.Entanglement.ReverseBlockCriterion`: pure-input vanishing, the reverse-block criterion and its heterogeneous finite tensor extension.
- `Channel.Entanglement.MaxEntangledOverlap`: PPT overlap bounds and full trace-norm stability.
- `Circuit.Model.LOCC`: finite-round operational definitions, actual branchwise factorization, and the bipartite separable-operation bridge.

The source-policy cleanup deliberately reuses original `KrausFamily` trace laws and `IsAdaptiveProtocol` identity/composition/CPTP theorems rather than adding alias declarations for them.

The sections below retain the architectural design and proposed interfaces. Their planned annotations are not a current completion checklist; consult the implemented declarations and regression tests for exact coverage. The coherence amplification, full concrete 4096-dimensional certificate, and distillation-rate integration remain separate proof obligations.

## 1. Existing Foundations (Inspected Inventory)

### 1.1 Algebraic & Kronecker Layer (`algebra`)

- `QICLean.Algebra.Kronecker.PiKronecker`:
  - `Matrix.piKronecker {ν : Type*} [Fintype ν] {ι κ : ν → Type*} (K : (k : ν) → Matrix (ι k) (κ k) ℂ) : Matrix ((k : ν) → ι k) ((k : ν) → κ k) ℂ`
  - `Matrix.piKronecker_mul`, `Matrix.piKronecker_one`, `Matrix.conjTranspose_piKronecker`
  - `Matrix.piKronecker_kronecker`: relates `piKronecker (fun k ↦ K k ⊗ₖ L k)` to `piKronecker K ⊗ₖ piKronecker L` via `Equiv.arrowProdEquivProdArrow ν ι ι'`
- `QICLean.Algebra.Kronecker.MaximallyEntangled`:
  - `Matrix.omegaVec (d : ℕ) : Fin d × Fin d → ℂ`
  - `Matrix.omegaProj (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ`
  - `Matrix.swapMatrix (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ`
  - `Matrix.one_sub_swapMatrix_posSemidef`, `Matrix.trace_omegaProj`
- `QICLean.Algebra.Kronecker.PartialTranspose`:
  - `Matrix.partialTransposeLeft`, `Matrix.partialTransposeRight`, `Matrix.IsPPT`, `Matrix.isPPT_iff_partialTransposeRight_posSemidef`, `Matrix.partialTransposeLeft_kronecker`, `Matrix.partialTransposeLeft_conj_kronecker_one`, and (in the current worktree) `Matrix.partialTransposeLeft_product_sandwich` for rectangular `Fin dA × Fin dB → Fin dAout × Fin dBout`.
  - **Current specialization:** all declarations in `PartialTranspose.lean` are typed on `Fin d × Fin d'`, not arbitrary finite types `A × B`.

### 1.2 Channel & Entanglement Layer (`channel`)

- `QICLean.Channel.KrausMap.KrausFamily`:
  - `KrausFamily (α β : Type) : Type 1` with fields `Index : Type`, `[fintype : Fintype Index]`, `op : Index → Matrix β α ℂ`
  - `KrausFamily.map`, `KrausFamily.effect`, `KrausFamily.IsTP`, `KrausFamily.IsTraceNonincreasing`, `KrausFamily.IsUnitary`, `KrausFamily.single`, `KrausFamily.adjoint`, `KrausFamily.reindex`, `KrausFamily.IsTP.reindex`, `KrausFamily.prepare`, `KrausFamily.discard`, `KrausFamily.measure`
- `QICLean.Channel.KrausMap.KrausFamilyProd`:
  - `KrausFamily.prod`, `KrausFamily.tensorRight`, `KrausFamily.traceRight`, `KrausFamily.map_prod`, `KrausFamily.IsTP.prod`
- `QICLean.Channel.Entanglement.Separable`:
  - `Matrix.IsSeparable (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) : Prop` (specialized to `Fin d × Fin d'`)
  - `Matrix.IsSeparable.posSemidef`, `Matrix.IsSeparable.isPPT`, `Matrix.isSeparable_kronecker`, `Matrix.isSeparable_sum`
- `QICLean.Channel.Entanglement.SeparableOperation` (present in this worktree, `QuantumInfo` namespace):
  - `QuantumInfo.SeparableOperation (A B Aout Bout : Type) : Type 1` with fields `Index : Type`, `[fintype : Fintype Index]`, `left : Index → Matrix Aout A ℂ`, `right : Index → Matrix Bout B ℂ`
  - `toKrausFamily : KrausFamily (A × B) (Aout × Bout)`, `single`, `id`, `map`, `map_kronecker`, `isKrausCP_map`, `IsTP`, `IsTraceNonincreasing`, `trace_map`, `trace_map_le`, `comp`, `toKrausFamily_comp_op`, `map_comp`, `map_comp_eq`
  - Polymorphic over arbitrary finite types `A B Aout Bout : Type`; no normalization baked into the structure; no identification with LOCC.
- `QICLean.Channel.Entanglement.SeparableOperationPreservation` (present in this worktree, `QuantumInfo.SeparableOperation` namespace):
  - `map_posSemidef`, `map_isSeparable`, `partialTransposeLeft_map`, `map_isPPT` for `SeparableOperation (Fin dA) (Fin dB) (Fin dAout) (Fin dBout)` (unrestricted, no normalization hypothesis).

### 1.3 Sites Layer (`sites`)

- `QICLean.ManyBody.Sites.Config`:
  - `ManyBody.Config (X : V → Type*) := (v : V) → X v`
  - `ManyBody.RegionConfig (X : V → Type*) (D : Finset V) := (v : {v // v ∈ D}) → X v`
  - `ManyBody.ComplConfig`, `ManyBody.cutEquiv : Config X ≃ RegionConfig X D × ComplConfig X D`
- `QICLean.ManyBody.Sites.Block`:
  - `ManyBody.blockSystem (f : V → V') (X : V → Type) : V' → Type`
  - `ManyBody.blockConfigEquiv (f : V → V') (X : V → Type) : Config (blockSystem f X) ≃ Config X`
- `QICLean.ManyBody.Sites.Placement.Basic`:
  - `ManyBody.place`, `ManyBody.reindex_cutEquiv_piKronecker`

### 1.4 Circuit, Party, and Model Layers (`circuit`, `party`, `model`, `protocol`)

- `QICLean.Circuit.Geometry.Basic`:
  - `QuantumCircuit.Geometry (S : Type)` (`Cell`, `cell : Cell → Finset S`, `cost : Cell → ℕ`)
  - `QuantumCircuit.Geometry.sites (S : Type) [DecidableEq S] : Geometry S` (`Cell := S`, `cell s := {s}`, `cost _ := 0`)
- `QICLean.Circuit.Geometry.Subsets`:
  - `QuantumCircuit.Geometry.subsets (S : Type) [DecidableEq S] : Geometry S` (`Cell := Finset S`, `cell := id`)
- `QICLean.Circuit.Core.Layer`, `LayerDual`, and `Parallel`:
  - `QuantumCircuit.KrausGate (D : Finset S) (X Y : S → Type) := KrausFamily (RegionConfig X D) (RegionConfig Y D)` with `KrausGate.ev`
  - `QuantumCircuit.Layer (Γ : Geometry S) G X Y`: pairwise disjoint `cells : Finset Γ.Cell`, `gate : (b : cells) → G (Γ.cell b) X Y`, `onsite : (s : Free) → KrausFamily (X s) (Y s)`
  - `Layer.Index`, `Layer.kraus`, `Layer.krausFamily`, `Layer.Forall`, `Layer.ofOnsite`, `Layer.kraus_ofOnsite`, `Layer.isTP_krausFamily`, `Layer.isTraceNonincreasing_krausFamily`
- `QICLean.Circuit.Core.Circuit`, `Channel`, `Outcome`, and `CoarsenCircuit`:
  - `inductive QuantumCircuit.Circuit (Γ : Geometry S) G [GateFamily G] : (S → Type) → (S → Type) → Type 1` with constructors `done (X)` and `step (L : Layer Γ G X Y) (next : L.Index → Circuit Γ G Y Z)`
  - `Circuit.Index` (`Unit` for `done`, `Σ i : L.Index, (next i).Index` for `step`), `instFintypeIndex`
  - `Circuit.kraus` (`1` for `done`, `(next p.1).kraus ev p.2 * L.kraus ev p.1` for `step`)
  - `Circuit.krausFamily`, `Circuit.map`, `Circuit.dual`, `Circuit.append`, `Circuit.comp`, `Circuit.kraus_append`, `Circuit.kraus_comp`, `Circuit.map_comp`, `Circuit.map_append`
  - `Circuit.Forall`, `Circuit.IsUnbranched`, `Circuit.isTP_krausFamily`, `Circuit.isTraceNonincreasing_krausFamily`, `Circuit.isKrausCPTP_map`
  - `Circuit.prob`, `Circuit.outcomeProb`
  - `Circuit.Coarsenable`, `Circuit.coarsen`, `Circuit.kraus_coarsen`
- `QICLean.Circuit.Model.Protocol`, `Approximate`, and `Measurement`:
  - `QuantumCircuit.IsAdaptiveProtocol`, `IsProtocol`, `IsBoundedProtocol`, `IsConversion`, `IsAdaptiveConversion`
  - `QuantumCircuit.IsApproxConversion` (measured in `Matrix.rectangularTraceNorm`), `IsAsymptoticConversion`
  - `Circuit.rounds`, `IsMeasurementConversion`, `IsOneRoundConversion`
- `QICLean.Circuit.Party.Syntax.PartyCircuit`, `Local`, and `LocalProduct`:
  - `QuantumCircuit.Party.PartyCircuit`: unbranched, sequential (and single-branch under `GateFamily.UniqueOutcome`); `PartyCircuit.IsLocal`, `partyOp`, `op_eq_piKronecker_partyOp`, `op_eq_reindex_kronecker_regionOp`.
  - **Architectural distinction:** `PartyCircuit` is unbranched and designed for PEPS compression words. Adaptive classical communication requires branching (`Circuit.step L next`), so LOCC must be built on `QuantumCircuit.Circuit`, not `PartyCircuit`.

---

## 2. Import DAG and Layer Ownership

From `scripts/check_import_layers.py` (direct imports after aggregator expansion, with `DEBT = {}` and `SUBLAYER_DEBT = {}`):

```text
algebra ──▶ analysis ──▶ spectral ──▶ channel ──▶ kraus ──▶ entropy
                                         │                      │
                                         ▼                      ▼
                                     ManyBody/Sites ◀───────────┘
                                         │
                  Circuit/Gate ──────────┼──▶ Circuit/{Geometry,Core} ("circuit")
                                         │         │
                                         │         ├──▶ Circuit/Party
                                         │         ├──▶ Circuit/Algorithm
                                         │         ├──▶ Circuit/Model ──▶ Circuit/Compile ──▶ Circuit/Protocol
                                         │         └──▶ Circuit/Simulation (+ Dynamics, Hamiltonian)
```

Key invariants enforced by `scripts/check_import_layers.py`:
1. **No `channel → circuit` edge:** `channel` may only import `{algebra, analysis, spectral}`. Within `QICLean.Channel`, `scripts/library_sublayers.json` places `Entanglement` after `Positive` (and transitively after `KrausMap`, `PartialTrace`, `Schmidt`, `Schwarz`).
2. **No `entropy → circuit` or `entropy → model` edge:** `entropy` may only import `{algebra, analysis, spectral, channel, kraus}`.
3. **`model` and `protocol` allowed imports:**
   - `model`: `MATRIX | CHANNEL | {"sites", "gate", "circuit"}`
   - `protocol`: `MATRIX | CHANNEL | {"sites", "gate", "circuit", "model", "compile"}`
   Neither directly imports `entropy` today.

### Layer Placement Decisions

| Component | Target Layer & Prefix | Rationale |
|---|---|---|
| Polymorphic partial transpose / `bipartiteTensorPower`, `(omegaProj d)^{T₁} = (1/d) • swapMatrix d`, trace-pairing symmetry | `algebra` (`QICLean.Algebra.Kronecker.*`) | Pure matrix/Kronecker identities; needed by both `Channel` and `Circuit.Model`. |
| `SeparableOperation`, `SeparableOperationPreservation` (PPT & separability preservation), Bell/maximally-entangled overlap & `≤ 1/d` PPT bound | `channel` (`QICLean.Channel.Entanglement.*`) | Single-system/bipartite channel & state properties; zero dependency on `Circuit` or `Sites`. |
| Party-local adaptive circuit restriction, finite-round LOCC predicates (`IsFiniteRoundLOCC`, `IsBoundedRoundLOCC`), branchwise product-Kraus factorization theorem (`LOCC ⊆ SEP`) | `model` (`QICLean.Circuit.Model.*`) | Matches `Circuit/Model/Protocol.lean` and `Circuit/Model/Measurement.lean`, which own protocol classes defined as restrictions of `QuantumCircuit.Circuit`. Imports `Circuit.Core`, `Circuit.Model.Protocol`, and `Channel.Entanglement.SeparableOperation`. |
| Operational entanglement distillation rate definitions, monotonicity, and PPT zero-distillation theorem ($E_D(\rho) = 0$ for PPT $\rho$) | `model` (`QICLean.Circuit.Model.*`) | Quantifies over operational protocol classes (`IsFiniteRoundLOCC`, `SeparableOperation`, etc.); cannot live in `Entropy` (which cannot import `Circuit`/`Model`). Does **not** require `Entropy` imports (only `Analysis`, `Channel`, `Sites`, `Circuit`). |
| Concrete distillation protocols (e.g., BBPSSW/DEJMPS recurrence, hashing, pure-state concentration circuits) | `protocol` (`QICLean.Circuit.Protocol.*`) | Matches `Teleportation`, `GHZ`, `WeightedGHZ`; may import `Model` and `Compile`. |
| Future entropic converse/achievability theorems (e.g., $E_D(\rho) \le E_R(\rho)$, $E_D(|\psi\rangle) = S(\rho_A)$) | Separate integration prefix or explicit `protocol → entropy` edge (future RFC) | Keeps `Circuit/Model` free of `Entropy` unless/until an entropic converse is formalized; never introduces `Entropy → Circuit`. |

---

## 3. Minimal Operational Definition of Finite-Round Finite-Outcome LOCC

### 3.1 Why Existing `QuantumCircuit.Circuit` Already Captures Adaptive Finite-Round Finite-Outcome Structure

`QuantumCircuit.Circuit Γ KrausGate X Z` is an `inductive` type:
- `done X` terminates the protocol.
- `step L next` applies a layer `L : Layer Γ KrausGate X Y` (allowing local dimension changes / ancilla preparation and discard via rectangular `KrausFamily`), obtains a classical outcome `i : L.Index` (a `Fintype`), and branches to `next i : Circuit Γ KrausGate Y Z`.

Consequently, every term `c : Circuit Γ KrausGate X Z` is **inherently finite-round** (well-founded finite tree height) and **inherently finite-outcome** (`Fintype c.Index`). Moreover, `next i` depends on the entire outcome tuple `i : L.Index`, which models **broadcast classical communication** of all measurement outcomes from round `L` to all parties before the next round.

### 3.2 Party-Local Restriction (Do Not Define LOCC by Assuming Product-Kraus Form)

We define finite-round LOCC operationally by restricting **cell locality** and **local trace preservation** on `Circuit`, and then **prove** that every branch factors as a product of party-local Kraus operators.

#### Canonical party-level formulation (`Geometry.sites P`)
Let `P : Type` with `[Fintype P] [DecidableEq P]` be the finite set of parties (for bipartite LOCC, `P = Bool` with `false` = Alice, `true` = Bob; or `P = Fin 2`).
- Each party `p : P` owns a single site whose basis type `X p` represents **that party's entire local Hilbert space** (including any multi-copy register `Fin n → A` and local ancillas).
- On `Geometry.sites P`, every cell is a singleton `{p}`. Thus every `Layer (Geometry.sites P) KrausGate X Y` automatically applies only single-party Kraus instruments (`gate` on `{p}`, `onsite` on `p ∉ cells`).
- **Round count (Planned** in `Circuit.Core` or `Circuit.Model.LOCC`):
  ```lean
  def Circuit.stepCount : {X Z : S → Type} → Circuit Γ G X Z → ℕ
    | _, _, done _ => 0
    | _, _, step _ next => 1 + Finset.univ.sup (fun i ↦ (next i).stepCount)
  ```
  (Note: `Geometry.sites P` has `cost _ := 0`, so `Circuit.depth` is always `0` on `Geometry.sites P`; `stepCount` measures the number of interactive rounds, i.e., $\mathrm{LOCC}_r$.)
- **Operational predicate (multipartite, Planned):**
  ```lean
  /-- A map realised by an `r`-round finite-outcome LOCC protocol on parties `P`. -/
  def IsBoundedRoundLOCC (P : Type) [Fintype P] [DecidableEq P]
      {X Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Z p)]
      (r : ℕ)
      (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
    ∃ c : Circuit (Geometry.sites P) KrausGate X Z,
      c.Forall KrausGate.ev KrausFamily.IsTP ∧
      c.stepCount ≤ r ∧
      c.map KrausGate.ev = Φ

  /-- Finite-round finite-outcome LOCC: `∃ r, IsBoundedRoundLOCC P r Φ`
  (equivalently `IsAdaptiveProtocol (Geometry.sites P) 0 Φ`). -/
  def IsFiniteRoundLOCC (P : Type) [Fintype P] [DecidableEq P]
      {X Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Z p)]
      (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
    IsAdaptiveProtocol (Geometry.sites P) 0 Φ
  ```
  *Observation:* `IsFiniteRoundLOCC P Φ` is definitionally `IsAdaptiveProtocol (Geometry.sites P) 0 Φ`, so it immediately inherits `IsAdaptiveProtocol.id`, `IsAdaptiveProtocol.comp`, `IsAdaptiveProtocol.step`, and `IsAdaptiveProtocol.isKrausCPTP` from `QICLean.Circuit.Model.Protocol` with zero duplicated boilerplate.

  *Parallel vs. single-party-per-round equivalence:* In `Layer (Geometry.sites P)`, multiple parties may act simultaneously in one layer, with all outcomes broadcast before the next layer. Restricting to at most one non-identity party per layer gives the same finite-round class `IsFiniteRoundLOCC` (a parallel layer serializes into `|P|` single-party layers by setting the other parties to `KrausFamily.single 1`), while changing only the round count `r` by at most a factor of `|P|`.

#### Multi-site-per-party generalization (via `Circuit.Coarsenable`)
When sites `S` are partitioned among parties via `owner : S → P` on an arbitrary geometry `Γ : Geometry S` (for example, $n$ local qudits per party with intra-party gates):
- **Party-local circuit predicate (Planned):**
  ```lean
  def Circuit.IsPartyLocal (owner : S → P) : {X Z : S → Type} → Circuit Γ KrausGate X Z → Prop
    | _, _, done _ => True
    | _, _, step L next =>
        (∀ b ∈ L.cells, ((Γ.cell b).image owner).card ≤ 1) ∧
        ∀ i, (next i).IsPartyLocal owner
  ```
- **Bridge to `Geometry.sites P`:** Any `c : Circuit Γ KrausGate X Z` with `c.IsPartyLocal owner` (with empty cells either forbidden or absorbed as scalar factors) coarsens onto `Geometry.sites P` via `Layer.coarsen` / `Circuit.coarsen` (`Circuit/Core/CoarsenCircuit.lean`), which already preserves `Circuit.kraus` up to `ManyBody.blockConfigEquiv owner`.
- **Crucial modeling rule for distillation:** For $n$-copy distillation of $\rho^{\otimes n}$, Alice must be allowed arbitrary joint operations across all $n$ of her local systems. Therefore, the canonical bipartite LOCC model uses `P = Bool` with `X false = (Fin n → A)` and `X true = (Fin n → B)` (not `Geometry.sites (Fin n ⊕ Fin n)`, which would forbid intra-Alice gates between copies).

---

## 4. Exact Branchwise Product-Kraus Theorem and Tensor Basis Reindexing

### 4.1 Multipartite Branchwise Factorization on `Geometry.sites P`

1. **Single-layer party extraction (Planned):**
   For `L : Layer (Geometry.sites P) KrausGate X Y` and `i : L.Index`, define
   ```lean
   def Layer.siteKraus (L : Layer (Geometry.sites P) KrausGate X Y)
       (i : L.Index) (p : P) : Matrix (Y p) (X p) ℂ
   ```
   - If `hp : p ∈ L.cells`: transport `(L.gate ⟨p, hp⟩).op (i.1 ⟨p, hp⟩) : Matrix (RegionConfig Y {p}) (RegionConfig X {p}) ℂ` along `Equiv.piUnique` (identifying `RegionConfig X {p} ≃ X p`).
   - If `hp : p ∉ L.cells`: `(L.onsite ⟨p, by simpa using hp⟩).op (i.2 ⟨p, by simpa using hp⟩)`.
   - **Lemma (Planned):**
     ```lean
     theorem Layer.kraus_eq_piKronecker_siteKraus
         (L : Layer (Geometry.sites P) KrausGate X Y) (i : L.Index) :
         L.kraus KrausGate.ev i = Matrix.piKronecker (L.siteKraus i)
     ```
     Proof: entrywise from `Layer.kraus_apply` and `Matrix.piKronecker_apply`, splitting `Finset.univ` into `L.cells` and its complement.

2. **Circuit branchwise party Kraus extraction (Planned):**
   By structural recursion on `c : Circuit (Geometry.sites P) KrausGate X Z`:
   ```lean
   def Circuit.partyKraus : {X Z : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
       (c : Circuit (Geometry.sites P) KrausGate X Z) → c.Index →
       (p : P) → Matrix (Z p) (X p) ℂ
     | _, _, _, _, done _, _ => fun _ ↦ 1
     | _, _, _, _, step L next, ⟨i, j⟩ => fun p ↦ (next i).partyKraus j p * L.siteKraus i p
   ```
   - **Main Branchwise Theorem (Planned):**
     ```lean
     theorem Circuit.kraus_eq_piKronecker_partyKraus
         (c : Circuit (Geometry.sites P) KrausGate X Z) (q : c.Index) :
         c.kraus KrausGate.ev q = Matrix.piKronecker (c.partyKraus q)
     ```
     Proof by induction on `c`:
     - `done`: `Matrix.piKronecker_one.symm`.
     - `step L next, ⟨i, j⟩`: `Circuit.kraus_step`, induction hypothesis on `next i`, `Layer.kraus_eq_piKronecker_siteKraus`, and `Matrix.piKronecker_mul`.

### 4.2 Bipartite Tensor Basis Reindexing and `SeparableOperation` Bridge

Three distinct coordinate systems appear in bipartite operational entanglement theory, linked by explicit `Equiv`s:

1. **Party-configuration basis vs. party-major product basis (`Bool`-indexed `Config X` vs. `X false × X true`):**
   ```lean
   def boolConfigEquiv (X : Bool → Type) : Config X ≃ X false × X true where
     toFun f := (f false, f true)
     invFun p b := match b with | false => p.1 | true => p.2
     left_inv f := funext fun b ↦ by cases b <;> rfl
     right_inv _ := rfl
   ```
   Under `boolConfigEquiv`, `Matrix.piKronecker` becomes binary Kronecker product `⊗ₖ`:
   ```lean
   theorem submatrix_boolConfigEquiv_piKronecker
       {X Z : Bool → Type} (K : (b : Bool) → Matrix (Z b) (X b) ℂ) :
       (Matrix.piKronecker K).submatrix (boolConfigEquiv Z).symm (boolConfigEquiv X).symm =
         K false ⊗ₖ K true
   ```

2. **Bipartite circuit → `QuantumInfo.SeparableOperation` (Planned):**
   ```lean
   def Circuit.toSeparableOperation
       {X Z : Bool → Type} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
       (c : Circuit (Geometry.sites Bool) KrausGate X Z) :
       QuantumInfo.SeparableOperation (X false) (X true) (Z false) (Z true) where
     Index := c.Index
     left q := c.partyKraus q false
     right q := c.partyKraus q true
   ```
   **Exact bridge theorems (Planned):**
   - Branchwise:
     ```lean
     theorem Circuit.toSeparableOperation_op
         (c : Circuit (Geometry.sites Bool) KrausGate X Z) (q : c.Index) :
         c.toSeparableOperation.toKrausFamily.op q =
           (c.kraus KrausGate.ev q).submatrix (boolConfigEquiv Z).symm (boolConfigEquiv X).symm
     ```
   - Channel-level (using `Layer.map_submatrix_of_op` or `KrausFamily.reindex`):
     ```lean
     theorem Circuit.toSeparableOperation_map
         (c : Circuit (Geometry.sites Bool) KrausGate X Z)
         (ρ : Matrix (X false × X true) (X false × X true) ℂ) :
         c.toSeparableOperation.map ρ =
           (c.map KrausGate.ev (ρ.submatrix (boolConfigEquiv X) (boolConfigEquiv X))).submatrix
             (boolConfigEquiv Z).symm (boolConfigEquiv Z).symm
     ```
   - Normalization:
     - `c.Forall KrausGate.ev KrausFamily.IsTP → c.toSeparableOperation.IsTP` (from `Circuit.isTP_krausFamily` and `KrausFamily.IsTP.reindex`).
     - `c.Forall KrausGate.ev KrausFamily.IsTraceNonincreasing → c.toSeparableOperation.IsTraceNonincreasing`.

3. **Copy-major vs. party-major reindexing for $n$-copy states $\rho^{\otimes n}$:**
   - Given `ρ : Matrix (A × B) (A × B) ℂ`, the $n$-copy tensor power `Matrix.piKronecker (fun _ : Fin n ↦ ρ)` is indexed by `Fin n → (A × B)` (copy-major).
   - Bipartite `SeparableOperation (Fin n → A) (Fin n → B) Aout Bout` and `Circuit (Geometry.sites Bool)` with `X = Bool.rec (Fin n → A) (Fin n → B)` act on `(Fin n → A) × (Fin n → B)` (party-major).
   - The canonical reindexing is Mathlib's `Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ A) (fun _ ↦ B) : (Fin n → A × B) ≃ (Fin n → A) × (Fin n → B)`, already used in `Matrix.piKronecker_kronecker`.
   - Define the party-major $n$-copy state:
     ```lean
     def bipartiteTensorPower (n : ℕ) (ρ : Matrix (A × B) (A × B) ℂ) :
         Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
       (Matrix.piKronecker (fun _ : Fin n ↦ ρ)).submatrix
         (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ A) (fun _ ↦ B)).symm
         (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ A) (fun _ ↦ B)).symm
     ```
   - **Key algebraic property (Planned):** `partialTransposeLeft (bipartiteTensorPower n ρ) = bipartiteTensorPower n (partialTransposeLeft ρ)`, hence `IsPPT ρ → IsPPT (bipartiteTensorPower n ρ)` (by `PosSemidef.piKronecker` + `PosSemidef.submatrix`).

4. **Bridge between arbitrary finite types `A × B` and `Fin d × Fin d'`:**
   - `Matrix.partialTransposeLeft`, `Matrix.IsPPT`, `Matrix.IsSeparable`, and `SeparableOperationPreservation` are currently typed on `Fin d × Fin d'`.
   - Either generalize `partialTransposeLeft` / `partialTransposeRight` / `IsPPT` / `IsSeparable` and `SeparableOperationPreservation` to arbitrary `[Fintype A] [Fintype B]`, or bridge `(Fin n → Fin dA) × (Fin n → Fin dB)` to `Fin (dA ^ n) × Fin (dB ^ n)` via `Fintype.equivFin` (the polymorphic generalization is cleaner and avoids repeated reindex boilerplate in distillation proofs).

---

## 5. PPT Preservation, Bell Overlap, and Distillation Rates

### 5.1 PPT and Separability Preservation under `SeparableOperation` (`QICLean.Channel.Entanglement`)

- **Already present on `Fin d` (`SeparableOperationPreservation.lean` + `PartialTranspose.lean`):**
  - `Matrix.partialTransposeLeft_product_sandwich`:
    `partialTransposeLeft ((L ⊗ₖ R) * ρ * (L ⊗ₖ R)ᴴ) = (L.map star ⊗ₖ R) * partialTransposeLeft ρ * (L.map star ⊗ₖ R)ᴴ`.
  - `QuantumInfo.SeparableOperation.map_posSemidef`, `map_isSeparable`, `partialTransposeLeft_map`, `map_isPPT` (unrestricted, no `IsTP` required).
- **Planned extension:** lift these to arbitrary finite types `A B Aout Bout` (or provide a `SeparableOperation.reindex` lemma to transfer `map_isPPT`/`map_isSeparable` along `Fintype.equivFin`).
- **Corollary for finite-round LOCC (Planned, in `Circuit/Model/LOCC.lean`):** Every bipartite `IsFiniteRoundLOCC` channel preserves both `IsSeparable` and `IsPPT`.

### 5.2 Maximally Entangled (Bell) Overlap and PPT Obstruction (`QICLean.Algebra.Kronecker` & `QICLean.Channel.Entanglement`)

For `d : ℕ` and `σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ`, the maximally entangled overlap is:
```lean
noncomputable def maxEntangledOverlap (d : ℕ)
    (σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  (Matrix.omegaProj d * σ).trace.re
```
Minimal chain of lemmas (all in `Algebra` / `Channel`, zero `Circuit` dependency):
1. `partialTransposeLeft_omegaProj (d : ℕ) (hd : 0 < d) : partialTransposeLeft (omegaProj d) = (1 / (d : ℂ)) • swapMatrix d`.
2. `trace_mul_partialTransposeLeft (A B : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) : (A * B).trace = (partialTransposeLeft A * partialTransposeLeft B).trace`.
3. **PPT overlap bound:** If `IsPPT σ`, `σ.PosSemidef`, `σ.trace = 1`, and `0 < d`, then
   $$\mathrm{maxEntangledOverlap}\ d\ \sigma = \frac{1}{d} \operatorname{Re}\operatorname{tr}(F \cdot \sigma^{T_1}) \le \frac{1}{d} \operatorname{Re}\operatorname{tr}(\sigma^{T_1}) = \frac{1}{d},$$
   using `Matrix.one_sub_swapMatrix_posSemidef` (already in `MaximallyEntangled.lean`) and `trace_partialTransposeLeft`.
4. **Trace-norm to overlap bound:** For any density matrix `σ` and `0 < d`,
   $$|1 - \mathrm{maxEntangledOverlap}\ d\ \sigma| \le \mathrm{rectangularTraceNorm}(\sigma - \mathrm{omegaProj}\ d),$$
   using `|tr(A B)| ≤ ‖A‖ · ‖B‖₁` and `‖omegaProj d‖ ≤ 1` (and the sharper factor `1/2` if desired).

### 5.3 Distillation Rates (`QICLean.Circuit.Model.Distillation`)

**Infimum/supremum modeling rule:** A general channel class can be empty at a given input/output size. Either define achievable rates by explicit existence of channel sequences, or take approximation-error infima in the extended nonnegative reals, with infimum of the empty set equal to positive infinity. Do not use real-valued sInf without a nonemptiness hypothesis: its empty-set value can spuriously declare all rates achievable. Taking the rate supremum in the extended nonnegative reals also avoids an unjustified boundedness assumption; the zero-distillation theorem then proves that supremum is zero. The source-style formulas below are schematic and must follow this convention.

Parameterize asymptotic distillation by a bipartite channel class `C` (a predicate on linear maps `Matrix ((Fin n → A) × (Fin n → B)) _ ℂ →ₗ[ℂ] Matrix (Fin d × Fin d) _ ℂ`, instantiated with `IsBipartiteFiniteRoundLOCC`, `IsSeparableChannel`, or `IsPPTPreservingChannel`):
- **Achievable distillation rate `R ≥ 0`:** for `ρ : Matrix (A × B) (A × B) ℂ`, there exist target dimensions `d : ℕ → ℕ` with `∀ᶠ n, 0 < d n` and `Tendsto (fun n ↦ Real.log (d n) / (n * Real.log 2)) atTop (𝓝 R)` (or `liminf ≥ R` / `2^{⌊R n⌋}` qubits—state the exact convention in the docstring and match the cited paper faithfully), and channels `Λ n` in class `C` such that
  `Tendsto (fun n ↦ rectangularTraceNorm (Λ n (bipartiteTensorPower n ρ) - omegaProj (d n))) atTop (𝓝 0)`
  (equivalently, `Tendsto (fun n ↦ maxEntangledOverlap (d n) (Λ n (bipartiteTensorPower n ρ))) atTop (𝓝 1)` for trace-preserving `Λ n`).
- **Distillable entanglement:** `distillableEntanglement C ρ := sSup {R : ℝ | 0 ≤ R ∧ IsAchievableDistillationRate C ρ R}`.
- **PPT zero-distillation theorem:** If `ρ` is a PPT density matrix, then for any class `C` contained in PPT-preserving CPTP maps (in particular `IsBipartiteFiniteRoundLOCC` and `IsSeparableChannel`), `distillableEntanglement C ρ = 0`.
  *Proof sketch:* `IsPPT ρ` ⇒ `IsPPT (bipartiteTensorPower n ρ)` ⇒ `IsPPT (Λ n (bipartiteTensorPower n ρ))` ⇒ `maxEntangledOverlap (d n) (Λ n (bipartiteTensorPower n ρ)) ≤ 1 / d n`. If `R > 0`, then `d n → ∞`, so `1 / d n → 0`, contradicting `maxEntangledOverlap → 1`.

---

## 6. Separation of Scope: Finite-Round LOCC vs. Closure and Infinite-Round LOCC

Keep bounded-round, finite-round, infinite-round, and closure conventions separate. For a fixed explicit model, the relevant inclusion targets are
$$\mathrm{LOCC}_r \subseteq \mathrm{LOCC}_{\mathbb{N}} \subseteq \overline{\mathrm{LOCC}_{\mathbb{N}}} \subseteq \mathrm{SEP} \subseteq \mathrm{PPT}.$$
These inclusions require proofs for the chosen channel/instrument conventions; no strictness or classification theorem is assumed. Strictness can depend on dimensions, outcomes, and the notion of operation, and is unnecessary for the undistillability criterion. Infinite-round protocols require their own definition and inclusion theorem.

Architectural rules to enforce faithfulness (per `CLAUDE.md` §Faithfulness rule):
1. **`IsFiniteRoundLOCC` models $\mathrm{LOCC}_{\mathbb{N}}$ only.** Never label a theorem over `IsFiniteRoundLOCC` as holding for infinite-round $\mathrm{LOCC}$ or $\overline{\mathrm{LOCC}}$ unless proved for the larger class.
2. **Topological closure $\overline{\mathrm{LOCC}}$** (if needed later) should be defined as a separate predicate `IsLOCCClosure` using `closure` in the finite-dimensional linear-map topology on `Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (Aout × Bout) (Aout × Bout) ℂ` of the set `{Φ | IsBipartiteFiniteRoundLOCC Φ}`.
   - PPT preservation and the `≤ 1/d` Bell-overlap bound pass from `IsBipartiteFiniteRoundLOCC` to `IsLOCCClosure` by continuity of `partialTransposeLeft` and closedness of the PSD cone, **without** needing an infinite-round circuit syntax.
3. **Infinite-round LOCC** (coinductive/countable-tree protocols converging in trace/diamond norm) is out of scope for the finite `Circuit` inductive type and should not be conflated with `IsFiniteRoundLOCC`.

---

## 7. Minimal Missing Lemmas

1. **`Algebra` (`PartialTranspose` & `TensorPower`):**
   - Trace-pairing symmetry: `(A * B).trace = (partialTransposeLeft A * partialTransposeLeft B).trace`.
   - `partialTransposeLeft (omegaProj d) = (1 / (d : ℂ)) • swapMatrix d` (for `0 < d`).
   - `bipartiteTensorPower` definition, `partialTransposeLeft_bipartiteTensorPower`, and `IsPPT ρ → IsPPT (bipartiteTensorPower n ρ)` (either by generalizing `partialTransposeLeft`/`IsPPT` to arbitrary `[Fintype A] [Fintype B]`, or by providing `Fin (dA ^ n) × Fin (dB ^ n)` reindexing bridges).
2. **`Channel` (`Entanglement`):**
   - `SeparableOperation.reindex` (or polymorphic `SeparableOperationPreservation` if `IsPPT`/`IsSeparable` are generalized to arbitrary finite types).
   - `maxEntangledOverlap` definition, `ppt_maxEntangledOverlap_le` (`≤ 1 / d`), and trace-norm/overlap comparison lemma `one_sub_maxEntangledOverlap_le_rectangularTraceNorm`.
3. **`Circuit.Model` (`LOCC` & `Distillation`):**
   - `Circuit.stepCount` and `stepCount_comp`.
   - `Layer.siteKraus` and `Layer.kraus_eq_piKronecker_siteKraus` on `Geometry.sites P`.
   - `Circuit.partyKraus` and `Circuit.kraus_eq_piKronecker_partyKraus`.
   - `boolConfigEquiv`, `submatrix_boolConfigEquiv_piKronecker`, `Circuit.toSeparableOperation`, and branchwise/channel-level/TP bridge theorems.
   - `IsBoundedRoundLOCC`, `IsFiniteRoundLOCC`, `IsBipartiteFiniteRoundLOCC`, and corollaries `IsBipartiteFiniteRoundLOCC.exists_separableOperation`, `isPPT_map`, `isSeparable_map`.
   - `IsAchievableDistillationRate`, `distillableEntanglement`, class-inclusion monotonicity, and `distillableEntanglement_eq_zero_of_isPPT`.

---

## 8. Concrete Implementation & Validation Sequence

Execute in strict bottom-up layer order so each step builds cleanly and passes `scripts/check_import_layers.py` with zero debt:

1. **Step 1 (`algebra`):** Extend `QICLean/Algebra/Kronecker/PartialTranspose.lean` (or add `QICLean/Algebra/Kronecker/PartialTransposeBipartite.lean`) with trace-pairing symmetry, `partialTransposeLeft_omegaProj`, and `bipartiteTensorPower` PPT preservation (plus polymorphic `IsPPT` or `Fin` reindexing bridge).
2. **Step 2 (`channel`):** Extend `QICLean/Channel/Entanglement/SeparableOperation.lean` / `SeparableOperationPreservation.lean` with `SeparableOperation.reindex` (or polymorphic preservation) and add `QICLean/Channel/Entanglement/MaxEntangledOverlap.lean` (`maxEntangledOverlap`, `≤ 1/d` PPT bound, trace-norm comparison) with companion tests under `QICLeanTest/`. Regenerate `QICLean/Channel/Entanglement.lean` via `scripts/generate_import_aggregators.py`.
3. **Step 3 (`model` — LOCC):** Add `QICLean/Circuit/Model/LOCC.lean` (plus tests in `QICLeanTest/LOCC.lean`) defining `Circuit.stepCount`, `Layer.siteKraus`, `Circuit.partyKraus`, `Circuit.kraus_eq_piKronecker_partyKraus`, `boolConfigEquiv`, `Circuit.toSeparableOperation`, `IsBoundedRoundLOCC`, `IsFiniteRoundLOCC`, `IsBipartiteFiniteRoundLOCC`, and proving the branchwise/channel-level `LOCC ⊆ SEP` and PPT-preservation theorems.
4. **Step 4 (`model` — Distillation):** Add `QICLean/Circuit/Model/Distillation.lean` (plus tests in `QICLeanTest/Distillation.lean`) defining `IsAchievableDistillationRate` and `distillableEntanglement` parameterized by a bipartite channel class, proving monotonicity under class inclusion (`LOCC ⊆ SEP ⊆ PPT`), and proving `distillableEntanglement_eq_zero_of_isPPT`. Regenerate `QICLean/Circuit/Model.lean` via `scripts/generate_import_aggregators.py`.
5. **Step 5 (Optional follow-up — Multi-site coarsening & concrete protocols):**
   - Add `Circuit.IsPartyLocal` coarsening lemma onto `Geometry.sites P` in `QICLean/Circuit/Model/LOCC.lean` (or a companion module) using `Circuit.coarsen`.
   - Add concrete distillation protocols under `QICLean/Circuit/Protocol/Distillation/`.
   - If `IsLOCCClosure` is needed downstream, add it as a separate module `QICLean/Circuit/Model/LOCCClosure.lean`.

### Verification Gates (per step)

- `python3 scripts/generate_import_aggregators.py --check` (after regenerating aggregators)
- `python3 scripts/check_import_layers.py` (verify zero layer/sublayer violations and no `Channel → Circuit` or `Entropy → Circuit` edges)
- `python3 scripts/test_architecture_policies.py` (confirm policy suite passes)
- `lake build` on each touched module and full library (plus `QICLeanTest/` modules)
- `rg -n "sorry|axiom" <changed files>` (zero proof-integrity blockers)

---

## 9. General Map-Level Reverse-Block Criterion and Self-Contained Certificate Architecture

Following the architectural pattern of `CertifiedGaps` (`criterion.tex`, `rings.tex`, and `Seed/Certificate.lean`), QICLean should extract and formalize the **broad, ansatz-independent mathematical mechanism** rather than only migrating LOCC/separable-operation plumbing, and every accepted argument must be completely self-contained over QICLean + Mathlib (no cited unformalized theorems and no trusted external Python/SDP checks).

### 9.1 Map-Level Reverse-Block Mechanism (Ansatz-Independent)

At the single-system / rectangular-channel level (`QICLean.Channel.Entanglement`, zero `Circuit` dependency), the mechanism separates cleanly into three reusable layers:

1. **Choi-kernel lemma for complex pure inputs (Planned):**
   For the unnormalized, input-first convention `Matrix.rectangularChoi` (`QICLean.Channel.Choi.RectangularChoi`), $J(\Phi)_{(i,a),(j,b)} = \Phi(E_{ij})_{a,b}$, so for any $x \in \mathbb{C}^\alpha$ and $y \in \mathbb{C}^\beta$:
   $$(x \otimes y)^\dagger J(\Phi) (x \otimes y) = y^\dagger \,\Phi(|\bar{x}\rangle\langle \bar{x}|)\, y.$$
   - **Complex-conjugate invariant:** For an arbitrary complex vector $u : \alpha \to \mathbb{C}$, the Choi kernel vector is `star u ⊗ y` (entrywise complex conjugate $\bar{u}$), **not** `u ⊗ y`.
   - For any rectangular CP map `Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ` (`IsKrausCP Φ`, equivalently `J(Φ).PosSemidef`):
     $$\Phi(|u\rangle\langle u|) = 0 \iff \bigl[\forall y,\ (\bar{u} \otimes y) \in \ker J(\Phi)\bigr].$$
     Either equivalent condition implies
     $$\forall z : \alpha \to \mathbb{C},\quad \Phi(|z\rangle\langle u|) = 0 \quad\text{and}\quad \Phi(|u\rangle\langle z|) = 0.$$

The separate `ChoiRectangular.choiMatrix` API in `QICLean.Channel.Choi.Rectangular` is normalized and output-first. For positive input dimension d it is the swapped unnormalized Choi matrix divided by d. Its quadratic formula therefore uses the vector y tensor x and has an additional factor 1/d. Do not apply the input-first formula to that API without the conversion. Zero input dimension requires a separate trivial case.

   The off-diagonal vanishing conclusion also has a direct Kraus proof: from a CP map Phi with Phi(uu*) = 0, taking the trace gives a sum of squared norms of K_i u equal to zero. Hence every K_i u vanishes, and Phi(zu*) = Phi(uz*) = 0 for every z. This avoids a Choi-convention dependency in the abstract map-level theorem.

2. **General map-level reverse-block theorem (Planned):**
   Let `C S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ` be arbitrary linear maps satisfying:
   - `IsKrausCP (C + S)` and `IsKrausCP (C - S)`,
   - `IsCompletelyCopositiveMap S` (defined in `QICLean.Channel.Basic`).
   Then:
   - `C` is CP (`IsKrausCP C`) and `-J(C) ≤ J(S) ≤ J(C)`.
   - Whenever `C (vecMulVec u (star u)) = S (vecMulVec u (star u))` for a complex vector `u : α → ℂ`, applying the Choi-kernel lemma to `C - S` yields `∀ y, (star u ⊗ y) ∈ ker J(C - S)`, and hence **off-diagonal agreement**
     $$\forall z : \alpha \to \mathbb{C},\quad C(|z\rangle\langle u|) = S(|z\rangle\langle u|)$$
     (and symmetrically on $|u\rangle\langle z|$), which pairs with `IsCompletelyCopositiveMap S` (transposition of the input block) to force the reverse-block positivity/obstruction constraint without any symmetry or ansatz hypothesis.

3. **Full bipartite product-map criterion for `C = L ⊗ M` (Planned):**
   Specialize `C` to the tensor product `L ⊗ M` of **arbitrary rectangular local CP maps** `L : Matrix A A ℂ →ₗ[ℂ] Matrix Aout Aout ℂ` and `M : Matrix B B ℂ →ₗ[ℂ] Matrix Bout Bout ℂ` (`IsKrausCP L`, `IsKrausCP M`), acting on an **arbitrary complex pure input** `u : A × B → ℂ` (no restriction to real vectors, square maps, or Werner/isotropic symmetry). Keep the statement, proof, and provenance strictly independent of any Werner ansatz; downstream formalizations instantiate it for specific families.

### 9.2 Self-Contained Verification Architecture (No Trusted External Oracles)

Mirroring `CertifiedGaps/Seed/Certificate.lean`:
- **Separation of abstract criterion and concrete witness:** QICLean owns the general map-level reverse-block criterion and product-map criterion in `QICLean.Channel.Entanglement` (e.g., `QICLean/Channel/Entanglement/ReverseBlockCriterion.lean`).
- **In-kernel certificates only:** Any concrete instantiation (such as certifying positivity of $J(C \pm S)$ or $J(S \circ \Theta)$ for a specific state or parameter regime in a downstream repo) must supply an explicit Lean-checked witness (e.g., rational Gram / Cholesky / sum-of-squares factorization or decidable rational inequalities checked inside Lean), never an axiomatized SDP output or external Python script.
- **Import DAG compliance:** `QICLean/Channel/Entanglement/ReverseBlockCriterion.lean` imports only `QICLean.Channel.Basic`, `QICLean.Channel.Choi.Rectangular` / `RectangularChoi`, `QICLean.Channel.KrausMap.KrausFamilyProd`, and `QICLean.Algebra.Kronecker.PartialTranspose`—staying strictly inside the `channel` layer (`Entanglement` sublayer) with zero `Channel → Circuit` dependency.
