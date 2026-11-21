# CLAUDE.md

This file provides guidance to AI coding assistants working with code in this repository.

## Project Overview

QICLean is a Lean 4 formalization of finite-dimensional **quantum-channel
theory** (following Wolf's *Quantum Channels & Operations*), **quantum
Wielandt theory**, and the **spectral / quantum Perron-Frobenius (QPF)
theory** that channel irreducibility and primitivity rest on. Built on
Mathlib v4.36.0-rc1.

QICLean was extracted from TNLean (the tensor-network / matrix-product-state
library), which formalizes the fundamental theorem of matrix product states
on top of the channel and Wielandt theory that now lives here. TNLean
consumes QICLean as a Lake dependency, pinned to a released tag; it does not
vendor or duplicate this source. QICLean itself never imports TNLean —
channel and Wielandt theory is stated over finite Kraus families and words,
never over matrix-product-state vocabulary.

**The extraction-era `QICLean.MPS` compatibility layer is dissolved.** Its
channel-generic declarations now live under `QICLean.Kraus`; pure delegation
wrappers were deleted, and genuinely matrix-product-*state* vocabulary was
re-homed in TNLean. The root-level abbrev `MPSTensor d D` remains in
`QICLean/Kraus/Word.lean` because TNLean uses it as a synonym for a finite
Kraus family, but QICLean declares no API under `namespace MPSTensor`. Do not
add matrix-product-state vocabulary or new compatibility wrappers here.

## Build Commands and Mathlib Cache Policy

**Canonical cache rule:** never rebuild Mathlib from source in a fresh, cloned,
or cache-cleared worktree. After adding or updating a Mathlib dependency, fetch
its prebuilt artifacts **before** any `lake build` or local Lean check:

```bash
# Fetch pre-built Mathlib artifacts after a Mathlib/toolchain/dependency update.
# Do this before `lake build` or `lake env lean`; otherwise Mathlib can rebuild
# from source and take hours.
lake exe cache get

# Only after the cache fetch succeeds:
lake build
lake env lean QICLean/Path/To/File.lean
```
# Check for sorrys/axioms in changed files
rg -n "sorry|axiom" QICLean/Path/To/File.lean || true

# Blueprint validation (requires leanblueprint; run after lake build succeeds)
cd blueprint && leanblueprint checkdecls

# Blueprint web/PDF generation
cd blueprint && leanblueprint web
cd blueprint && leanblueprint pdf
```

QICLean's Mathlib pin moves in **lockstep** with TNLean's: QICLean upgrades
first, tags a release, and only then does TNLean copy the new
`lean-toolchain` byte-for-byte and bump its `QICLean` and `mathlib`
lake-manifest revisions in the same PR. See
[`docs/UPGRADE_RUNBOOK.md`](docs/UPGRADE_RUNBOOK.md) for the full procedure
and the invariants a CI guard checks on both sides.

## Lean Toolchain & Dependencies

- **Lean**: v4.36.0-rc1 (pinned in `lean-toolchain`; TNLean follows the released
  upgrade according to `docs/UPGRADE_RUNBOOK.md`)
- **Mathlib**: v4.36.0-rc1
- **checkdecls**: Blueprint declaration checker (PatrickMassot/checkdecls)
- **Gametheory**: Custom Brouwer fixed-point theorem library (LionSR/Brouwer) — moved here from
  TNLean, since the quantum Perron-Frobenius existence argument is the only consumer

### Lean Options (lakefile.toml)

- `relaxedAutoImplicit = false` — strict implicit arguments, no auto-implicit
- `pp.unicode.fun = true` — pretty-prints `fun a ↦ b`
- `maxSynthPendingDepth = 3` — typeclass synthesis depth limit

## Architecture

The source lives in `QICLean/` and is organized into layers checked by
`scripts/check_import_layers.py`: the single-system layers of
`docs/library_layers.md` form a chain below the many-body and circuit layers of
`docs/import_structure.md` (`QICLean.lean` is generated).

| Layer | Modules | Content |
|-------|---------|---------|
| **Algebra** | `Algebra/` | Exact algebra of matrices: entries, reindexing, rank, Kronecker products, partial traces, polynomials, words, star subalgebras, Skolem–Noether; no norms (layers and subdirectories: `docs/library_layers.md`) |
| **Analysis** | `Analysis/` | Norms, the Loewner order, functional calculus, exponentials, convexity, majorization, scalar real analysis, fixed-point theorems |
| **Spectral** | `Spectral/` | The spectrum of one matrix: eigenvalues, gaps above a kernel, spectral projections, filters and truncations, low-energy subspaces, Jordan forms |
| **Channel** | `Channel/` | Linear maps on matrix algebras: positive and CP maps, Kraus representations of maps (`Channel/KrausMap`), Choi, dilations, Kadison–Schwarz, fixed points, peripheral spectrum, GKSL semigroups (Wolf Ch. 2–7) |
| **Kraus** | `Kraus/` | Finite Kraus families as families: words, word spans, transfer maps, blocking, injectivity, primitive fixed points, mixed transfer maps, the quantum Wielandt inequality |
| **Entropy, Probability, Representation** | `Entropy/`, `Probability/`, `Representation/` | Entropies and information of one, two or three systems; measures and random matrices; group actions on tensor powers and Schur–Weyl duality |
| **Gates** | `Circuit/Gate/` | Unitaries on an arbitrary finite basis, with no sites: two-level and Givens words, controlled elements of a ring, the dilation of a partial isometry, exact amplification. Imports matrix modules only; nothing here mentions sites, layers, depth or supported operators (plan: `docs/many_body_circuit_architecture.md` in TNLean) |
| **Sites** | `ManyBody/Sites/` | Systems of sites with finite basis types `X : V → Type*`: configurations and cuts along a region, the terms of a family of supports crossing a cut, the `*`-subalgebra `supportedOperators X D`, the placement `place D K = K ⊗ 1`, the product-span description, the region expectation `regionExpectation D` (the normalized partial trace onto a region), its localization error through on-site commutators, regional pure states and their entropy, disjoint-region placement, operators on one of two systems of sites `A ⊕ B` and the two replicas `V ⊕ V` (their exchange on a region, the pairing with the alphabet `α × α` and the support transfer), covariance under site and basis relabelling, sums over a partition of the sites into blocks, and the lattice geometry of the models (`Sites/Lattice`: chain intervals, finite domains of `ℤ` and `ℤ × ℤ`, oriented edges `Edge G`, the square lattice, and their supports of bounded range). Imports the single-system layers up to `Entropy` only; nothing here mentions circuits, layers, depth, Hamiltonians or Kraus families (plan: `docs/many_body_circuit_architecture.md` in TNLean) |
| **Dynamics** | `ManyBody/Dynamics/` | Interactions `Interaction X T` (terms indexed by any type, each in `supportedOperators X (T i)`; Hermiticity and norm bounds are hypotheses) and their Hamiltonian `Φ.hamiltonian`, the one spelling of the sum of the terms; two interactions side by side `Φ.sum Ψ` on `A ⊕ B` (for `Φ` beside itself, the doubled Hamiltonian of two replicas); the Heisenberg picture `heisenbergEvolution` (the evolution itself is `Matrix.hermitianUnitaryPath`); the commutator recursion, exact locality on interaction-closed regions, the Lieb–Robinson bounds in graph distance, graph balls and localization onto them, the growth of graph balls and connected sets under a degree bound, the graph of a metric interaction range; imaginary-time conjugation by sums of positive contractions of bounded support and degree; relative evolutions projected onto a region, their products over disjoint regions, and supported Gaussian averages. Imports Sites and the matrix layers only; nothing here mentions ground states, gaps, circuits or layers (plan: `docs/many_body_circuit_architecture.md` in TNLean) |
| **Hamiltonians** | `ManyBody/Hamiltonian/` | Spectral notions of a Hamiltonian, over any `Matrix n n ℂ`: the ground space `groundSpace H E₀` and the gap predicate `IsGapped H E₀ Δ` (a nonzero ground space and every other eigenvalue at least `E₀ + Δ`), with the operator form of a gapped unique ground state as a theorem; the factorization of a gapped unique ground vector of a Kronecker sum or of a sum of single-site terms; common ground vectors on disjoint regions and the hard truncation of a region; frustration-free interactions `Φ.IsFrustrationFree` (one nonzero vector minimizing every term), with the ground space of the Hamiltonian as the intersection of the ground spaces of the terms and additivity of the least eigenvalue; the Gaussian-filtered terms `gaussianFilteredTerm` of a gapped Hamiltonian, their locality for an interaction, and Hastings' truncated filters on graphs and finite metric spaces; the Hermitian parts `Φ.hermitianPart` of the terms of an interaction; the lattice models as `Interaction` types (`ChainInteraction`, `DomainInteraction`, `PlaneInteraction`, `RectangleInteraction`, `SquareInteraction`), with Hermiticity and norm bounds as hypotheses. Imports Sites, Dynamics and the matrix layers only; nothing here mentions circuits or layers (plan: `docs/many_body_circuit_architecture.md` in TNLean) |
| **Circuits** | `Circuit/Geometry/`, `Circuit/Core/` | Geometries of cells with costs; gate families with interpretations (`KrausGate` the plain one); `Layer` (gates on disjoint cells, Kraus families at the other sites, basis types may change) and `inductive Circuit` (`done`, `step L next` with `next` depending on the outcome); their Kraus family, map and Heisenberg picture; adaptive composition `append`/`comp`; depth, gate count and participation as one cost `total`; local properties `Forall ev P`; trace preservation and the backward light cone, proved once; gates from matrices on a local basis, operations at one site controlled by a configuration (`ctrlOp`), and registers of qudits with their gate set (`Core/Qudit`). The finite Kraus family `KrausFamily` itself lives in `Channel/KrausMap/Family`. Imports Sites, channels and matrix modules; nothing here mentions a tensor network or a specific model (plan: `docs/many_body_circuit_architecture.md` in TNLean, steps 3C) |
| **Algorithms** | `Circuit/Algorithm/` | Specific circuits on their own sites, written in the circuit core and proved to compute their matrices, on the qudit registers of `Circuit/Core/Qudit` (the base-`d` encoding, the Fourier matrix, the gates `hadamard`, `phaseShift`, `controlled` and the swap `Matrix.swapMatrix 2` on the geometry of sites and pairs), which protocols use as well: the quantum Fourier transform of Nielsen–Chuang Fig. 5.1 from one gate table `qftGate`, proved once for every admissible order of the gates (`IsGateOrder`, `prod_gateOp_eq_dft`), with the textbook circuit (`kraus_qft`, gate count `n(n+1)/2 + n/2`) and its scheduling in `2n` layers of disjoint gates (`kraus_qftPar`, `depth_qftPar_le`, `gateCount_qftPar`). Imports the circuit core, Gates, Sites, channels and matrix modules; nothing in Core, Gate or Geometry imports it |

TNLean's tensor-network layers (`MPS/`, `PEPS/`, `PiAlgebra/`, `QCA/`) are
**downstream** of this library, never upstream. TNLean consumes the generic
`Kraus.mapLM` / `IsIrreducibleMap` APIs directly; do not add a channel-side
dependency on any matrix-product-state notion or recreate compatibility
wrappers for downstream notation.

### Key Types and Definitions

- `Kraus.map` / `Kraus.mapLM` — the CP map of a finite Kraus family, and its linear-map form
- `Kraus.adjointMap`, `Kraus.IsUnital`, `Kraus.IsTP` — the adjoint family and unital/trace-preserving predicates
- `Choi` — the Choi-Jamiolkowski matrix of a linear map
- `IsIrreducibleMap`, `IsPrimitive` — channel-level irreducibility and primitivity (Wolf Ch. 6)
- `channelPeriod`, `peripheralEigenvalues` — the peripheral spectrum of a channel
- `evalWord` — product of Kraus operators along a word `w : List (Fin d)`
- `IsInjective` — the Kraus family spans the full matrix algebra
- `IsNormal` — the quantum Wielandt normality predicate
- `cumulativeSpan` — span of all products of Kraus operators of length `<= n`

## Blueprint

`blueprint/` holds the reader-facing mathematical account, extracted from
TNLean's blueprint (see `docs/extraction/interface_edges.md` for the
severed cross-boundary edges left by that extraction). `blueprint/src/content.tex`
arranges the chapters in eight parts, ordered by dependency as far as
possible; the first three parts follow M. Wolf's *Quantum Channels &
Operations: A Guided Tour*, Chapters 1--7. The comment at the top of that file
lists every part and chapter. See `blueprint/README.md` for layout and build commands.

## Conventions & Style Guides

Shared conventions (Mathlib style, naming, documentation, PR review, proof
integrity, prose style) live in the `lean-conventions` skill of
texra-ai/texra-lean-skills, auto-installed via `.claude/settings.json` —
consult the skill, and `docs/project_conventions.md` for QICLean-local
addenda. Repo-specific conventions live in `docs/`; read the relevant file
before working in that area:

| File | Covers |
|------|--------|
| `lean-conventions` skill | Mathlib style, naming, documentation, PR review, proof integrity, prose style (canonical; installed) |
| [`docs/project_conventions.md`](docs/project_conventions.md) | QICLean-local addenda to the shared conventions |
| [`docs/blueprint_style_guide.md`](docs/blueprint_style_guide.md) | LaTeX conventions, `\lean{}`/`\leanok` tags, notation table, `\uses` rules, blueprint build commands |
| [`docs/UPGRADE_RUNBOOK.md`](docs/UPGRADE_RUNBOOK.md) | The two-repo Mathlib upgrade procedure and lockstep invariants with TNLean |
| [`docs/implementation/`](docs/implementation/) | Issue-linked integration and acceptance plans; retain assumptions and open work until the linked issue closes, then remove the plan after moving any lasting guidance to the relevant documentation |

The remaining TNLean convention docs (`CONTRIBUTING.md`, `glossary.md`,
`pr_review_management.md`, `ci-automation.md`, `lake_build_cache.md`,
`tactic_development.md`, `tactic_patterns.md`) were not carried into this
extraction; port them individually if QICLean develops a need for the
process they describe.

### Quick Reference (from the docs above)

- **PR titles**: `type(scope): description` -- types: `feat`, `fix`, `refactor`,
  `doc`, `style`, `ci`, `chore`; scope is shortened module path without
  `QICLean/` prefix
- **Issue titles**: plain mathematical titles, not `type(scope): ...`; use
  `Tracking: <area>` for trackers and keep titles bracket-free
- **Naming**: Definitions `camelCase`, predicates `IsPrefix`, theorems `snake_case`, files `CamelCase.lean`
- **Proof integrity blockers**: `sorry`, `admit`, `native_decide`, `unsafeCast`, `axiom`, circular reasoning
- **Blueprint prose**: Pure mathematics only — no Lean identifiers in text, no software jargon (see banned terms list in blueprint style guide)
- **Paper references**: Cite theorem numbers in docstrings (e.g., "Wolf Thm 6.3", "arXiv:1606.00608 Appendix A")
- **Adapted code**: Apache-2.0 code adapted from another repository carries a source notice in its module docstring or header naming the upstream file, the commit, and the changes; no separate attribution files are kept
- **Mathematical renames**: When renaming a declaration whose old name encodes misleading terminology (banned vocabulary in the lean-conventions prose_style reference, §2), skip the `@[deprecated] alias` and state the reason in the PR body (see `docs/CONTRIBUTING.md` §Mathematical-language renames).

## Workflow

### Mathlib Scouting

When writing new proofs or closing sorrys, scout Mathlib first:
- Use `exact?`, `apply?`, `rw?`, `simp?` tactics
- Grep Mathlib source: `.lake/packages/mathlib/Mathlib/` for related definitions/theorems
- Reuse Mathlib lemmas rather than reproving from scratch
- Not needed for cosmetic fixes, docstrings, imports, or renaming

### Tactic Self-Improvement Loop

Proof text must grow sublinearly with mathematical content: a tactic pattern
paid for three times gets abstracted, not copied a fourth time. The full
process is in `docs/tactic_development.md`; the pattern ledger is
`docs/tactic_patterns.md`. In every proof-writing session:

1. **Consult** the ledger's promoted section first and use existing custom
   tactics/simp sets where they apply — hand-writing a pattern that has a
   promoted tactic is a review-blocking style issue.
2. **Detect** repetition while writing, and in proof-heavy PRs run:

   ```bash
   python3 scripts/tactic_pattern_scan.py
   ```

3. **Record** noticed repetition as a candidate entry in the ledger — in the
   same PR; recording is cheap and needs no design decision.
4. **Promote** when a pattern hits ≥ 3 occurrences across ≥ 2 files (rule of
   three): prefer a lemma, then a simp set, then `@[grind]` annotations +
   `grind` for goal-closing patterns, then a macro, then an elab tactic
   (weakest mechanism that removes the duplication). Refactor the known call
   sites and update the ledger entry.

### Blueprint Updates

When adding or completing (removing sorry from) theorems/lemmas:
1. Update the corresponding entry in `blueprint/src/chapter/*.tex`
2. Add `\lean{DeclarationName}` and `\leanok` tags for new results
3. Add `\leanok` to `\begin{proof}` for newly proven results
4. Validate with `lake build` then `leanblueprint checkdecls`

### General Rules

- Prefer minimal diffs
- Do not leave unrelated new sorrys
- Before changing theorem statements, first try to complete the proof using existing lemmas
- If a mathematical result looks wrong or suspiciously general, check the LaTeX sources in
  `Notes/` for the original theorems (QICLean's copy of Wolf's lecture notes; see
  `docs/paper-gaps/README.md`)

### Faithfulness rule

**A theorem is "formalized" only when its Lean signature has no hypothesis
absent from the cited source's statement.** Adding hypotheses — even
mathematically natural ones — produces a *different* theorem and must
not be marked `\leanok` against the source's blueprint label.

This applies to every formalized result, not only those undergoing active
paper-realignment. The check is on hypotheses, not just conclusions:

- A Lean theorem whose conclusion matches the source but whose hypotheses
  are stricter than the source's is **not** the formalization of the source
  theorem. It is a different theorem (a corollary or specialization).
- The blueprint label citing the source must point to a Lean statement
  with the source's hypothesis set, not to a stronger-hypothesis variant.
- If the only available Lean theorem has extra hypotheses, the blueprint
  must either: (a) drop the `\leanok` and `\lean{...}` tags from the
  source-labelled entry, or (b) state the source's theorem as a
  separate blueprint entry with `\leanok` only after a faithful Lean
  version exists.

Scope-restricted theorems may be marked `\leanok` only against a blueprint
statement that explicitly states the restriction. Such an entry must not be
presented as the source theorem itself. The unrestricted source theorem remains
unformalized until a Lean statement with the source's hypothesis set exists.

A paper-gap note in `docs/paper-gaps/` is required whenever a
stricter-hypothesis Lean version is the *only* available formalization of
a source theorem. The note must identify the missing hypothesis and the
elimination plan (formalize the source-faithful version, derive the
stricter version inside a particular argument, etc.).

### Paper-realignment mode

When the formalization has drifted from the cited source and the work is
**realigning the Lean development to the paper** (replacing wrong hypotheses,
removing divergent structures, restating theorems to match the source), the
default `sorry`/`axiom` blockers from the lean-conventions proof-integrity rules are temporarily
relaxed. The priority is **getting the statements right**; proofs are
restored after.

#### Source-citation requirement

In paper-realignment mode every restated definition, hypothesis field, or
theorem **must carry a docstring referencing the source by paper label or line
range**. The minimum acceptable forms:

- `arXiv:1606.00608, eq:II_CF1` — equation/theorem label
- `arXiv:1606.00608, lines 1170–1192` — line range in the local source PDF/tex
- `CPSV16, Lemma Lem1` — paper short name plus internal label
- `Wolf §6.2` — published section reference

For Lean fields and theorems whose mathematical content is being aligned to a
specific paper passage, the docstring must say *which* passage. Inline
identifiers without a source reference are unreviewable in this mode: a
reviewer cannot tell whether the field/theorem is faithful or invented.

This rule applies whether or not the proof is `sorry` — the *statement* is
the load-bearing artifact during realignment.

#### Marking unfaithful theorems

A theorem or lemma is **unfaithful** when its proof relies on a hypothesis or
intermediate lemma that is known to deviate from the cited source — typically
because the hypothesis was smuggled into the formalization, the proof
shortcuts a load-bearing source step, or the result is restated more weakly
than the paper would prove. Unfaithful theorems must carry a docstring
marker so a future reader (or a follow-up PR) can locate them.

The marker is a docstring section starting with `**Unfaithful:**` that names
the load-bearing deviation, cites the paper-gap note documenting it, and
sketches the elimination plan. Minimum form:

```
**Unfaithful:** This proof currently relies on `<hypothesis or lemma>`,
which deviates from `<paper, label or line range>`. Documented in
`docs/paper-gaps/<note>.tex`. Elimination: replace by `<faithful
substitute>`; tracked in `<issue or PR>`.
```

The marker propagates to dependent theorems: any theorem whose proof
transitively calls an unfaithful one is itself unfaithful and must carry its
own marker. The marker is removed only when every transitively-cited
dependency is faithful.

Reviewers should not approve a paper-realignment PR that introduces an
unfaithful theorem without the marker. The marker makes the deviation
auditable and keeps the elimination plan visible.

#### Locally-fixable deviations

Not every paper deviation rises to **Unfaithful**. When the cited source
contains a small typo, a locally-fixable gap (a missing or off-by-one
constant, a clarification needed at one step), or a scope restriction that
the paper proves more generally but the local result handles only a
sub-case, the formalization may proceed without the full **Unfaithful**
ceremony. These cases must still:

- Cite a paper-gap document (under `docs/paper-gaps/`) that records the
  deviation in mathematical terms; if no note exists, write a short one
  before merging.
- Use a lighter-weight in-source marker. The recommended forms are
  `**Scope restriction (...):**` for sub-case proofs, or
  `**Local fix (...):**` for typo/constant adjustments. Both forms must
  reference the paper-gap document by file path.
- Be inline-readable: the marker should let a reader recognize the
  deviation without leaving the file.

The **Unfaithful** marker is reserved for deviations that would be
mathematically wrong without follow-up work (the proof is unprovable, or
the statement smuggles an unwarranted hypothesis). The lighter markers
are for deviations that are mathematically correct as stated, just
narrower or differently phrased than the source.

A paper-realignment PR may:

- Delete fields, hypotheses, or whole theorems that are documented as
  divergent from the cited source (with the divergence recorded in
  `docs/paper-gaps/`).
- Leave `sorry` in proof bodies whose old proof depended on the deleted
  data, when the paper-faithful replacement is the next step.
- Cascade signature changes through downstream consumers, also using
  `sorry` if necessary, rather than reverting to keep the build proof-clean.

A paper-realignment PR must:

- Cite the relevant `docs/paper-gaps/*.tex` note documenting the divergence
  in the PR description.
- Identify, in the PR description, every `sorry` introduced and the
  paper-faithful theorem that will discharge it.
- Be scoped tightly — no unrelated refactors or feature additions.
- Be followed by tracked implementation issues for the missing
  paper-faithful proofs.

In paper-realignment mode the standard "do not add sorry" rule is the
*wrong* heuristic: keeping a divergent proof intact to avoid `sorry`
preserves a result the source does not assert. Reviewers should evaluate
paper-realignment PRs against the paper-gap note and the planned
follow-up, not against the temporary `sorry` count.

### Downstream-compatibility rule

TNLean consumes this library as a Lake dependency pinned to a released tag,
not as a vendored copy. **Renaming, removing, or changing the signature of
any declaration that TNLean imports requires a coordinated TNLean tag-bump
PR** landed together with (or immediately after) the QICLean change: TNLean
must not be left pointing at a tag whose public surface it can no longer
build against. When a declaration used across the boundary must change,
either keep a `@[deprecated] alias` for one release cycle, or open the
TNLean-side PR in the same batch and merge them together. Before making a
breaking change here, check TNLean's import surface of this library (grep
`import QICLean` and the relevant consuming declarations on the TNLean side)
for consumers.

## Lean proof automation ledger

| Name | Kind | Use when | Defined in |
|---|---|---|---|
| `Kraus.map_compressed_fixedPoint` | helper theorem | Preserving a supported fixed point under finite-Kraus compression along an isometry | `QICLean/Channel/KrausMap/KrausCornerCompression.lean` |
| `Matrix.isSimpleModule_pi` | helper theorem | Using simplicity of the defining module of a full matrix algebra over a field | `QICLean/Algebra/MatrixAlgebra/MatrixAlgHomCentralizer.lean` |
| `IsSimpleRing.nonempty_linearEquiv_of_isSimpleModule` | helper theorem | Identifying two simple modules over a simple Artinian ring, instead of rebuilding the ideal/isotypic comparison | `QICLean/Algebra/MatrixAlgebra/MatrixAlgHomCentralizer.lean` |
| `Matrix.IsHermitian.apply_of_map_conjTranspose` | helper theorem | Showing a map that commutes with `ᴴ` (placement, region expectation, local lift) sends Hermitian matrices to Hermitian matrices, instead of `rw [IsHermitian, ← f_conjTranspose, hA.eq]` | `QICLean/Spectral/Eigenvalue/HermitianExtremalEigenvalues.lean` |
| `ManyBody.Interaction.norm_exp_conjugation_shift_le_two`, `ManyBody.Interaction.norm_exp_conjugation_shift_sum_le`, `Matrix.norm_exp_conjugation_le_two_of_growth` | helper theorems | Bounding `‖e^{t(H−z)} O e^{−t(H−z)}‖ ≤ 2‖O‖` (or `2|J|` for a sum of `J` terms) for a sum `H = ∑_{i ∈ s} Φ.term i` of positive contractions on at most `k` sites with every site in at most `g` terms and `2gkt ≤ 1`, instead of a new commutator count; the last lemma turns any factorial growth `a^m m!` into the conjugation bound | `QICLean/ManyBody/Dynamics/BoundedDegreeImaginaryTime.lean`, `QICLean/Analysis/Exponential/ExpConjugation.lean` |
| `Matrix.norm_partially_clipped_truncation_low_le`, `Matrix.exists_weighted_low_restriction_of_conjugation_le` | helper theorems | Bounding a regional clipping error `‖(A_j − min(A_j, e_j + t))|_G‖` on the low spectral span `G` of a centered partially clipped sum plus `Y`, from commuting Hermitian regional operators and only a conjugation bound on `Y`, instead of rerunning the weighted Sylvester argument | `QICLean/Spectral/LowEnergy/WeightedLowRestriction.lean` |
