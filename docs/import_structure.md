# Import structure and architecture checks

QICLean implements the lower layers of the adopted
[TNLean many-body/circuit architecture](https://github.com/LionSR/TNLean/blob/7e8438a32f1f0435e3acec579a89656de1b3f07b/docs/many_body_circuit_architecture.md#layers),
tracked in [TNLean #10718](https://github.com/LionSR/TNLean/issues/10718).
This check implements [QICLean #1053](https://github.com/LionSR/QICLean/issues/1053),
steps 0.4 and 0.6. The source document, rather than the migration-era location
of a theorem, determines its intended layer.

## New layers

| Directory | May import, besides itself |
|---|---|
| `ManyBody/Sites` | matrix foundations, single-system channels |
| `ManyBody/Dynamics` | matrix foundations, channels, Sites |
| `ManyBody/Hamiltonian` | matrix foundations, channels, Sites, Dynamics |
| `ManyBody/PoissonWord` | matrix foundations, channels, Entropy, Probability, Sites, Dynamics, Hamiltonian |
| `Circuit/Gate` | matrix foundations |
| `Circuit` | matrix foundations, channels, Sites, Gates |
| `Circuit/Party` | matrix foundations, channels, Sites, Gates, Circuits |
| Gaussian laws and integrals in `Circuit/Party/Compression/SourceSampling` | the party-circuit layer and Probability, together with the layers allowed by party circuits |
| `Circuit/Algorithm` | matrix foundations, channels, Sites, Gates, Circuits |
| `Circuit/Model` | matrix foundations, channels, Sites, Gates, Circuits |
| `Circuit/Compile` | matrix foundations, channels, Sites, Gates, Circuits, Model |
| `Circuit/Protocol` | matrix foundations, channels, Sites, Gates, Circuits, Model, Compile |
| `Circuit/Simulation` | matrix foundations, channels, Sites, Gates, Circuits, Dynamics, Hamiltonians |

The source-sampling law, integrability, Gaussian error and approximation modules may import
Probability. The sample coordinates, Schmidt frames and endpoint operators belong to the
deterministic party-circuit layer. They can be used without importing measures or integrals.

`Circuit/Simulation` owns statements comparing circuit simulation with many-body
Hamiltonian evolution. This is a separate upper integration layer, as specified
by [QICLean #1062, “Where the planned modules go”](https://github.com/LionSR/QICLean/issues/1062):
“Product formulas, simulation error bounds, simulation by circuits” belong on the
circuit side, importing Hamiltonians and Dynamics. It implements the adopted TN
architecture's statement-based ownership rule; the sibling relationship between
circuit primitives and Hamiltonians remains unchanged. Only the specific
`Circuit/Simulation` prefix gains those imports. Core, ordinary Circuit,
Algorithm, Party, Model, Compile, Protocol, Sites, Dynamics and Hamiltonian
cannot import Simulation, either directly or through an aggregator. Simulation
cannot import Algorithm, Party, Model, Compile or Protocol. Low-level matrix
product-formula results stay in Analysis, and generic circuit construction stays
in Circuit. The integration layer introduces no
alternative interaction, support or evolution definitions. No debt exception is
added for this layer; regression tests enforce both allowed and forbidden edges.

Matrix foundations means `Algebra`, `Analysis`, `Spectral`; single-system
channels means `Channel`, `Kraus`. `Sites`, `Dynamics` and `Hamiltonian` may
also import `Entropy` (entropy of one or two systems). The single-system layers
below, and the many-body layers `ManyBody/Entropy`, `ManyBody/Subspace`,
`ManyBody/Replica` and `ManyBody/PoissonWord` that hold the regional modules moved out of them, are
described in `docs/library_layers.md`. Lower prerequisites remain available at
higher layers. Specific prefixes own modules before the enclosing `Circuit`
prefix does. Nothing below `Circuit/Model` (Core, Geometry, Gate, Party,
Algorithm) imports it; only `Circuit/Compile` and `Circuit/Protocol` do. Other
QICLean targets are rejected from these new layers. Imports of external
dependencies such as Mathlib are outside this local layer check. The
repository rule that QICLean never depends on TNLean still applies.

The check expands import-only aggregators recursively, including `QICLean.lean`.
Aggregators themselves have no declarations and do not contribute dependency
edges. This measures direct dependencies after aggregator expansion, not all
transitive dependencies of ordinary modules. Header whitespace, escaped and Unicode module names, comments, and import
modifiers are handled before determining the edges. String and character
literals cannot manufacture commands or hide imports; `module` headers are
recognized when expanding import-only aggregators. Lexical errors fail the check
with a module diagnostic instead of silently dropping that module.

Every module of a layer is now checked as an importer, including the
single-system layers of `docs/library_layers.md`.

## Recorded debt

`scripts/check_import_layers.py` recorded eight unordered mutual directory
pairs: Algebra/Channel, Analysis/Channel, Analysis/Entropy,
Analysis/Probability, Analysis/Representation, Channel/Entropy, Channel/Kraus,
and Entropy/Representation. The reorganization of `docs/library_layers.md`
removed all of them, and the record is empty. A pair has an edge in each
direction; longer cycles are caught by the layer table. Directory identity is the first path component,
except under `ManyBody` and `Circuit`, where it is the first two. The checker
prints witness imports for each new pair. The imported TNLean example-import
ratchet also starts empty: theory must not depend on worked-example directories.

`scripts/check_pass_through_declarations.py` records 79 lexical forwarding
candidates at QICLean main `dfd6b71656fbd67c501d3c8cd84259c629d15dce`. A candidate applies a single target to
all its explicit binders, in order, either directly, with `by exact`, or with
`by simpa using`. Unlike TNLean's scanner, the target can be unqualified or
have a different name. This makes the inventory broader than upstream's
same-name namespace aliases (15 here), without trying to prove semantic
redundancy. The script docstring specifies the grammar and exclusions.

The initial inventory includes five legacy compatibility proofs introduced by
PR #1075 before this checker landed: `Entropy.eq_of_forall_trace_mul_eq`,
`Entropy.inner_toEuclideanLin_eq_trace`, `Entropy.regionState_isHermitian`,
`Entropy.regionState_posSemidef`, and `Entropy.trace_regionState`. The first two
forward to `Matrix` results; the remaining three forward to `ManyBody` regional
state results. They preserve existing legacy statements while the implementations
move to the lower layers. These are recorded migration debt, not exceptions to
future enforcement; no new-layer forwarding debt is recorded. The regional
vocabulary unification (step 4.0 of the many-body plan) deleted the three
`ManyBody` forwarders, together with the forwarding `Entropy.IsSupportedOn` and
`Entropy.localLift`, leaving 74 recorded candidates.

These are review candidates, not a verdict that a one-line proof is redundant.
The scanner does not elaborate Lean or compare statement types. In particular,
zero-argument aliases, implicit/named argument forwarding, indented commands,
and more complex forwarding proofs need review. Private names are recorded by
their lexical namespace, not Lean's generated private name. Additional occurrences
of the same lexical name receive a module/occurrence suffix, so an existing
private alias cannot conceal another forwarding declaration.

Both records must match the source tree exactly. New entries fail; repaired or
removed entries must be deleted. With `--base-ref`, entries may only shrink
relative to the Git merge base. `--base-revision` compares against an exact
commit and is used in CI: a force-push must not resurrect debt removed at the
previous branch tip. The first introduction of a record is the sole
bootstrap exception. No module in the new layers has recorded import debt or
pass-through debt, and a regression test keeps that invariant explicit.

`scripts/check_small_lean_modules.py` keeps the number of small modules of
each directory under a ceiling. A module holds one coherent interface, and a
module of at most two public top-level declarations is merged into the module of
its object (`docs/library_layers.md`). The check counts, per directory of the
layer check (two path components below `ManyBody` and `Circuit`, one elsewhere),
the modules with at most two public top-level declarations, not counting
aggregators, import-only modules or `Archive`, and fails when a count rises above
its ceiling in `scripts/small_lean_module_ceilings.txt`. A directory that is not
listed has ceiling 0. The ceilings may only fall: after a change that merges
small modules, `--write` lowers them to the current counts and never raises one.
Compared with the merge base, a ceiling may rise only by the number of small
modules that Git records as moved into the directory, and the sum of the
ceilings may not rise; so a moved module carries its ceiling, and a new small
module cannot be admitted by recording it. `--list` prints the small modules of
each directory. The check is ported from TNLean.

## Running and maintaining the checks

```sh
PYTHONPATH=scripts python3 scripts/test_architecture_policies.py -v
PYTHONPATH=scripts python3 scripts/test_lean_file_policies.py -v
python3 scripts/check_import_layers.py --base-ref origin/main
python3 scripts/check_pass_through_declarations.py --base-ref origin/main
python3 scripts/check_small_lean_modules.py --base-ref origin/main
node --test scripts/test_issue_automation.cjs
python3 scripts/generate_import_aggregators.py --check
```

Use `--print-mutual-directories`, `--print-debt`, and `--print-record` to inspect
current findings. These commands print inventories; they do not update the
records. Do not regenerate a record to admit new debt. Stage new Lean files
before checking: like the upstream checker, the scan covers Git-tracked sources
outside `Archive`. Deleted working-tree files are omitted.

The PR CI module-policy job runs both tests and checks on Lean, checker, test,
workflow and policy-document changes. PRs use the event's exact base SHA. A
missing or malformed PR SHA and an unavailable commit fail rather than
silently disabling the comparison. The nightly run (`nightly.yml`) checks the
merged tree again, against the last commit of `main` that passed it. A manual
dispatch, and a nightly run with no such commit, still check the tree against
the records, with no historical comparison.

## Tracking parents

The issue automation queries each native parent's `repository.nameWithOwner`
and updates only parents in this repository, comparing names case-insensitively.
A remote parent (or one without repository identity) is logged and skipped,
because the workflow's `GITHUB_TOKEN` is repository-scoped. Its number must never
be interpreted as a QICLean issue number. Merged-PR progress on the local child
still occurs. Tests execute the actual inline workflow script with mocked API
calls for issue closed/reopened and PR opened/merged events; they never post
comments or mutate GitHub.

CI shell regression tests cover both checkers receiving the exact SHA, failure
before checking when a base is missing or unavailable, a zero-SHA initial push,
and dispatch without historical comparison. A divergent-history Git fixture
checks that an exact revision rejects restored debt that a merge base allows.
