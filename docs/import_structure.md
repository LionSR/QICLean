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
| `Circuit/Gate` | matrix foundations |
| `Circuit` | matrix foundations, channels, Sites, Gates |
| `Circuit/Party` | matrix foundations, channels, Sites, Gates, Circuits |

Matrix foundations means `Algebra`, `Analysis`, `Topology`; single-system
channels means `Channel`, `Kraus`. Lower prerequisites remain available at
higher layers. Specific prefixes own modules before the enclosing `Circuit`
prefix does. Other QICLean targets are rejected from these new layers. Imports
of external dependencies such as Mathlib are outside this local layer check.
The repository rule that QICLean never depends on TNLean still applies.

The check expands import-only aggregators recursively, including `QICLean.lean`.
Aggregators themselves have no declarations and do not contribute dependency
edges. This measures direct dependencies after aggregator expansion, not all
transitive dependencies of ordinary modules. Header whitespace, escaped and Unicode module names, comments, and import
modifiers are handled before determining the edges. String and character
literals cannot manufacture commands or hide imports; `module` headers are
recognized when expanding import-only aggregators. Lexical errors fail the check
with a module diagnostic instead of silently dropping that module.

Existing directories remain unconstrained as importers by this new layer table:
in particular, old entropy consumers can import Sites while their definitions
move down. Reordering all existing single-system dependencies would impose the
follow-on F3 refactor, which is outside this change.

## Recorded debt

`scripts/check_import_layers.py` records eight unordered mutual directory pairs:
Algebra/Channel, Analysis/Channel, Analysis/Entropy, Analysis/Probability,
Analysis/Representation, Channel/Entropy, Channel/Kraus, and
Entropy/Representation. A pair has an edge in each direction; longer cycles
are not covered by this ratchet. Directory identity is the first path component,
except under `ManyBody` and `Circuit`, where it is the first two. The checker
prints witness imports for each new pair. The imported TNLean example-import
ratchet also starts empty: theory must not depend on worked-example directories.

`scripts/check_pass_through_declarations.py` records 74 lexical forwarding
candidates at QICLean main `e9cc1cc6`. A candidate applies a single target to
all its explicit binders, in order, either directly, with `by exact`, or with
`by simpa using`. Unlike TNLean's scanner, the target can be unqualified or
have a different name. This makes the inventory broader than upstream's
same-name namespace aliases (15 here), without trying to prove semantic
redundancy. The script docstring specifies the grammar and exclusions.

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

## Running and maintaining the checks

```sh
PYTHONPATH=scripts python3 scripts/test_architecture_policies.py -v
python3 scripts/check_import_layers.py --base-ref origin/main
python3 scripts/check_pass_through_declarations.py --base-ref origin/main
node --test scripts/test_issue_automation.cjs
python3 scripts/generate_import_aggregators.py --check
```

Use `--print-mutual-directories`, `--print-debt`, and `--print-record` to inspect
current findings. These commands print inventories; they do not update the
records. Do not regenerate a record to admit new debt. Stage new Lean files
before checking: like the upstream checker, the scan covers Git-tracked sources
outside `Archive`. Deleted working-tree files are omitted.

The PR CI module-policy job runs both tests and checks on Lean, checker, test,
workflow and policy-document changes. PRs use the event's exact base SHA; pushes use
the exact previous SHA. Missing or malformed PR/push SHAs and unavailable
nonzero commits fail rather than silently disabling the comparison. Manual dispatch and an initial push without a predecessor still
check the tree against the records, with no historical comparison.

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
