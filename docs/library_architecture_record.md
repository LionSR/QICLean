# Architecture record of the single-system layers

Status: adopted 2026-11-26 (QICLean #1060, with #1172 and #1183). This record
maps the modules of `Algebra`, `Analysis`, `Spectral`, `Channel`, `Kraus`,
`Entropy`, `Probability` and `Representation` to the objects their statements
mention and to their imports, names what still sits above its objects, orders
the remaining cleanup into bounded batches, and records the decision on a
separate many-body library. The layers themselves, and the order inside each
layer, are fixed in `docs/library_layers.md`; the many-body and circuit layers
in `docs/import_structure.md`. The per-module classification made when the
layers were introduced is `docs/library_layers_inventory.md`; its counts are
historical and are kept apart from the counts below, which are read from the
import graph of this revision.

## How the counts were taken

A module is a Lean file of `QICLean/` outside `Archive` that is not a generated
import aggregator. An import is a line `import QICLean.…` of such a file, after
comments are removed. The counts of this record were taken on the tree of the
pull request that closes #1183, after its module moves; they change with every
later move, and the scripts below reproduce them.

- `scripts/check_import_layers.py` checks the layers, the pairs of directories
  that import each other, and the order inside each layer, and prints the
  recorded entries with `--print-debt` and `--print-sublayer-debt`.
- `scripts/generate_import_aggregators.py --check` checks the aggregators.

The historical counts of #1053 (the imports between directories before the
layers existed) and of `docs/library_layers_inventory.md` (the classification
of 2026-11-21) are not repeated here; where this record cites one, it says so.

## The objects of each layer

| Layer | Modules | Subdirectories | Largest directory (modules at one level) | Objects |
|---|---:|---:|---|---|
| `Algebra` | 202 | 16 | `Combinatorics` (37) | matrices over a ring, reindexing, rank, Kronecker products, polynomials, words, star subalgebras, the partial trace |
| `Analysis` | 355 | 28 | `Real` (39) | norms, the Loewner order, functional calculus, exponentials and logarithms, convexity, scalar real analysis |
| `Spectral` | 119 | 10 | `Eigenvalue` (32) | eigenvalues, gaps, spectral projections, filters and low-energy subspaces of one matrix |
| `Channel` | 356 | 45 | `Schwarz` (29) | linear maps between matrix algebras: positive, completely positive and Schwarz maps, Choi matrices, Kraus representations, transfer matrices, dilations, fixed points and peripheral spectra |
| `Kraus` | 58 | 11 | the top level (15) | a finite family of matrices: words, word spans, the transfer map of the family, blocking, injectivity, primitivity, Wielandt bounds |
| `Entropy` | 115 | 12 | `Conditional` (25) | von Neumann, relative, Rényi and Shannon entropy, mutual and conditional information, strong subadditivity, recovery |
| `Probability` | 60 | 8 | `PoissonWord` (19) | measures, Haar and Gaussian random matrices and subspaces, sampling, concentration |
| `Representation` | 94 | 11 | `SchurWeyl` (19) | permutation and unitary actions on tensor powers, Schur–Weyl duality, characters, Young diagrams, coherent states |

The directory table of `docs/library_layers.md` gives the objects of every
subdirectory. Above these layers sit `ManyBody` (388 modules) and `Circuit`
(198 modules). No directory holds more than forty modules at one level.

## Import dependencies

The eight single-system layers form a chain, and every import between two of
them points down the chain. The imports between layers, counted as import
lines, are:

| From | Algebra | Analysis | Spectral | Channel | Kraus | Entropy | Probability |
|---|---:|---:|---:|---:|---:|---:|---:|
| `Analysis` | 73 | | | | | | |
| `Spectral` | 8 | 93 | | | | | |
| `Channel` | 155 | 172 | 47 | | | | |
| `Kraus` | 17 | 3 | 12 | 50 | | | |
| `Entropy` | 23 | 53 | 8 | 37 | 0 | | |
| `Probability` | 4 | 33 | 4 | 1 | 0 | 1 | |
| `Representation` | 32 | 26 | 5 | 1 | 0 | 4 | 1 |

Above them, `ManyBody` imports `Analysis` (156 lines), `Representation` (75),
`Spectral` (73), `Algebra` (63), `Entropy` (48), `Channel` (28), `Probability`
(22) and `Kraus` (1); `Circuit` imports `Analysis` (33), `ManyBody` (31),
`Algebra` (22), `Channel` (14), `Probability` (4) and `Spectral` (4). No module
of the eight single-system layers imports `ManyBody` or `Circuit`, and no module
of `ManyBody` imports `Circuit`.

### Components that import each other

There are none, at any of the three levels the check sees.

- Between layers, the recorded violations (`DEBT`) are empty.
- Between directories, the recorded pairs that import each other
  (`MUTUAL_DIRECTORIES`) are empty. The base revision of the layers recorded
  eight pairs; `docs/library_layers.md`, "Directories that imported each other",
  says how each was removed.
- Inside a layer, the recorded imports against the order of its subdirectories
  (`SUBLAYER_DEBT`) are empty. There were 108 when the order was fixed; #1217
  repaired 83 of them, and #1183 the last 25 (`docs/library_layers.md`, "How the
  last imports against the order were repaired").

So the graph of directories is acyclic. Each of the three records may only
shrink, so a new cycle fails the check.

## Declarations that can still move down

The imports now point down, but a module can still sit above its objects when
one lemma of its proof needs a higher layer. The inventory of 2026-11-21 listed
155 modules in a layer other than that of their statements, and 200 modules that
hold declarations of two layers. Those lists predate #1217 and #1183, which moved
more than a hundred declarations and 79 modules, so they are an upper bound and
must be read again before a batch uses them. The check cannot see a module filed too
high; finding one needs a reading of its statements.

One measurable family remains.

- **Small modules.** 227 modules hold one or two public declarations: 152 in
  the single-system layers (46 in `Analysis`, 30 in `Algebra`, 24 in
  `Channel`, 20 in `Spectral`, 15 in `Entropy`, 8 in `Kraus`, 5 in
  `Representation`, 4 in `Probability`) and 75 in `ManyBody` and `Circuit`.
  Each is merged into the module of its object. #1172 counted 447 such modules,
  private declarations included, before 119 were merged; the count here excludes
  private declarations and import-only modules.

## Cleanup batches

Each batch is bounded, moves no statement, and is applied through
`scripts/library_layers_module_map.txt`, so that a dependent library follows the
moves by `scripts/apply_library_layers.py --downstream`. Before a batch starts,
its owner checks the open pull requests that touch the same directories; the
lanes moving many-body material into QICLean own `ManyBody` and `Circuit` while
they run.

1. **Small modules of the single-system layers**, one pull request per layer, at
   most about fifty merges each: `Analysis`, then `Algebra`, then
   `Channel`, `Spectral` and `Entropy`, then the rest. A layer is done when none
   of its modules holds one or two public declarations outside a definition
   that other modules extend.
2. **The tests follow their modules.** Dropped: the 411 files of `QICLeanTest`
   were deleted on 2026-11-27, and the repository keeps no Lean test fixtures
   (`docs/project_conventions.md`, "No test fixtures").
3. **The top level of `Kraus`.** Its 15 modules are words and word spans,
   blocking, the transfer map of a family, injectivity and primitivity; they go
   into subdirectories by these objects, with an order in
   `scripts/library_sublayers.json`.
4. **Modules filed above their objects.** The inventory lists are read again
   against this revision, and each confirmed module is split or moved, one layer
   per pull request.
5. **Small modules of `ManyBody` and `Circuit`**, after the many-body lanes have
   merged.

## A separate many-body library

**Decision: `ManyBody` and `Circuit` stay inside QICLean.** The decision is to be
taken again once the criteria below hold.

The dependency direction allows a split: the single-system layers import
neither `ManyBody` nor `Circuit`, `ManyBody` does not import `Circuit`, and the
layers check enforces all three. The smallest boundary that builds on its own is
`ManyBody` together with `Circuit` (586 modules) above the eight single-system
layers (1,359 modules). `ManyBody` uses all eight, `Representation`, `Analysis`
and `Spectral` most of all. `Circuit` uses `ManyBody/Sites` and the matrix and
channel layers.

A split would cost a second package. TNLean would pin two libraries, which have
to move to a new Mathlib together. Each would need its own build and cache in
CI, and every pin move would be a pair of pull requests. The boundary is also
not settled yet. The many-body lanes are still moving modules into `ManyBody`,
and this month's module map moves modules of `ManyBody/Sites` (product states
and placements). In TNLean, 367 of 5,420 Lean files import `ManyBody` or
`Circuit`, so every such move is also a change in TNLean.

The separation is reconsidered when all of the following hold:

1. the three records of `scripts/check_import_layers.py` have stayed empty, and
   no module of `ManyBody` or `Circuit` has moved down into a single-system
   layer, for two consecutive pin moves of TNLean;
2. the module map has had no entry for `ManyBody` or `Circuit` for two
   consecutive pin moves, so that consumers no longer follow moves;
3. batches 1, 2 and 5 above are done, so that the split does not move files
   twice;
4. a second consumer besides TNLean imports `ManyBody` or `Circuit` without
   importing tensor networks, which is the reason a separate package would serve.

If the criteria hold and the library is split, the package takes `ManyBody` and
`Circuit` with their tests and keeps the module names, so that the module map
needs no entry. Until then, nothing is named or created for it.
