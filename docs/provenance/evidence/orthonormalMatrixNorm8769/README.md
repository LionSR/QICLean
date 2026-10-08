# Operator norms in orthonormal coordinates

Source revision: `361713b3a0fc203724a720d34b980d4e12320035`.
Parent revision: `4be0ef429c5048cf1bf4f5b7afd5b9f7b9361ca0`.

`ContinuousLinearMap.norm_toMatrix_orthonormal` proves that the matrix of a
continuous linear map in arbitrary finite orthonormal input and output bases
has exactly the same Euclidean operator norm as the map. The scalar field may
be real or complex. The matrix may be rectangular, and either basis may be
empty. The proof identifies the represented map with the composition of the
original map and the two coordinate isometries, then uses invariance of the
operator norm under these compositions.

This is a general supporting identity for the exterior-contraction argument in
the polynomial-PEPS manuscript, not a formalization of the complete compression
theorem. Mathlib supplies the Euclidean matrix norm identification and both
isometric-composition identities. No upstream OpenAI Lean proof text is reused.
The original checked source has SHA256
`5a573d1fe0ad1a2cb8032ca839cafc434a5757445a800a6bef3f82783bb9182f`.
Only a provenance comment was added; its noncomment tokens are preserved.
The production source has SHA256
`73f1f0327f668cfef27ecfa77670b066e058c3ddf3a34b54d2635450a291db32`.

## Verification

The new module and the affected `QICLean.Analysis` and `QICLean` aggregators
compiled directly with the package options and warnings as errors. All three
checks succeeded without diagnostics, in 3.781, 28.816 and 8.407 seconds.
`build-commands.json` records the exact commands and source and output hashes.
These are direct Lean checks against existing pinned artifacts, not a Lake build
or a CI measurement. The isolated worktree has no `.lake` directory; predecessor
artifacts were accessed through read-only file links, without copying caches.

The importing axiom check reports only `propext`, `Classical.choice` and
`Quot.sound`. All 3,994 imported artifact hashes were checked again when the
source revision was pinned. The source snapshots and commands are retained here;
large imported-file manifests are compressed without changing their contents.

The canonical provenance checker validates the one new exact-source entry,
including its manuscript label and notice. A separate collision check covers all
488 QICLean provenance entries. This does not claim that the other 487 entries
were revalidated. The checker and schema are included unchanged under
`canonical/`; no unrecorded Git revision of the checker is needed.

From the repository root, the recorded checks can be inspected with:

```bash
python3 docs/provenance/evidence/orthonormalMatrixNorm8769/validate-evidence.py --root .
uv run --no-project --with jsonschema==4.26.0 python docs/provenance/evidence/orthonormalMatrixNorm8769/check-provenance.py --root . --upstream-root /path/to/openai-math
```

The second command requires the pinned manuscript revision in the supplied
checkout. Neither command compiles Lean. The verification scripts retain the
actual isolated compiler commands; recompilation requires the pinned toolchain
and matching dependency artifacts.

## Mathematical documentation

The blueprint states exactly the norm identity, including unequal dimensions
and empty bases, and its proof follows the two coordinate isometries. The
canonical formatter was checked for idempotence. Full source synchronization
passes for 3,660 blueprint reference entries. A direct check in the compiled root
environment finds every one of the 3,628 names in the full declaration list.
This is a compiled declaration-presence check, not Lake's `checkdecls` command.

The focused four-page PDF contains the title, contents, the complete mathematical
page and bibliography. The mathematical page was inspected visually, with no
overflow or undefined references. The web check passes on six pages with
38 typeset elements. These are focused renders, not a full-book build.

Two initial rendering setup failures are retained: the disposable copy first
lacked the Git metadata required by the web tool, and the QICLean browser script
did not accept the TNLean script's `--jobs` option. Initializing only the disposable
copy and using the QICLean script's actual arguments resolved them. The web tool
also replaces the declaration list with the focused document's list; the first
compiled check therefore covered one name. That check is retained separately.
The full source list was then restored and all 3,628 names were checked.

## Downstream uses

The recorded TNLean patch replaces the two existing coordinate-vector proofs in
`Word.norm_preparedMatrix_le_one` and `Word.norm_freeSourceMatrix_le_one`.
The separate `ExteriorSourceContraction.lean` reference already applies the new
identity in `Word.norm_physicalOutputMatrix_le_one`. These three applications
justify the shared result recorded in the proof-pattern ledger.

The consumer files under `consumers/` are references only. The TNLean patch has
not been applied, no TNLean dependency pin has changed, and no existing QICLean
publication branch has been modified. The downstream refactor belongs with the
later dependency update.

The unapplied consumer patch is gzip-compressed to retain its exact blank-line
context. Its decompressed hash is recorded in `consumer-references.json`.
