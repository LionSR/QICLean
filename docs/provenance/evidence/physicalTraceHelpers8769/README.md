# Partial traces, physical blocks, and trace-norm integrability

Source revision: `92b6eea77da987d4d12236c3dd3fc06510cd98ac`.
Parent revision: `b2521d2a2843d824ce85a4d94bf4b60d322d6c6f`.

This contribution contains ten supporting results for the physical error
estimate in the polynomial-PEPS manuscript. Four results establish invariance
of reduced trace norms under orthonormal changes of coordinates, four reconstruct
an operator from its physical blocks and bound its trace norm, and two establish
integrability of finite matrix sums. These results do not assert the complete
compression theorem or the remaining application to its actual sampled circuit.

The coordinate-invariance statements permit arbitrary mixed outer products;
positivity is not assumed. Endpoint isometries need not be onto. The finite
matrix-sum integrability statement requires integrability of the pairwise
coefficient products, with square integrability as a sufficient condition.
It imposes no independence assumption on those coefficients.

The averaged block inequality uses the Bochner integral convention that the
integral of a nonintegrable function is zero. Its hypotheses establish
integrability of the individual block norms, but the statement does not claim
integrability of the full trace norm. Applications requiring that conclusion
use the separate integrability results. The mathematical chapter states this
distinction explicitly.

## Source preservation

The statements and proofs were extracted from independently checked TNLean
drafts. All noncomment tokens in the two physical-coordinate modules are
preserved. The two generic probability theorem blocks are also preserved;
TNLean-specific consumers are excluded. The probability module adds an explicit
import of `RectangularTraceNormAlgebra`, formerly provided transitively by the
TNLean draft. The original sources and their hashes are retained, and the
provenance replay verifies these token comparisons. No upstream OpenAI Lean
proof text was reused.

No predecessor worktree, dependency pin, or dependency build cache was changed.
The new worktree has no `.lake` directory. Existing dependencies were accessed
through read-only file links; all new compiled artifacts were written under
`/private/tmp/qic-physical-trace-helpers`.

## Verification

The three new modules, their two enclosing import modules, and the QICLean root
compiled directly with the package options and warnings as errors. All six
checks passed without diagnostics. Their elapsed times were respectively
5.340, 5.012, 15.661, 30.108, 4.679, and 10.562 seconds (71.362 seconds in total).
These are direct Lean checks against pinned dependency artifacts, not Lake
builds or CI timings. Exact commands, source hashes, artifact hashes, and
working directories appear in `build-commands.json`.

An audit through the imported QICLean root found only `propext`,
`Classical.choice`, and `Quot.sound` for all ten declarations. All 11,629
actually imported artifact hashes were rechecked unchanged at the source pin.
The complete blueprint declaration list was checked in the compiled root:
all 3,639 names were present. This is a direct Lean declaration-presence check,
not a local Lake `checkdecls` invocation.

The initial check of the probability module failed because the extracted
module lacked the direct algebra import mentioned above. Its exact source,
diagnostics, and command are preserved in `initial-checks/`. The import was
added before the final six successful checks; theorem tokens did not change.

The unchanged canonical provenance checker and schema are included under
`canonical/`. The replay validates the ten new exact-source entries and their
manuscript labels. Its collision check covers all 499 QIC entries; it does not
revalidate the other 489 entries.

From the repository root:

```bash
python3 docs/provenance/evidence/physicalTraceHelpers8769/validate-evidence.py --root .
uv run --no-project --with jsonschema==4.26.0 python docs/provenance/evidence/physicalTraceHelpers8769/check-provenance.py --root . --upstream-root /path/to/openai-math
```

Neither command compiles Lean. The second requires the pinned manuscript
revision in the supplied checkout. Recompilation requires the recorded Lean
toolchain, options, and matching dependency artifacts. The verification scripts
retain the absolute paths used for these local checks; a new machine must
provide its own corresponding read-only dependency paths.

## Mathematical documentation

Full source synchronization passes for 3,671 blueprint reference entries and
9,527 Lean declarations. All ten new names occur exactly once in the new
chapter. The explicit dependency graph contains 1,769 nodes and 3,344 edges,
with no duplicate labels or cycles. The chapter formatter is idempotent.

The focused six-page PDF and web document were generated from a disposable
copy. All 958 recorded original source files match the committed revision.
The mathematical pages 3, 4, and 5 were inspected visually, including the final
lines of the integrability proof. The final TeX log has no warnings or
overfull boxes. The focused browser check passes on six pages containing
171 typeset elements. This does not claim a full-book render. After the web
generator produced a focused declaration list, the full source list was
restored before the compiled declaration-presence check.

The render inputs and complete TeX log are retained in compressed form without
altering their bytes. The manifest covers every evidence file other than itself;
the provenance shard is stored separately in `openai-math.d`.
