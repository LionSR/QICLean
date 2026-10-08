# Local evidence for physical-buffer overlap

This packet records the 42 original declarations in the partial-swap,
product-overlap purity, and physical-buffer assembly modules. The endpoint
constructs a Hermitian contraction on the original doubled buffer, with an
exact complex overlap equal to a real number at least `exp (-2 * b)`.
It does not formalize the subsequent spectral-filtering or polar-unitary steps.
The source checkpoint is `abd6b6a3285c00e023e9976cdc6235f6b4da676d`;
documentation is at `8a3db4d8bd2d15ec15be5746525c7ef7c9385b22`.
No Lean build was run while assembling this evidence.

## Recorded validation

[verification.json](verification.json) binds exact final source, test, and
raw-driver bytes to the retained commands, process exits, timings, and logs.
The strict commands disable both implicit-variable options, enable Mathlib
standard linters, and treat warnings as errors.

- Three production files passed strict elaboration.
- Three test files passed: 17 `example` consumers, one additional named
  isometry helper theorem, and 42 exact guarded axiom reports.
- Three byte-for-byte retained [raw drivers](drivers) passed and reported all
  42 declarations: 36 use the standard three axioms, two use only `Quot.sound`,
  and four use no axioms. There are no other reported axioms.
- The supporting [native log](logs/native-build.log) reports a successful
  3,171-job target build. It records neither the top-level invocation nor the
  overall runtime, process exit, or source digest; none is inferred.

The [nine-run package record](runs/buffer-package-strict-bb14.json) includes
one failed production run: a provenance-ID comment exceeded 100 characters.
Commit `abd6b6a` shortened only that comment line. The
[final strict rerun](runs/buffer-provenance-style-final.json) passed for the
final purity source. Noncomment code, tests, and raw drivers are unchanged;
the other two production hashes still match the nine-run record. Tests and
raw audits were not rerun after this comment-only edit. The final native log
follows the edit.

Raw logs preserve all 42 informational `hashCommand` diagnostics. Each
checked-in guard expects its exact axiom report and that informational
diagnostic; the guards do not disable the linter. The ledger's required
`build` evidence means the recorded source elaboration, not a full-root build.
The full test and run details are centralized in the verification index.

## Source and reuse

All 42 ledger IDs and downstream names are taken from the actual production
notices, including the shortened coordinate-normalization ID. The reference
is `02-information.tex`, lines 355–424, equations `eq:info-split-overlap` and
`eq:info-reset-overlap`, in the September 24, 2026 paper at pinned revision
[`adc7f124`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex#L355-L424).
No upstream OpenAI Lean declaration or proof text was copied. The existing
purification-splitting result from [QIC#558](https://github.com/LionSR/QICLean/pull/558)
is an unchanged dependency, not a newly authored proof or ledger entry.

## History and rendering

The [history](history) retains the seven earlier native failures or warning
runs, all logs referenced by the first strict-leaf record, and the failed
purity output from the nine-run package check. Their actual diagnostics are
preserved, including the early `sorry` warning and complex regression errors.
These are superseded evidence, not final failures. Missing metadata for
log-only runs is explicit in the index.

The normalized [render report](render/render-report.json) records focused
six-page PDF and static HTML checks, 42 changed declarations plus one reused
declaration, and 43 verified declaration links. The actual Tenkz sweep passed
for the compression picture with the original doubled-buffer boundary.
The report preserves artifact hashes and the visual review of PDF content
pages 3–5 and the generated web SVG. No binary is included. Complete-book
Tenkz integration and full-book validation remain pending; live browser,
MathJax, and responsive-layout checks were not performed.

## Normalization and checking

Every retained input has an original-to-normalized SHA256 mapping. Private
executor paths are replaced by role tokens; log line-end whitespace and
terminal blank lines are trimmed without dropping diagnostic lines. Embedded
digests keep their original meaning. Raw Lean drivers are retained exactly.
Tokenized recorded commands are historical descriptions; raw-driver replay
commands use the committed relative paths.

Run `python3 docs/provenance/evidence/8766-physical-buffer-overlap/check.py`
from the repository to recheck hashes, source/ledger/guard/raw coverage,
standard-axiom bounds, run references, source-revision bytes, dependency
preservation, and rendering source hashes. It performs no Lean execution.

This packet makes no full QIC root, import-aggregator, complete dependency/cache,
remote CI, publication, merge, release, or issue-completion claim. QIC
publication remains held. The earlier polar worktree is unchanged.
