# Positive-gap uniqueness evidence

The three public results derive the projection identity for an arbitrary ground
vector, identify the ground eigenspace with a unit ground vector's span, and
prove that its dimension is one. The projection identity does not require the
reference vector to be an eigenvector. Every result requires a strictly
positive gap bound; none identifies that bound with the actual spectral gap.

The public recovery checkpoint is
[`5a846a09`](https://github.com/LionSR/QICLean/commit/5a846a09030085ad1546d50163caad111f7748f4),
on `codex/physical-buffer-gap-checkpoint-8766`. Each of the production, test,
and raw-driver files was independently read at that commit through the GitHub
connector. Its Git blob ID matches the checked local file. This establishes
file identity, without claiming that public CI passed.

## Validation and exact revisions

[verification.json](verification.json) binds final file hashes, actual run
revisions, command arguments, timings, exits, retained logs, and the public
checkpoint blobs.

- Native target builds passed and reported 2,711 jobs.
- Production and the eight consumer examples passed strict checks at
  `9b52983ef89dbf88e8b833c198953e3980dcbb5d`. The same test file includes three
  exact axiom guards. These source bytes remain identical at the public
  checkpoint and the later local `5bbc0fd` revision.
- The separate raw driver passed strict checking at
  `5bbc0fd9bd3e5ddca0016b5a684cd5fa1ac56f63`. All three reports contain exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- The strict commands disable both implicit-variable options, enable Mathlib
  standard linters, and treat warnings as errors. The three informational
  hash-command diagnostics are retained; no linter is disabled in the files.

The eight examples cover the weak projection contract, the zero vector,
non-real normalized phase, an unnormalized complex multiple, a negative
ground energy, eigenspace equality, dimension one, and the generic physical
partial-swap composition. An explicit two-dimensional zero-Hamiltonian
counterexample verifies that the nonnegative-gap endpoint permits an
independent ground vector.

The ledger's verification revision names the public files. Its successful
native and raw commands ran at the actual local `5bbc0fd` revision. Strict
production/tests ran earlier at `9b52983`; their hashes prove equivalence.
No run is relabeled as having executed at the public commit.

## Retained failed attempts

All five command-record groups and their thirteen logs remain in `runs/` and
`logs/`, including four failed invocations:

1. `263dc86`: the initial energy simplification converted a complex scalar
   before the intended inner-product rewrite. Staged rewrites repaired it.
2. `897e972`: the first strict tests exposed an unused section instance, an
   unused simplification argument, and a zero-matrix column simplification.
3. `f0c8141`: unfolding the column still left a partially applied zero. The
   fixture now uses `Matrix.zero_mulVec` and `zero_smul` explicitly.
4. `9b52983`: the raw driver lacked its module docstring. It already printed
   the three standard axiom reports, but that invocation failed the header
   linter. Adding the ordinary header and docstring produced the passing
   `5bbc0fd` raw run.

These failures are historical evidence, distinct from the selected passing
checks. The native target is not a full QIC root build.

## Source, local reuse, and overlap

The source is the unnumbered uniqueness assertion following
`eq:info-reset-overlap`, `02-information.tex`, lines 415–425, in the
September 24, 2026 polynomial-PEPS manuscript at
[`openai/math@adc7f124`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex#L415-L425).

No OpenAI Lean proof text is copied or adapted. The projection-residual proof
does adapt the local QIC proof inside
`SpectralFilter.filterIntegral_mulVec_of_posSemidef_gap`, generalizing its
unit eigenbasis vector to an arbitrary ground vector. This local adaptation
is identified in the module, the first ledger row, and
[reuse-and-overlap.json](reuse-and-overlap.json), with the exact source blob,
commit, declaration, lines, and Apache license. The ledger's `original`
category concerns OpenAI proof-text reuse, not absence of all library reuse.

Read-only inspection of [QIC #582](https://github.com/LionSR/QICLean/pull/582)
at `618a686200739b84c23170d2e2f0d52f440ca037` found the restricted argument
still inline in PositiveReplacement. GapPerturbation exports a positive-gap
conclusion and describes uniqueness in prose, but neither inspected module
exports the general projection/eigenspace theorem. Both remain unchanged.

## Normalization and replay

Private executor prefixes are replaced with role tokens or committed relative
log paths. Every retained input has original and normalized SHA256 values.
No diagnostic line, exit code, timing, or source revision is removed.
Production, test, and raw-driver hashes refer to their actual file bytes.

Run `python3 docs/provenance/evidence/8766-positive-gap-uniqueness/check.py`
from the repository to check file identities, log hashes, recorded revisions,
declaration/guard/raw coverage, the standard-axiom bounds, local proof
attribution, and historical-failure retention. It performs no Lean execution
or network action. The three-row ledger was also validated against the
supplied provenance JSON schema; its schema hash is recorded. This packet
does not claim to run the complete external provenance policy checker.

No root imports, blueprint files, workflows, pins, remote writes, full-root
checks, or complete CI runs are included in this evidence-only change.
