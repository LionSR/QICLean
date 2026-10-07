# Two-generator Gaussian matrix integral evidence

This packet covers the finite-matrix Gaussian integral and its unrenormalized
truncation from the information-reset proof, `lem:reset`, in the September 24,
2026 polynomial-PEPS manuscript. The source is `02-information.tex`, lines
426–452, at [openai/math@adc7f124](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex#L426-L452).
Coordination is under LionSR/TNLean issue #8766, comment 6041075081.

The 21 public declarations define the full and truncated filters, prove
Bochner integrability and Euclidean operator-norm contraction, identify the
adjoint by exchanging the generators, calculate the cross-eigenvector
Gaussian multiplier, convert positive-variance integrals to the Gaussian
density, and bound the truncation error by `2 exp(-T²/(2h)) ‖W‖` for `T ≥ 0`.
The probability formulation includes `h = 0`; density conversions require
`h ≠ 0`. No Hermiticity of the output is inferred from Hermiticity of `W`.

## Actual checks and revisions

[verification.json](verification.json) binds file hashes and Git blobs to
actual command receipts, timings, exit codes and normalized logs.

- Native target, strict production, six consumer examples, and all 21 raw
  axiom reports passed at `c5cd25546f2333bcd986e2dcfc8dff1a88600e65`.
- The separate 21-declaration guarded audit passed at that same revision.
- The manuscript/tracker attribution was corrected in the module header at
  `4df73de57fd0ba9f20349852d74af85a61e7880e`. Native target and strict
  production checks passed again there. No proof statement or body changed.
  Test and audit bytes remain identical to their checked `c5cd255` versions.
- The native target reported 3,263 jobs. All raw reports contain exactly
  `propext`, `Classical.choice`, and `Quot.sound`.

The strict commands disable both implicit-variable options, enable the
standard Mathlib linters and treat warnings as errors. The raw command's
informational hash-command diagnostics are retained. No linter or proof
budget was relaxed.

The six consumers test a non-real Hermitian input whose two-generator
output is not Hermitian, the swapped adjoint, the signed phase with a
non-real eigenvector, zero variance, an empty negative-cutoff window and
an empty finite index type. The full guarded driver additionally covers
every public definition and theorem, including both simp-tagged theorems.

## Local proof reuse

The proof text adapts existing QIC arguments from
`QICLean/Analysis/SpectralFilter/MatrixFilter.lean` at base revision
`3080ce291ad7f8796c5416a78af9a63ccf10ea2e`.
[reuse.json](reuse.json) records the exact source blob, SHA256, Apache
license, declaration names and line ranges for seven public adaptation
targets. In particular, the phase calculation and continuous-linear
matrix-element integral argument follow the existing spectral filter;
the adjoint argument is shared through a private helper and changes the
conclusion to exchange the two generators. Existing unitary-path and
Mathlib Gaussian APIs are reused directly. The scalar kernel and tail
results come from the separately documented `GaussianFilter.Kernel` module.

No OpenAI Lean proof text is copied or adapted. The ledger's `original`
category refers to that provenance scope and does not deny the local QIC
proof adaptation documented here. The 21-row ledger is
[gaussian-matrix8766.json](../../openai-math.d/gaussian-matrix8766.json).

## Retained failures and runner incident

The packet preserves earlier failed checks separately from final passing
checks. At `3b32da1`, the missing NNReal notation scope caused elaboration
failures. At `a40d30a`, production passed but strict fixtures exposed a
scalar-type annotation, a complex-exponential simplification and an unused
simp argument. All three fixture issues were repaired before `c5cd255`.

After the four successful commands in `gaussian-matrix-c5cd.json`, the
runner attempted a nonexistent guarded-driver filename. Its diagnostic is
retained as `gaussian-matrix-c5cd-4.log`; the original receipt stops before
that attempt, so [runner-incident.json](runner-incident.json) explicitly
leaves its command receipt, exit code and timing unknown. The correct
filename was then checked successfully in
`gaussian-matrix-guards-c5cd.json`. This runner incident is not a failed
mathematical proof or consumer at the final source.

## Normalization and replay

Private executor prefixes are replaced by role tokens or committed
relative log paths. Original and normalized SHA256 values are retained.
No diagnostic line, source revision, command argument, timing or recorded
exit code is discarded.

Run `python3 docs/provenance/evidence/8766-gaussian-matrix/check.py` from
the repository to verify source hashes, declaration/guard/raw coverage,
standard axioms, actual receipt links, historical failures and local proof
attribution. This checker performs no Lean, network or remote action. The
ledger was also validated with `jsonschema.validate` against the supplied
provenance schema v1; its hash is recorded. This is not a claim to have run
the complete external provenance policy checker.

These checks do not assert a full QIC root build, public CI, a spatial
locality estimate, a ground-state norm estimate or the full information-reset
theorem. No shared blueprint files or dependency pins are changed here.
