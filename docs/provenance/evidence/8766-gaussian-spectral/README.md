# Gaussian spectral estimate

`GaussianFilter.norm_sub_ground_le_of_coefficients` derives

\[
\|y-\langle\Omega,x\rangle\Omega\|
\le e^{-h\Delta^2/2}\|x\|
\]

from a Hermitian Hamiltonian, a unit ground eigenvector, the positive-semidefinite
gap defect with `Δ > 0`, `h ≥ 0`, and the exact Gaussian multiplier identity for
each eigenbasis coefficient of `y`. The estimate uses Parseval and has no
factor depending on the matrix dimension. The input vector is arbitrary.

`GaussianFilter.eigenvector_ground_or_gap` supplies the ground/excited
dichotomy. Its ground branch reuses the positive-gap uniqueness theorem;
its excited branch combines Hermitian orthogonality with the quadratic-form
gap inequality. The parameter `Δ` remains a lower bound on the gap.

The source is `02-information.tex`, lines 426–452, particularly
`eq:info-gaussian-two-sided`, from the September 24, 2026 polynomial-PEPS
manuscript at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This standalone module is the spectral step only: it does not import the new
Gaussian kernel or matrix-integral module. The integral consumer must derive
the exact coefficient identity. The module makes no claim to complete
truncation, locality, regional-gap, or reset arguments.

[reuse.json](reuse.json) records the exact local QIC proof and test-fixture
adaptations, their base revision, Git blobs, SHA256 values, and Apache license.
The Parseval estimate is written using Mathlib's existing theorem. No OpenAI
Lean proof text is copied or adapted.

`QICLeanTest/GaussianSpectralGap.lean` supplies three consumer checks:

- The endpoint `h = 0` and an arbitrary input vector
- A vector constructed by inverse eigenbasis coordinates, whose multiplier
  identity is proved directly from that construction
- A two-dimensional shifted-projector Hamiltonian with ground energy `-7`,
  gap lower bound `2`, width `2`, and an unnormalized input with a non-real
  phase; the resulting bound is `2 exp (-4)`

Both public declarations have exact standard-axiom guards. The separate
[raw driver](drivers/GaussianSpectralRawAxioms.lean) prints their axiom reports.
All four checks passed at the actual source revision
`03c84b6e86a6b0cdf1f0affd25d0738379159bb5`: native target build, strict
production, strict consumers and guards, and the strict raw axiom driver.
The native build reports 3,128 jobs. The strict commands disable both implicit
variable options, enable Mathlib standard linters, and treat warnings as errors.
Both raw reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`.
The raw driver's informational hash-command diagnostics are preserved.

[verification.json](verification.json) binds the checked source bytes, Git
blobs, line counts, actual run revisions, exact commands, elapsed times, and
output hashes. The [two-row ledger](../../openai-math.d/gaussian-spectral8766.json)
records these actual checks. Its `original` category concerns OpenAI proof-text
reuse; all local QIC adaptations remain separately attributed.

The complete retained history consists of three command-record groups and
eight logs. It preserves both failed invocations:

1. `7d2ef5e`: the conjugation rewrite did not match the `star` expression.
   An explicit equality for the real eigenvalue repaired the rewrite.
2. `00432e1`: production passed, but strict consumer checks found a redundant
   final tactic and an unused finite-type instance. Removing the tactic and
   proving projector Hermiticity directly repaired those checks.

Private executor path prefixes are replaced with role tokens or committed
relative log paths. Original and normalized SHA256 values are retained for
every input. No commands, diagnostics, results, timings, or revisions are
removed or relabeled. All Lean/Lake/cache execution belonged to the parent
integration task; assembling this metadata ran none of those commands.

Run `python3 docs/provenance/evidence/8766-gaussian-spectral/check.py` from the
repository to verify the source identities, ledger coverage, log hashes,
consumer and axiom coverage, local reuse, and retained failures. The ledger
also passed `jsonschema.validate` against the supplied provenance schema v1;
the schema hash is recorded. This does not claim to execute the complete
external provenance policy checker, a root build, public CI, publication,
or a complete paper theorem. No Lean source, shared imports, workflows,
blueprint files, or dependency pins change in this evidence update.
