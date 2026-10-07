# Actual Gaussian ground-vector estimates

This packet records five theorems that apply the Gaussian integral to unit ground
vectors of two Hermitian matrices at a common energy. Each positive-semidefinite
gap defect supplies a strictly positive lower bound `Δ` on the corresponding gap.
Writing `M` for the actual integral and `z = ⟪Φ, W Ψ⟫`, the conclusions are

- `‖M Ψ - z Φ‖ ≤ exp(-h Δ²/2) ‖W‖`
- `‖M† Φ - conj(z) Ψ‖ ≤ exp(-h Δ²/2) ‖W‖`

The forward theorem only requires the target gap. The two-sided theorem uses
both gaps. The Gaussian coefficients are proved from the actual integral and
the Hermitian eigenbasis equation; they are not assumptions. The dimension-free
norm bound follows from the local spectral theorem and Mathlib's Euclidean
operator norm estimate.

For an explicitly real overlap and `‖W‖ ≤ 1`, the next theorem supplies the
paper's common real coefficient, its two residual bounds and the contraction
`‖M‖ ≤ 1`. A separate hypothesis asserting Hermiticity of `W` would not make a
cross-vector overlap real.

The remaining two results bound the unrenormalized integral over `[-T,T]`, with
`T ≥ 0`. Each residual is at most
`(exp(-h Δ²/2) + 2 exp(-T²/(2h))) ‖W‖`.
The proof adds the existing operator-norm tail estimate by the triangle
inequality. All results use the nonnegative-variance probability measure and
include `h = 0`. Positive variance is needed only for the density interpretation
already provided by the matrix-integral module. No spatial locality or full
reset statement is claimed.

The source is the September 24, 2026 Polynomial-PEPS manuscript, `lem:reset`,
`02-information.tex` lines 426–452 and `eq:info-gaussian-two-sided`, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The real overlap comes
from `eq:info-reset-overlap`, lines 402–414. This is not a statement of GLM23.
[reuse.json](reuse.json) records the local QIC theorem calls, adapted test
fixtures, source commits, Git blobs, file hashes and Apache license. No OpenAI
Lean proof text is copied or adapted.

The five consumers cover a Hermitian all-ones input with non-real overlap `-I`,
different ground lines at energy `-7` and gap `2`, both complex phases in the
actual two-sided integral estimate, zero variance, truncation with variance `2`
and cutoff `3`, and the real-overlap contraction theorem. The all-ones input also
has a nonzero excited component. All five public theorems have exact
standard-axiom guards and separate raw reports containing exactly `propext`,
`Classical.choice`, and `Quot.sound`.

The retained command history preserves its actual revisions:

- `000af37c19f9ddb2aa9e52654e3e981a5057bdf8`: the first production build failed
  on the missing complex order scope, final coercion closure, Euclidean
  representation normalization and conjugate-inner rewrite orientation.
- `2ae6e2590cb787e3c9c252ca043686b44cbd93fc`: native production, strict
  production and strict consumers with all five axiom guards passed.
- `90bcaa0d425ad9f7916ce322edfcb229ecec8b9d`: the native target and strict raw
  five-theorem driver passed. Both native successes reported 3,269 jobs.

The ledger uses public recovery revision
`16b81356549158a8393aaea5085defd4c5022e71` on
`codex/gaussian-two-generator-filter-8766`. Its tree
`41d46a48626973c9056f36ca6163fe3b5e23665d` equals local `90bcaa0`; the metadata worker independently verified both Git object trees and all three
public/checked source blobs after the integration task fetched the official branch.
[public-source-binding.json](public-source-binding.json) retains these read-only
Git commands and their outputs. The production and consumer bytes at that checkpoint
are identical to the checked `2ae6e25` bytes. [verification.json](verification.json)
keeps these identities and the actual per-command revisions separately; no run
has been relabeled as executing at the public checkpoint.

There are six retained commands: five successes and the historical failure.
Their three command records and six complete logs retain diagnostics, exit
codes and timings. Private executor prefixes alone are replaced with role
tokens, while record log paths become repository-relative. Every original and
normalized input hash is retained.

Run `python3 docs/provenance/evidence/8766-gaussian-ground/check.py` to verify
source identities, declaration and consumer coverage, ledger commands, output
hashes, exact raw and guarded coverage, local reuse and the historical failure.
The five-row ledger also passes the supplied provenance schema v1; this is not
an assertion that the full external provenance policy checker, root build,
public CI or entire reset theorem has passed. All Lean/Lake/cache execution
belonged to the parent integration task. This packet changes no proof source,
shared router, workflow, blueprint file or dependency pin.
