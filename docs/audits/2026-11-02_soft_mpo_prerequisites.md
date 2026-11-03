# Shared estimates for a corrected soft-truncation approximation

Four modules provide the finite algebra and normalized estimates for a
one-interval soft-truncation approximation. They are auxiliary to ALVV,
arXiv:1602.08828v2, `thm:cluster-approx` and `lem:exp-approx-eff`.

The mandatory-label estimate assumes Hermiticity, local norms at most one,
and an explicit lower energy H >= lambda I. It bounds the finite alternating
sum R by exp(t lambda) ||R|| <= (exp(t) - 1)^|S|. The separate union coefficient
estimate supplies the factor 2^|U| used by the corrected label expansion.
Neither result states the false printed physical-support approximation.
Its counterexamples remain recorded in the published TNLean cluster note.

The finite heat identity retains the constant term and the scale:

    h_(m,t)(U) = sum_(a=0)^m c_a(t,m) exp(-a U/t),
    sum_(a=0)^m |c_a(t,m)| <= t 2^(m+1).

It is proved for the same Hermitian matrix U by continuous functional calculus.
The logarithmic order lemma bounds W (exp(N^2 b^r) - 1) at a requested accuracy.
These estimates do not assert the unrestricted parameter or running-time claim
of the source's approximation lemma.

## Source and ownership

The worktree starts at exact QICLean revision
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`.
The two cluster estimates are selected source files from preserved revision
`ec3434f7d6fbdfc5318dc55934feb9532e239b81`; the heat and logarithmic-order
modules are the preserved 2026-10-29 soft-MPO sources. No existing production
source is replaced. The heat module imports the current scalar definition
directly; it does not require the separate soft-versus-hard comparison.
Generated imports and focused mathematical sections are updated on this base.

## Verification status

All four new modules passed fresh strict actual-name checks on 2026-11-02.
The selected non-overridden production dependencies were required to be
source-identical to the exact target revision, and all three build-input files
were checked against that revision. Two differing existing dependencies,
`WeylMonotonicity` and `SoftTruncation`, and both selected importers above them,
`TraceExponentialPerturbation` and `MatrixBernsteinInputs`, were re-elaborated
from their current source into temporary objects. Their source is not part of
the contribution.

The separate imported audit of all seven new public declarations passed. Every
declaration depends only on `propext`, `Classical.choice` and `Quot.sound`.
The ordinary target build and compiled complete-book checks are also pending.
No provider or dependency cache was modified, no Mathlib source was rebuilt,
and this source-only worktree has no `.lake` directory. No Lean test fixture
is added; local foundation commands are confined to a temporary combined audit.

Focused mathematical PDF excerpts were rendered twice and visually inspected.
They supplement the source review; they do not replace the pending complete
compiled-book check.
