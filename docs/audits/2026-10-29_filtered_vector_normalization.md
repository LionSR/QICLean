# Normalized filtering with error and Schmidt-rank bounds

AKLV, arXiv:1301.1162v1, Lemma 6.3 (`l:5`), source
`1dfrustrated34.tex`, lines 1023–1048, repeatedly applies an approximate
ground-state projector and normalizes its output. These auxiliary results
express that operation on the actual filtered vector.

Let K fix a unit vector Gamma and preserve its orthogonal complement, with
squared contraction bound delta on orthogonal unit vectors. If x has nonzero
overlap a with Gamma, then Kx is nonzero. There is a unit scalar c such that
psi = c Kx / norm(Kx) is a unit vector and

`norm(psi - Gamma)^2 ≤ 2 * delta * norm(x - a Gamma)^2 / norm(a)^2`.

In a bipartite space, the same psi has Schmidt rank at most the operator
Schmidt rank of K times the Schmidt rank of x. The input x need not be
normalized. Nonnegativity of delta is not an extra hypothesis: its needed
consequences follow from the contraction estimate.

The squared triangle inequality supplies the elementary comparison between
successive targets. The proofs reuse the existing phase-minimized
normalization, homogeneous contraction, and rank-growth lemmas. No additional
proof-automation pattern is introduced.

These statements do not construct physical filters or a sequence of changing
ground states. They are the finite-dimensional normalization step used by those
later constructions. Verification commands and results are recorded in the
pull request.

## Verification

The targeted Lake build passed (2,795 jobs). Both modules passed strict implicit
arguments and Mathlib standard linters with warnings as errors. All three
results were checked with `#print axioms`; only `propext`, `Classical.choice`,
and `Quot.sound` occur. Blueprint/source synchronization, generated import
checks, and proof-token and file-length checks passed.
