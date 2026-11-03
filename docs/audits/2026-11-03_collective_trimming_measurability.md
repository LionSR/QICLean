# Borel measurability of collective trimming projections

`Entropy.measurable_trimProj` and `Entropy.measurable_trimStep` prove
that the literal successive collective-trimming products and individual
spectral cut projections are Borel functions of the entire input family.
The threshold, cut sequence and number of steps are fixed. The family
need not be orthonormal or linearly independent. Empty families, zero
vectors, arbitrary real thresholds and arbitrary cut orders are included.

The proof retains the original definition in ALVV, arXiv:1602.08828v2,
Definition `def:trimming`, lines 648–655. It uses the original stacked
Gram operator, whose entries are continuous finite sums, and the exact
cut-marginal identity from `ViableSubspaceTrimmingInvariance`. At each
step the current product conjugates that Gram operator; regional partial
trace is continuous. The fixed closed spectral cutoff is Borel by
`Matrix.measurable_spectralProjectionGE`, including at a threshold
eigenvalue. The local lift is continuous, so literal induction proves
measurability of the next product.

No eigenbasis is selected in this proof, and no measurability hypothesis
is assumed for the output projections. This does not yet prove
measurability of the final trimmed-subspace projector or a conditional
adaptive sampling law.

## Verification

The exact immutable provider was TNLean
`e2706cbe715c49745d4399d37dabe3d2559cc494` and its own QICLean package
`de8a9d1286709f39d8c37d4d52d6e336925863e5`. The check used explicit
immutable overrides for the frozen Borel spectral-cutoff theorem and
the frozen trimming invariance, including its freshly checked changed
threshold and trimming importer closure. No old importer object compiled
against changed source was reused. All selected source, object and
build-input hashes were guarded.

Strict actual-name private compilation passed in 4.473 seconds with
default options and 51 selected QIC source/object pairs. The three-name
imported foundation inspection passed in 4.495 seconds; each result uses
only `propext`, `Classical.choice`, and `Quot.sound`. The temporary
inspection source was deleted. No ordinary library build, shared cache
mutation or Mathlib source compilation was invoked.

The new reader section follows basis independence. Source declaration
synchronization, generated imports, reader prose, pattern, integrity and
whitespace checks pass. The mathematical reader is rendered and visually
inspected. Canonical ordinary compilation and compiled blueprint checks
remain for coordinated integration with the frozen parent results.
