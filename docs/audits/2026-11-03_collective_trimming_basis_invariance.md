# Basis independence of collective trimming

ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655,
starts with an orthonormal basis of the input subspace. The new theorem
`Entropy.trimSubspace_eq_of_orthonormalBasis` proves that the literal
successive construction produces the same subspace for any two finite
orthonormal bases of that same subspace.

## Mathematical argument

The physical left marginal of the stacked vector is the sum of the
rank-one operators of its columns. After any physical operator `P`,
the cut marginal equals the regional partial trace of `P * Gram * Pᴴ`.
Consequently two families with equal original Gram operators give exactly
the same successive products of trimming projections, by induction.
This does not require a positive threshold or monotone cuts. For an
orthonormal basis of `S`, Mathlib's sum-of-rank-one formula identifies
that Gram operator with the orthogonal projection onto `S`. The actual
trimmed span is the image of `S` under the literal trimming product,
which therefore depends only on `S`. The zero subspace is included.

No new invariance hypothesis is assumed, and neither the trimming
algorithm nor its threshold convention is changed. This is an algebraic
result; measurability and conditional adaptive probability remain
separate consequences to be proved using a measurable choice of frame.

## Shared identity and unchanged statements

The existing two private marginal-conjugation calculations in
`Channel/SchmidtThreshold.lean` now use the thin shared theorem
`Matrix.leftMarginal_leftApply`. All six public theorem signatures in
that module are unchanged. No compatibility alias is introduced.
The original `ViableSubspaceTrimming.lean` source remains byte-identical.

## Verification

The exact provider was TNLean
`e2706cbe715c49745d4399d37dabe3d2559cc494`, with its own QICLean package
`de8a9d1286709f39d8c37d4d52d6e336925863e5`.
Strict actual-name private checks passed with default options:

- `SchmidtMarginalAction`: 3.993 seconds.
- Changed `SchmidtThreshold`: 4.816 seconds.
- Its selected importer `ViableSubspaceTrimming`: 10.311 seconds,
  freshly re-elaborated from byte-identical current source.
- `ViableSubspaceTrimmingInvariance`: 4.868 seconds, using that fresh
  importer and all changed dependencies.

The imported foundation inspection covered all nine new public results
and both refactored threshold results. It passed in 4.175 seconds; each
uses only `propext`, `Classical.choice`, and `Quot.sound`. The temporary
inspection source was deleted afterward. All selected source, object and
build-input hashes were guarded, including the changed importer graph.
No shared artifacts were copied or mutated, no ordinary build was
started, and no Mathlib source was compiled. Canonical ordinary library
compilation and compiled blueprint checks remain for integration.

Reader registration, source declaration synchronization, generated
imports, reader prose, proof integrity, pattern and whitespace checks
are recorded in the external manifest. The mathematical reader was
rendered and visually inspected.
