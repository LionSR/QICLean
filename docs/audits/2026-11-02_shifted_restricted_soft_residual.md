# Energy shifts and restricted soft residuals

Two auxiliary declarations support the physical original-side soft residual.
Hard clipping at a translated cutoff commutes exactly with subtracting a real
scalar energy. The proof uses composition in the existing real functional
calculus and the scalar minimum identity. Independently, the checked vector
soft–hard residual estimate yields the restricted operator-norm estimate on
any subspace. The hard cutoff is nonnegative and the soft scale is positive;
the Taylor order is at least one. No successful approximation or small global
residual is assumed. Zero-dimensional spaces and the zero subspace are allowed.

These are auxiliaries to ALVV, arXiv:1602.08828v2, `def:hard-trunc` and
`lem:exp-approx`, lines 873–886 and 1195–1255. The independent scale and order,
and the exact polynomial error from the preceding contribution, are retained.
No physical Hamiltonian, reverse comparison or efficient filter is constructed
in these generic companion results.

The shift module passed strict actual-name checking in 4.717 seconds, and the
restricted residual module in 4.990 seconds. Their imported foundation audit,
combined with the physical consumer and its newly exposed regional identity,
passed in 4.639 seconds. Both declarations use only `propext`,
`Classical.choice` and `Quot.sound`.

The checks read immutable fully built TNLean
`1f0087d553cec4bf20448b0358489716cec64caf` and its own QICLean package
`099049ed6805334c6517c66b4b9858480bc7e9c7`. The preceding new scalar/vector
leaves are explicit private overrides. Before their objects were reused, all
fourteen existing QIC source files and corresponding objects in their import
closure, and all three companion build inputs, were compared byte-for-byte
with the previous checked provider. No provider, dependency cache or Mathlib
source was changed. All new objects and foundation commands are confined to
`/tmp`; the source worktree has no `.lake`.

The mathematical book entries are included. Ordinary integrated full-library
and compiled-book checks remain pending. No permanent test fixture is added.
