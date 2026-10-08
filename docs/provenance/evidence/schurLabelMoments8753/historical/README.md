# Signed centered Schur-label moments

The three declarations compare the actual centered Schur-label exponential
moments to supported surprisal moments. The positive comparison assumes a
normalized invariant positive semidefinite state and a nonnegative parameter.
The negative comparison is a weighted trace Cauchy–Schwarz inequality and
requires neither normalization nor a sign restriction on its parameter.
The copy-permutation corollary substitutes the proved polynomial Schur
remainder when 0 ≤ 2u ≤ 1. The center is arbitrary throughout.

The source is Section 7, lines 227–237, of the September 24, 2026 area-law
manuscript. Bounds on the centered surprisal moments, their independent-copy
specialization, and the later comparator estimate are separate results.
No global inequality between the label and surprisal is assumed: the positive
comparison treats the kernel as a zero trace weight.

## Verification

`commands.json` records raw Lean commands using the package options and
`warningAsError=true`, the exact environment, exit codes and durations. The
strict source check passed in 4.730 seconds. The separate imported axiom check
passed in 5.289 seconds; all three public declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

The 4,650 actually imported module artifacts are recorded in
`imported-dependencies.json`. The previously imported dependency hashes were
checked before and after the final compilation and audit and agree exactly.
The input dependency source is pinned to
`f24f6b07ddf56b782f6e097e0fe6a95907fbeef2`, based on
`f675fee80416c966989bc8bc124a3d54b1348492`. Only the new module was compiled;
all dependency artifacts were read without modifying the shared cache.

This was direct Lean verification, not a Lake build or full blueprint
`checkdecls` run. The separate mathematical fragment has exactly one tag for
each public declaration; its coverage and hash are recorded. Integration
and full-book rendering remain with the area-law coordinator.

The focused repeated-pattern scan covers the new module and its three
nearest spectral-resolution dependencies. The two logarithmic support
comparisons are recorded in the repository tactic-pattern ledger. No new
automation is introduced.
