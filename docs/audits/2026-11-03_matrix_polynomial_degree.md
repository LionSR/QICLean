# Entrywise degree bounds for matrix polynomials

`Algebra/MatrixPolynomialDegree.lean` proves three elementary bounds, with exactly the prepared signatures of `Matrix.polynomial_natDegree_mul_apply_le`, `Matrix.polynomial_natDegree_pow_apply_le`, and `Matrix.polynomial_natDegree_aeval_apply_le`.

For rectangular matrices over the polynomial semiring of any semiring R, entrywise degree ceilings add under multiplication. For square matrices with a finite index set, an entrywise ceiling d becomes at most r*d under the r-th power. Finally, for a commutative coefficient semiring R, evaluating an actual scalar polynomial P at the matrix gives entrywise ceiling P.natDegree*d. The matrix coefficients need not commute. Zero polynomials, zero powers, and empty matrix index sets are included.

The multiplication proof uses the actual finite matrix-product sum and Mathlib's polynomial product and finite-sum bounds. Power induction reuses that result. The evaluation proof expands the actual polynomial evaluation into its coefficient-weighted powers, then uses Mathlib's scalar-action and finite-sum bounds. No additional degree, interpolation, spectral, or decomposition hypothesis is introduced.

These are algebraic auxiliaries for the finite parameter interpolation supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333, and the soft construction at lines 1373–1420. They are not the source's improving-family or running-time theorem. Their separate blueprint entries state precisely these degree bounds.

## Verification

The source-only worktree is based on QICLean `79fb1403dd2ec8ca448204f89ccef73c1a77f509`, registered under the QICLean source repository rather than any dependency checkout. It has no `.lake`. The guarded private checker used fully verified TNLean `6dcb693b498041f9f0e2efb8df37a5474aac2b17` and its own QICLean package at the same QICLean revision. The new source imports only prebuilt Mathlib modules. No provider, dependency source, build cache or Mathlib object was modified.

The complete three-lemma production source passed the default strict check in 3.354 seconds, with zero QICLean dependency pairs. Its imported three-name foundation audit passed in 3.398 seconds; every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. Temporary audit commands were deleted. The prepared public signatures were compared byte-for-byte before the proof bodies and are unchanged.

The import-aggregator check, whole source-only blueprint scan, changed-prose check, whitespace/proof-token checks and tactic-pattern scan passed. All three new blueprint references resolve. Canonical ordinary and compiled blueprint checks remain integration requirements. No local cache was created for these source checks.
