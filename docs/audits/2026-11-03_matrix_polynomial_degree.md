# Entrywise degree bounds for matrix polynomials

`Algebra/MatrixPolynomialDegree.lean` proves three elementary bounds, `Matrix.polynomial_natDegree_mul_apply_le`, `Matrix.polynomial_natDegree_pow_apply_le`, and `Matrix.polynomial_natDegree_aeval_apply_le`.

For rectangular matrices over the polynomial semiring of any semiring R, entrywise degree ceilings add under multiplication. For square matrices with a finite index set, an entrywise ceiling d becomes at most r*d under the r-th power. Finally, for a commutative coefficient semiring R, evaluating an actual scalar polynomial P at the matrix gives entrywise ceiling P.natDegree*d. The matrix coefficients need not commute. Zero polynomials, zero powers, and empty matrix index sets are included.

The multiplication proof uses the actual finite matrix-product sum and Mathlib's polynomial product and finite-sum bounds. Power induction reuses that result. The evaluation proof expands the actual polynomial evaluation into its coefficient-weighted powers, then uses Mathlib's scalar-action and finite-sum bounds. No additional degree, interpolation, spectral, or decomposition hypothesis is introduced.

These are algebraic auxiliaries for the finite parameter interpolation supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333, and the soft construction at lines 1373–1420. They are not the source's improving-family or running-time theorem.
