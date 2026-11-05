# Fixed-node interpolation of matrix polynomials

A matrix with polynomial entries of degree at most d is recovered from its
values at the fixed integer nodes 0 through d. The scalar Lagrange weights
are common to every entry and every matrix with that degree bound.

The new theorem `Matrix.map_polynomial_eval_eq_sum_lagrange` uses Mathlib's
`Lagrange.eq_interpolate` entrywise. It is stated over any field of
characteristic zero and permits arbitrary row and column sets. No new
coefficient representation or interpolation weights are defined.

This is supporting algebra for a family chosen before an estimated soft
center, associated with ALVV, arXiv:1602.08828v2, Proposition 5.7 and
`t:aisefficient`, lines 1311–1420. It does not construct the physical heat
operators, derive the required polynomial degree, or prove an improving
family. Those applications must supply their actual matrix polynomial and
its derived degree bound. No spectral or computational conclusion is part
of this auxiliary statement.
