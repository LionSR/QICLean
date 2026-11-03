# Fixed-node interpolation of matrix polynomials

A matrix with polynomial entries of degree at most d is recovered from its
values at the fixed integer nodes 0 through d. The scalar Lagrange weights
are common to every entry and every matrix with that degree bound.

The new theorem `Matrix.map_polynomial_eval_eq_sum_lagrange` uses Mathlib's
`Lagrange.eq_interpolate` entrywise. It is stated over any field of
characteristic zero and permits arbitrary row and column sets. No new
coefficient representation or interpolation weights are defined. The existing
finite monomial and integer-grid coefficient-recovery theorems remain active.

This is supporting algebra for a family chosen before an estimated soft
center, associated with ALVV, arXiv:1602.08828v2, Proposition 5.7 and
`t:aisefficient`, lines 1311–1420. It does not construct the physical heat
operators, derive the required polynomial degree, or prove an improving
family. Those applications must supply their actual matrix polynomial and
its derived degree bound. No spectral or computational conclusion is part
of this auxiliary statement.

## Verification

The production module passes strict elaboration in 3.577 seconds against the
fully built TNLean 6dcb693b / QICLean 79fb1403 pair. It imports Mathlib only;
no QICLean or TNLean proof module is substituted. The check retains the
standard linters, warnings as errors and default proof-resource limits.
An imported foundation inspection passes in 3.402 seconds and finds only
`propext`, `Classical.choice` and `Quot.sound`; its temporary source is deleted.

Complete source/blueprint synchronization, generated imports, reader-facing
prose, forbidden-token and whitespace checks pass. The supporting entry is
a lemma. Its one-page mathematical excerpt was rendered and inspected, with
no overfull boxes. The tactic-pattern ledger records the direct reuse of
scalar interpolation. The tensor-network repository's pattern scanner is
used with this repository's source root; no scanner or role-policy script is
added to QICLean.

Ordinary combined build and compiled blueprint verification remain pending
for this new contribution. The held dependency pair's preceding full build
and checks are separate evidence. No provider, ordinary build artifact or
Mathlib cache was changed by the private proof checks.
