# Scalar-shift derivatives of positive matrix powers

`QICLean/Analysis/ShiftedPowerDerivative.lean` supplies the finite-dimensional
scalar-shift calculation supporting
[OpenAI's September 24, 2026 PEPS manuscript, lines 425–451](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L425-L451).
The immutable source revision is `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The derivative of an individual filter occurs at lines 425–431; its later
use in an ordered product and minimum envelope is a downstream obligation.

## Statements and scope

For a finite complex positive semidefinite matrix A, a positive real b, and
an arbitrary real exponent r:

- The derivative of s ↦ (A+sI)^r at b is r(A+bI)^(r−1).
- The derivative of R ↦ (A+exp(−R)I)^r is
  −r exp(−R)(A+exp(−R)I)^(r−1).
- The Euclidean operator norm of b(A+bI)^(−1) is at most one.

All scalars and exponents in these statements are real. The codomain is the
complex matrix space with its Euclidean operator norm. No trace condition,
invertibility of A, or nonempty index hypothesis is needed. The statements
therefore include singular matrices and the zero-dimensional matrix space.
The zero exponent gives the zero derivative. No inverse identity at b = 0
or derivative in a noncommuting matrix direction is asserted.

For r = −a/2, the existing power-addition law factors the regulator
derivative into (a/2) times b(A+bI)^(−1) times (A+bI)^(−a/2).
The regression file checks this exact form without adding another public
pass-through theorem. The ordered-product derivative and minimum envelope
remain downstream work; these three results do not complete Proposition 4.1.

## Reuse and simplification audit

The derivative reuses `Matrix.PosSemidef.add_smul_one_rpow_eq_cfc` from
`ShiftedDensityTruncation`, already accepted in QIC main. It fixes the
Hermitian eigenbasis, differentiates scalar real powers coordinatewise,
and uses the existing diagonal linear map and constant matrix
multiplications. There is no new general Fréchet calculus, eigenvector
selection varying with the regulator, or matrix antitonicity argument.

The norm proof uses `cfc_const_mul`, `norm_cfc_le`, and the scalar inequality
0 ≤ b/(t+b) ≤ 1 for t ≥ 0. The existing
`l2_opNorm_add_smul_one_rpow_le_of_nonpos` requires trace one, so cannot cover
the arbitrary positive semidefinite statement. Importing
`OperatorMean.PowerDerivative` merely for its inverse estimate would add a
large unrelated integral/Fréchet dependency and would use matrix
antitonicity. The direct finite-spectrum proof avoids both. No duplicate
public definitions, convenience wrappers, or special-case suffix ladder
are introduced.

## Validation

The production file and regression file were checked serially with the
package Lean options, Mathlib standard linters, warnings as errors, and a
90-second timeout. The regression file additionally disables auto-implicit
variables. Tests cover empty index types, a singular two-dimensional
matrix, the zero matrix, the zero exponent, the factored negative-exponent
chain rule, rejection of a nonnegative-only shift hypothesis, an actual
negative-shift counterexample to contraction, and failure of an inverse
identity at zero.

All three public declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. Dependency source and artifact hashes were audited before and
after checking the final files. Source provenance remains planned until
immutable source publication and a separate evidence update. No full local
Lake build, aggregate declaration check, or full blueprint rendering is
claimed by the focused checks.
