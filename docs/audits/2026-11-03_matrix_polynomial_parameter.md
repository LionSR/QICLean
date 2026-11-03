# Fixed nodes for a polynomial matrix parameter

For arbitrary coefficient matrices, let B(z)=C+Σ_{a=0}^m z^a B_a.
The theorem `Matrix.aeval_polynomial_parameter_eq_sum_lagrange` proves that
P(B(z)), for every scalar polynomial P of degree at most k, is recovered
from the fixed parameter values 0 through mk. The Lagrange weights depend
only on m,k,z, before the coefficient matrices and polynomial are supplied.
No commutation among the coefficient matrices is assumed.

The proof constructs a matrix with polynomial entries using `Matrix.of`.
It derives the entrywise degree bound m, applies the existing polynomial
matrix evaluation bound to obtain mk, and uses the preceding fixed-node
interpolation theorem. Mathlib's `AlgHom.mapMatrix` and
`Polynomial.aeval_algHom_apply` transport scalar evaluation through the
matrix polynomial. No desired interpolation or decomposition statement is
introduced as a hypothesis.

This is supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7
and `t:aisefficient`, lines 1311–1420. The physical application must still
construct its actual coefficient matrices from the closing coefficients
of the same native operator chain. In particular, an exterior scalar term
may depend on the final estimated center only after the identity has been
proved for every fixed exterior matrix. No logarithm of the interpolation
parameter is treated as a polynomial.

## Verification

The exact production module passes strict elaboration in 3.656 seconds,
with both new polynomial dependencies supplied as immutable checked objects
against the fully built TNLean 6dcb693b / QICLean 79fb1403 pair. It retains
default proof-resource limits, standard linters and warnings as errors.
The imported foundation inspection passes in 4.204 seconds and uses only
`propext`, `Classical.choice` and `Quot.sound`; its temporary source is deleted.

Complete source/blueprint synchronization, generated imports, reader-facing
prose, forbidden-token and whitespace checks pass. The mathematical entry
is an auxiliary lemma. Its one-page mathematical excerpt was rendered and
visually inspected without overfull boxes. The tactic ledger records direct reuse of Mathlib's
matrix algebra homomorphism and the need for an explicit matrix constructor.
Ordinary combined build and compiled blueprint checks remain required after
integration. No provider, ordinary build object or Mathlib cache was changed
by these private checks.
