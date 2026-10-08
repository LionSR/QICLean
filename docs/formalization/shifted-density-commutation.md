# Commutation recovered from a shifted inverse power

The functional-calculus step in OpenAI's September 24, 2026 polynomial PEPS
manuscript (`03-patches.tex`, lines 160–168, equation
`eq:patch-stationarity-commutation`) is proved in
`QICLean/Analysis/ShiftedDensityCommutation.lean`. The source is fixed at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

For a positive definite matrix A and a nonzero real exponent r, the matrices
A and A^r have the same commutant. Applying continuous functional calculus
with scalar function t ↦ t^(1/r) to a commutation relation with A^r, and using
(A^r)^(1/r) = A, proves the nontrivial implication. This reuses Mathlib's
`Commute.cfc_real` and `CFC.rpow_rpow_inv`; no new diagonalization construction
is introduced. The same result with r = 2 also gives commutation with a
positive definite filter L from commutation with L², supplying the immediately
preceding spectral step in `03-patches.tex`, lines 153–168.

For x positive semidefinite, b > 0 and a > 0, the matrix x + bI is positive
definite and r = -a/2 is nonzero. Consequently, if an arbitrary matrix ρ
commutes with (x + bI)^(-a/2), then ρ commutes with x. No Hermitian, positivity,
trace or rank condition on ρ is necessary. Exponent zero is excluded: its
power is the identity, which can commute with a matrix that does not commute
with x. The regression uses an actual singular x ≥ 0 and a non-Hermitian
matrix ρ to exhibit this failure.

The premise that the native filter commutes with its actual output marginal
remains to be derived by descending stationarity. This theorem supplies only
the ensuing spectral implication, and neither assumes away nor proves that
premise. The native diagonal variation and identification with the simplex
derivative, followed by the simultaneous spectral density-order consequence,
remain separate steps.

The three production theorem statements and proofs are carried unchanged from
[QICLean PR #607](https://github.com/LionSR/QICLean/pull/607), at commit
`0e3c232fed3b901db3b992b6bd557210296e3982`. This standalone port uses the
accepted main branch and does not depend on the simplex results in
[PR #605](https://github.com/LionSR/QICLean/pull/605). The existing copyright
and mathematical source citation are retained. The obsolete provenance-ID
block and separate evidence archives are not carried forward, following
[PR #678](https://github.com/LionSR/QICLean/pull/678).

The original proof was based on the mathematical manuscript and Mathlib,
with OpenAI Codex (GPT-6) assistance, and reused no upstream OpenAI Lean
proof text. The standalone port preserves that proof rather than claiming
it as a new proof. Its additional regressions cover the empty index type,
a singular positive semidefinite matrix with a positive shift, exponent two,
and the inverse-power implication for positive a.
