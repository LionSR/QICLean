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

Ownership was checked on October 7, 2026. QICLean PR #603 owns local lifts,
actual regional states and one-step trace stripping; TNLean PR #8830 owns the
unstripped coordinate first variation and actual marginal adapter. The
analytic-core session owns the descending stationarity and floor-calculus
work. This independent spectral implication was coordinated separately.

All proof text is original and based on the mathematical manuscript and
Mathlib. OpenAI Codex (GPT-6) assisted the proof, source comparison and checks;
no upstream OpenAI Lean proof text was reused.
