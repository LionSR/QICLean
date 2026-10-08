# Spectral truncation of shifted powers

`QICLean/Analysis/ShiftedDensityTruncation.lean` proves the generic
inside-space spectral estimates used in
[OpenAI's September 24, 2026 PEPS manuscript, lines 484–502](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L484-L502),
at the immutable source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The paper takes b = exp(−R), r = aⱼ/2, and Fⱼ = Lⱼ⁻¹. The module allows
any b > 0 and any real r, with r ≥ 0 needed only for the tail-norm bound.

## Canonical objects and hypotheses

For a finite index type n, a complex PSD matrix A, b > 0, and r ∈ ℝ, set

- Π = 1_[b,∞)(A), the canonical closed-threshold spectral projection
- F = (A + bI)^r
- H = FΠ and T = F(I − Π)

`Matrix.spectralProjectionGE`, `Matrix.shiftedPowerHead`, and
`Matrix.shiftedPowerTail` define these objects using the actual matrix
functional calculus. No projection, decomposition, range, rank bound, or
norm bound is supplied as an assumption. Eigenvalues exactly equal to b
belong to the head; the tail uses the strict complement λ < b.

The mathematical statements are:

- For Hermitian A and any real b, Π is self-adjoint and idempotent,
  equals the Hermitian spectral functional calculus, and commutes with A.
- For PSD A, b > 0, and every real r, F equals the functional calculus of
  λ ↦ (λ + b)^r at A and commutes with Π.
- H + T = F. This algebraic identity is proved without PSD, trace, or
  positivity hypotheses; its natural spectral interpretation uses the
  preceding assumptions.
- H and T are the functional calculi of the corresponding truncated scalar
  powers. They are PSD, and HT = TH = 0, for every real r.
- F(A + bI)^(−r) = I. The shift is strictly positive even when A is singular.
- ran H = ran Π and rank H = rank Π for every real r. The range equality
  is stronger than a rank inequality and uses the actual inverse power.
- b rank Π ≤ Re(tr A) for PSD A and any real b, without trace normalization.
- For tr A = 1 and b > 0, rank H ≤ 1/b.
- For PSD A, b > 0, and r ≥ 0, ‖T‖ ≤ (2b)^r, without trace normalization.

The norm is the Euclidean operator norm under `Matrix.Norms.L2Operator`.
All ranks are on the original finite inside space. No rank claim is made
for H tensored with an outside identity.

All results permit an empty index type. Then the matrices and ranks are
zero, the inverse identity holds in the zero-dimensional matrix algebra,
and a trace-one hypothesis cannot be satisfied. At r = 0, the formulas
give F = I, H = Π, and T = I − Π. No nonempty-space assumption or invertibility
assumption on A is introduced.

## Proof structure

The finite spectrum permits the discontinuous threshold function to be
used in continuous functional calculus: only continuity on the spectrum
is required. Scalar indicator identities prove projection and commutation.
Composing the shift and real-power functions represents F in the functional
calculus of A. Multiplication and subtraction then give the two truncated
functions; pointwise nonnegativity and disjoint support prove positivity
and orthogonal products.

The identity H = ΠF gives ran H ⊆ ran Π. The inverse-power identity gives
Π = H(A + bI)^(−r), proving the opposite inclusion. Projection rank equals
its trace, and the eigenvalue sum bounds each term
b 1_[b,∞)(λᵢ) by λᵢ. Dividing by b in the trace-one case gives the head-rank
bound. On the tail spectrum, 0 ≤ λ < b, so 0 < λ + b < 2b; scalar monotonicity
for r ≥ 0 and the functional-calculus norm bound give the tail estimate.

## Scope and attribution

This is the single-matrix inside-space step of `eq:patch-head-tail-bounds`.
It does not choose or prove existence of a minimizing tuple, prove an
entropy-tail estimate or regulator-growth bound, construct a regional
contraction, invert or expand a native ordered product, or prove
Proposition 4.1. No arbitrary surrogate replaces the paper's canonical
closed-threshold projection. The mathematical generalization to any positive
b and all real r where valid is explicit; the tail estimate retains r ≥ 0.

All proofs are independently written from QICLean and Mathlib results. No
OpenAI Lean proof text is reused.

The blueprint is
`blueprint/src/chapter/ch01_shifted_density_truncation.tex`, routed from the
opening chapter. It covers every public declaration and states the relevant
hypotheses at each step. See also the [concept glossary](../glossary.md) and
[tactic-pattern record](../tactic_patterns.md).

## Regression contract

`QICLeanTest/ShiftedDensityTruncation.lean` has 18 examples covering empty
spaces, the zero matrix, exponent zero, singular trace-one input, a threshold
above the spectrum, the reverse inverse-power identity, and exact threshold
equality. Two negative examples prove that the stated tail estimate fails
for a negative exponent and that an inverse-filter tail need not be a
contraction. The empty-space norm test uses no trace-one assumption.
The dedicated strict CI step runs after the full project build, with a
90-second timeout, both implicit-variable restrictions, and warnings as
errors. No test assumes a chosen projector or a decomposition certificate.
