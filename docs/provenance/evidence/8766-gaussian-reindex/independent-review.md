# Independent review: finite-reindex Gaussian covariance

Reviewed production source: `QICLean/Analysis/GaussianFilter/Reindex.lean`
at `b23c6270b5c7061bb0b2ef38f25f73c3a182ff27`.
Consumer checkpoint: `858eb39102006bbbe01a1ddcc12057fea5ad4e2e`.
Compiler and axiom output are recorded separately; this review does not replace
those checks.

## Mathematical contract

- The coordinate map is exactly `A ↦ A.submatrix e.symm e.symm`.
  Its target coordinate `(a,b)` is `A (e.symm a) (e.symm b)`.
  It neither transposes the two indices nor conjugates matrix entries.
- The same finite equivalence transports both axes of every square matrix.
  Therefore Mathlib's `Matrix.reindexAlgEquiv` preserves multiplication and the
  identity. Arbitrary independent row and column equivalences would not suffice
  for the exponential argument.
- `NormedSpace.map_exp` applies to the continuous algebra equivalence. The local
  rational normed-algebra instance is a restriction of the existing complex
  instance; it adds no mathematical assumption.
- The time path is defined as `exp (t • (Complex.I • H))`. Linearity transports
  the scalar `t i` unchanged. No Hermiticity assumption is used by covariance.
- The integrand keeps the order `U(H',t) * W * U(H,-t)` throughout. Covariance
  is separate from the adjoint identity, which exchanges the generators.
- `ContinuousLinearEquiv.integral_comp_comm` needs no integrability hypothesis.
  Its proof uses a continuous inverse to preserve integrability and hence the
  zero-valued Bochner convention for nonintegrable functions. Using only an
  arbitrary continuous linear map here would not justify dropping integrability.
- The full and truncated theorems unfold the actual Gaussian integrals. The
  truncated theorem retains precisely the restriction of `gaussianReal 0 h` to
  `Set.Icc (-T) T`, without renormalization or a new output assumption.

## Edge cases and consumer discrimination

- `h = 0` is allowed: the Gaussian is a Dirac measure, and the full filter is
  the original input. The consumers retain the entries `i` and `2i` after
  transport from `Fin 2` to `Bool`.
- A negative cutoff is allowed: `[-T,T]` is empty and the truncated filter is
  zero. There is no added condition `0 ≤ T`.
- Empty finite index types are allowed: `Fin 0 ≃ Empty` instantiates both full
  and truncated covariance statements. Matrix spaces then have one element;
  the equivalence and integral arguments remain valid.
- The concrete input has asymmetric non-real off-diagonal entries. Its two
  generators are distinct and each is proved non-Hermitian using a non-real
  diagonal entry. The entry-level consumers preserve generator placement,
  time signs, and row/column orientation for all six covariance declarations.

## Source boundary

The paper passage is `peps-02-information-adc7f124.tex`, lines 426–452, from
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. It defines the full
Gaussian filter and its finite-time truncation in the reset argument.
This change supplies the generic coordinate-transport interface needed to use
those integrals after the existing regional `threeSplit` / `sheetSwap`
identifications. It establishes neither finite-time locality nor the complete
reset theorem. No issue was found in the six mathematical contracts.
