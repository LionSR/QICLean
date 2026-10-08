# Concept glossary

This glossary records the mathematical meaning and hypothesis boundaries of
public QICLean constructions. Similar notation alone does not identify two
constructions.

## Closed-threshold spectral truncation

- **Declarations:** `Matrix.spectralProjectionGE`, `Matrix.shiftedPowerHead`,
  and `Matrix.shiftedPowerTail` in
  `QICLean/Analysis/ShiftedDensityTruncation.lean`.
- **Meaning:** For a Hermitian A, Π = 1_[b,∞)(A) selects eigenvalues at least
  b, including equality. For A ≥ 0 and b > 0, the shifted power F = (A+bI)^r
  has head H = FΠ and tail T = F(I−Π). The projection is determined by A
  and b; it is not extra input.
- **Source:** [OpenAI, September 24, 2026 PEPS manuscript, lines 484–502](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L484-L502),
  `eq:patch-head-tail-bounds`, with b = exp(−R) and r = aⱼ/2.
- **Proved comparisons:** H and Π have the same range and rank for every
  real r; b rank Π ≤ Re(tr A) for every real b. With tr A = 1 and b > 0,
  rank H ≤ 1/b. The tail has Euclidean operator norm at most (2b)^r when
  r ≥ 0; this bound needs no trace normalization.
- **Boundaries:** The rank is measured before outside-identity extension.
  No support inverse replaces the full-space positive shift. Empty index
  types are allowed; trace one is then impossible. These objects do not
  themselves specify a minimizing tuple, ordered regional product,
  entropy-tail bound, or tensor-network approximation.
