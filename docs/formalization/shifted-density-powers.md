# Shifted density matrices and real powers

`QICLean/Analysis/ShiftedDensityPowers.lean` proves seven generic
finite-dimensional facts used in the regularized-filter construction in
[OpenAI's September 24, 2026 PEPS manuscript, lines 51–114](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L51-L114).
The paper uses b = exp(−R) and factors (x + bI)^(−a/2). The results here
allow every positive b and every real exponent r.

## Statements and hypotheses

For a finite index type n, let D(n) be the set of complex positive
semidefinite n-by-n matrices with trace one.

- `Matrix.isCompact_setOf_posSemidef_trace_eq_one`: D(n) is compact for
  any finite n, including an empty index type.
- `Matrix.setOf_posSemidef_trace_eq_one_nonempty`: D(n) is nonempty when
  n is nonempty. This hypothesis is essential; the empty matrix has trace zero.
- `Matrix.PosSemidef.add_smul_one_posDef`: x + bI is positive definite
  whenever x is positive semidefinite and b > 0. No trace normalization is
  needed, and this declaration does not require a finite index type.
- `Matrix.continuousOn_add_smul_one_rpow`: for fixed b > 0 and real r,
  the actual matrix-valued function x ↦ (x + bI)^r is continuous on the
  whole positive semidefinite cone. Continuity is proved from continuous
  functional calculus on strictly positive matrices; it is not a hypothesis.
- `Matrix.PosSemidef.spectrum_add_smul_one_bounds`: if x belongs to D(n),
  then every real spectral value of x + bI lies in [b, 1 + b].
- `Matrix.PosSemidef.l2_opNorm_add_smul_one_rpow_le_of_nonpos`: for
  x in D(n), b > 0 and r ≤ 0, ‖(x + bI)^r‖ ≤ b^r.
- `Matrix.PosSemidef.l2_opNorm_add_smul_one_rpow_le_of_nonneg`: for
  x in D(n), b > 0 and r ≥ 0, ‖(x + bI)^r‖ ≤ (1 + b)^r.

Both norm inequalities use the Euclidean operator norm, under
`Matrix.Norms.L2Operator`. The shift acts on the full matrix space. Singular
densities are allowed, and the two exponent regimes both include zero; no
support inverse, strict positivity assumption on x, or positive-exponent
restriction is substituted for the paper's regularization.

## Proof structure

Compactness and nonemptiness are transported from the existing density-matrix
results on `Fin (Fintype.card n)` by simultaneous row and column reindexing.
The positive scalar multiple bI is positive definite, and adding x preserves
that property. Composition with continuous functional calculus proves
continuity. For trace-one x, the bound ‖x‖ ≤ Re(tr x) = 1 gives x ≤ I.
The inequalities bI ≤ x + bI ≤ (1 + b)I imply the spectral interval. Scalar
monotonicity of t^r on that interval and the norm estimate for continuous
functional calculus then give both operator-norm bounds.

## Scope and provenance

These are elementary spectral and compactness ingredients. This module does
not define the native ordered product or its variational objective, prove
minimum attainment or positivity of that minimum, or establish the paper's
ordered-product norm bounds. It does not prove stationarity, excitation-energy
estimates, or Proposition 4.1. In particular, no source-level completion label
is assigned by assuming continuity, compactness, norm estimates, or an already
minimizing tuple in place of proving those missing steps.

The proofs are independently written using existing QICLean and Mathlib
results. No OpenAI Lean proof text is copied or adapted. The separate
`docs/provenance/openai-math.d/shiftedDensityPowers8767.json` shard records the
manuscript as mathematical motivation and preserves the distinction from
upstream code reuse. Its rows remain planned, with proposed names and pending
verification, until publication supplies an immutable source revision and
fresh verification evidence for these exact declarations. Passing local checks
alone does not promote the provenance status.

The blueprint entry is
`blueprint/src/chapter/ch01_shifted_density_powers.tex`, included from the
opening chapter. It states only the generic facts above.
