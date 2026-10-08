# Canonical entropy spectral tails

`QICLean.Entropy.SpectralTail` connects a density-matrix entropy bound to the
canonical projector `Matrix.spectralProjectionGE σ t`, reusing the spectral
projection and counting theorem from `Analysis.ShiftedDensityTruncation`.

For `0 < t < 1`, the excluded mass is at most `S(σ) / (-log t)`. With
`S(σ) ≤ M`, `M > 0`, and `c > 0`, cutoff `exp(-c M)` gives rank at most
`exp(c M)` and excluded mass at most `1/c`. Zero eigenvalues require no
faithfulness assumption. Eigenvalues at the cutoff belong to the head.
For a zero entropy budget a separate cutoff-one theorem gives rank at most
one and zero excluded mass; it does not divide by zero.

The expectation-transfer theorem is valid for every effect between zero and
the identity and equal-trace Hermitian matrices. It uses the Jordan parts of
the difference and `Matrix.traceDistance`, which is **half** the full trace
norm. The `spectralProjectionGE_constant_tail` corollary instead takes the
manuscript's explicit **full** trace-norm bound `traceNorm (ρ - σ) ≤ 1/16`.
Its excluded mass is at most `1/8` (the stronger intermediate bound is `3/32`).
The projector always comes from `σ`; it is not replaced by a projector of `ρ`.

The final regulator corollary invokes `Analysis.PatchRegulator` directly.
It assumes the entropy bound, closeness, density order and commutation where
needed. It does not prove the original ground state's global-gap area law,
the filtered state's physical closeness, or the complete PEPS theorem.

## Source

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`03-patches.tex:362–413`, equations `eq:patch-constant-tail` and
`eq:patch-regulator-trace`. The proofs are independently written from the
mathematical argument, with no upstream Lean proof text reused.

## Regression checks

`QICLeanTest.SpectralTail` exercises a rank-deficient pure state, the
maximally mixed two-level state at and strictly above the cutoff, the
zero-entropy endpoint, a noncommuting target state, the half/full norm
convention and the impossibility
of a trace-one state on an empty index set. `SpectralTailAxioms` reports all
exported kernel dependencies. Both are included in the strict PR workflow.
