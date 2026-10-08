# Rectangular window minorization

## Ownership and hypotheses

The channel-generic proof belongs in QICLean. `OrderedRectangular` supplies dependent
interval composition; `WindowMinorization` derives cyclic densities from a full-cycle
fixed point and the residual estimate. `ChoiResidual` handles normalized Choi
minorization and Hilbert--Schmidt induced norms. No matrix norm is redefined.

The local condition uses the output-first normalized Choi matrix and coefficient
`η / D_input`. The dimensions may vary, and the reference densities may be singular.
Complete windows are removed from the right, leaving a shorter left remainder.
Its trace scale is one; the full residual trace scale is `(1 - η) ^ (length / width)`.

The principal bound is `2 * D_input * (1 - η) ^ (length / width)`. It holds also
when the trace scale vanishes. No qualitative convergence hypothesis is promoted
to a uniform quantitative rate.

## Reuse and compatibility

- The PSD trace bound and the Gram-trace operator-norm inequality extend the existing
  `MatrixTraceInequalities` owner rather than introducing a duplicate norm library.
- `Kraus.RectangularChain` owns the exact recursive rectangular Kraus product and
  transfer definitions formerly in TNLean's preparation block module. TNLean keeps
  thin compatibility declarations with the original public names and binders.
- `Matrix.entry_eq_of_heq` is moved verbatim from TNLean's MPDO proof to the lightweight
  `Algebra.MatrixDependentEntries` module. Its fully qualified name is unchanged.
- `Real.pow_nat_div_le_two_mul_exp` is the former private square-window scalar estimate,
  now reusable by both square and rectangular preparation results.

No block geometry, padding, MPS state or circuit types are moved upstream.

## Validation at the review checkpoint

Every new or modified non-aggregate QIC production module passed an actual-source,
single-process Lean check with the package options and warnings treated as errors.
`QICLeanTest/WindowMinorization.lean` also passed. This regression alternates dimensions
two and three, uses different singular rank-one references, includes a nonempty
remainder with different endpoint dimensions, and derives a compatible cyclic family.

The checks used Lean 4.35.0-rc3, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`,
and QIC base `075e870322202eb9eaa8f7d166996d4be7920686`. All local inputs were audited
for source/options/pin compatibility and artifact hashes. An unchanged `RankOne`
frontier was checked separately; no cold transitive build was run.

The generated aggregates, blueprint declaration scanner, reader-facing prose scanner,
file-length guard and whitespace check passed. CI builds the generic targets and
regression before the full required library build. Local focused checks are not a
substitute for that full exact-head CI.

Changing `MatrixTraceInequalities` deliberately falls outside the additive-only cache
seed policy. The owner was not split or relocated merely to qualify for that seed.

## Downstream boundary

The dependent TNLean integration identifies actual original tensor blocks with these
rectangular intervals, derives the compatible bond references, and obtains the
uniform constants `K = 4D` and `r = -log(1 - η/2) / s`. Its existing physical compiler
is unchanged. Source-matched local checks cover the interval and block-rate bridge;
the heavy physical compiler import closure and preserved square/MPDO consumers remain
mandatory downstream CI gates.
