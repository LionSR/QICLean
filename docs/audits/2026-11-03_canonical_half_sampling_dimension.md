# Unconditional dimensions of the actual stopped resampling iteration

The dimension theorem concerns the existing `canonicalHalfSampleTrimMatrix`
and its literal `canonicalHalfSampleTrimIterate`. It does not replace their
sample, fixed rectangular family, collective trim, or coordinate transport.
The input matrix may be arbitrary. No target, viability, spectral assumption,
positive rank, or successful-sampling premise is used.

A family of cardinality at most `D^2` maps the actual quotient sample into a
space of dimension at most half the input rank. The trim cannot increase
this dimension. The active output projection therefore has rank at most
half the input rank; below the stopping threshold the original matrix is
retained. The same argument includes `D = 0` and rank zero. A separate exact
range identity identifies the next matrix range, transported to native
coordinates, with the literal trim used in that round.

The existing integer stopped-halving theorem gives rank below any threshold
at least two after `R` prescribed rounds when the initial rank is at most
`2^R`. An initial bound `q^L` gives the prescribed count `q*L`. Both conclusions
hold for every entire seed sequence, including unsuccessful histories. These
are rank and round-count bounds, not viability, joint probability or
computational running-time theorems.

The proof reuses the exact dimension of the canonical range sample, the
matrix-product rank inequality, the finite-sup dimension bound, basis-independent
collective trimming, and `finrank_map_le`. All private checks use default
proof limits and immutable selected imports from the verified TNLean provider
`8f85b0be007c009ca208e82cbec4873dff2427e6`, whose own QICLean revision is
`cc2569b660d020e2946cdc979488d639add36d9f`, together with explicit fresh
objects for the pending stopped-iteration and rank-dependent sampling modules.
No cache or provider is written and no Mathlib source is compiled. Full
ordinary-library and compiled-blueprint checks remain part of integration.

The final separate-module check, refreshed against the complete stopped-iteration
object including seed-prefix dependence, passed in 5.615 seconds. An imported
inspection of all five public declarations passed in 4.801 seconds, with only
`propext`, `Classical.choice`, and `Quot.sound`. The temporary inspection source
was removed. Blueprint synchronization, import aggregation, proof-integrity,
reader-facing prose and whitespace checks passed.
