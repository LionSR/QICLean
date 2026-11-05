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
collective trimming, and `finrank_map_le`.
