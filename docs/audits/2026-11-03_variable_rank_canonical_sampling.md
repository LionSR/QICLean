# Canonical sampling across matrix-rank changes

The actual canonical-basis random-subspace sampler is now Borel on one
fixed finite unitary product, including at changes of the candidate rank.
This is a prerequisite for adaptive sampling, not its probability theorem.

For ambient dimension d, the product has one U(r) coordinate for each
0 ≤ r ≤ d. A candidate matrix P uses its actual rank coordinate and the
canonical Borel orthonormal basis of its actual range. The retained
coordinate set is the first min(s, rank P) coordinates. The construction
is literally the existing basis-parametrized randomSubspace, as shown by
the exact restriction identity on every rank stratum. Rank zero and s=0
are allowed. No Hermitian or projection hypothesis is needed on P.

Matrix rank is Borel by the existing lower-semicontinuity theorem. Borel
restrictions on the rank strata glue by a countable measurable partition.
The fixed-rank canonical-sampler theorem then proves joint measurability
of the actual ambient projection. Composing with the existing joint
column support proves that the actual finite-family image projection is
also Borel. No arbitrary varying orthonormal-basis selection is used.

The source motivation is ALVV, arXiv:1602.08828v2, Lemma l:rs, lines
530–558. This auxiliary does not establish an adaptive success probability,
a runtime estimate, or finite-precision implementation. Those require the
actual composite node map and a separate conditional probability argument.
