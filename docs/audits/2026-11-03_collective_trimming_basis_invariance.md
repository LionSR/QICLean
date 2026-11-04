# Basis independence of collective trimming

ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655,
starts with an orthonormal basis of the input subspace. The new theorem
`Entropy.trimSubspace_eq_of_orthonormalBasis` proves that the literal
successive construction produces the same subspace for any two finite
orthonormal bases of that same subspace.

## Mathematical argument

The physical left marginal of the stacked vector is the sum of the
rank-one operators of its columns. After any physical operator `P`,
the cut marginal equals the regional partial trace of `P * Gram * Pᴴ`.
Consequently two families with equal original Gram operators give exactly
the same successive products of trimming projections, by induction.
This does not require a positive threshold or monotone cuts. For an
orthonormal basis of `S`, Mathlib's sum-of-rank-one formula identifies
that Gram operator with the orthogonal projection onto `S`. The actual
trimmed span is the image of `S` under the literal trimming product,
which therefore depends only on `S`. The zero subspace is included.

No new invariance hypothesis is assumed, and neither the trimming
algorithm nor its threshold convention is changed. This is an algebraic
result; measurability and conditional adaptive probability remain
separate consequences to be proved using a measurable choice of frame.
