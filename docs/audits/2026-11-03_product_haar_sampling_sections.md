# A fixed Haar product law and exact input failure sections

`Matrix.rankUnitaryHaar d` is the finite product of the existing Haar
probability measures on `unitaryGroup (Fin r)`, for every `r <= d`.
Its domain is exactly the existing `Matrix.rankUnitaryProduct d`.
It is a probability measure fixed before the input matrix, and every
coordinate evaluation is measure preserving with the exact existing
Haar marginal. The zero-dimensional unitary factor is included.

The arbitrary-basis section theorem instantiates the existing corrected
random-subspace estimate using the rank coordinate of this same product.
It assumes only the old input viability, and keeps the actual rank,
sample size and target dimension in the failure bound. The matrix
specialization concerns the literal existing `randomRangeSubspace P s U`,
with actual rank `q = P.rank` and actual sampled size `a = min s q`.
It proves the true failure-section bound with error
`1 - (1 - delta) * a / (8 * q)` and corrected probability
`(1 + 2 / sqrt((1 - delta) * a / (8 * q)))^(2 * dim T) * q * exp(-a/16)`.
The Lean statement retains the old theorem's unrestricted real-error
and zero-rank conventions; it adds no sampling-probability premise.

The proof uses `MeasurePreserving.measure_preimage_le`, which holds for
arbitrary sets. It therefore does not assert equality of measures for
an unproved measurable failure set. The existing Haar theorem remains
responsible for the corrected measurable net-event cover; no new hull
or alternative success predicate is introduced. Borel measurability of
the actual sampled, improved and trimmed output events is a separate
proved ingredient before a later Fubini composition. No uniform bound
over unrelated ranks or adaptive high-probability conclusion is claimed.

When the requested sample size reaches the actual rank, the literal
clamped sample equals the entire original range for every seed, including
rank zero. This follows from actual inclusion and equality of dimensions.

Source: ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558. The inherited
correction to the printed sphere-net cardinality is recorded in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
