# The actual full good-copy density

Let the five finite factors be Q, Y, V, C and R, in that order. The physical
one-copy space is Q tensor Y tensor V. For an arbitrary original vector u,
form the actual excitation component w = (R_B tensor I)u. Retain all five
factors on the good copies and trace only the bad physical and auxiliary
copies. The resulting unnormalized density retains every good Y coordinate.

The coordinate equivalence groups the physical copies first and the C and R
copy registers second. The same chosen finite-set enumeration of the good
copies is used in each factor. It need not be an increasing enumeration.
The definition constructs the retained and discarded vector directly from
w and takes its literal rank-one partial trace.

When the one-copy ground vector is unit, the physical-only symmetrizer fixes
this actual density. The proof derives the permutation and symmetrizer
transport through the explicit five-factor equivalence. It then traces the
bad auxiliary copies in the earlier physical-support identity. Multiplication
by a physical operator passes through that auxiliary trace by interchanging
finite sums. There is no symmetry, normalization or nonzero assumption on u,
and no supplied coordinate or support identity. Zero components, zero copies
and empty good sets are included.

The three declarations are `TensorPower.fiveFactorCopiesEquiv`,
`Matrix.replicaGoodConfigurationMarginal` and
`Matrix.symProj_mul_replicaGoodConfigurationMarginal`. The compatible physical
spectral projection is separate. Identifying the further marginal obtained by
tracing the good Y coordinates is also a separate assertion.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 23 and 103–110 for the independent physical
factors, lines 513–517 for physical symmetric support, and lines 520–549 for
the actual product-density argument.
