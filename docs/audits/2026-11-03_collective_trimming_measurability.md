# Borel measurability of collective trimming projections

`Entropy.measurable_trimProj` and `Entropy.measurable_trimStep` prove
that the literal successive collective-trimming products and individual
spectral cut projections are Borel functions of the entire input family.
The threshold, cut sequence and number of steps are fixed. The family
need not be orthonormal or linearly independent. Empty families, zero
vectors, arbitrary real thresholds and arbitrary cut orders are included.

The proof retains the original definition in ALVV, arXiv:1602.08828v2,
Definition `def:trimming`, lines 648–655. It uses the original stacked
Gram operator, whose entries are continuous finite sums, and the exact
cut-marginal identity from `ViableSubspaceTrimmingInvariance`. At each
step the current product conjugates that Gram operator; regional partial
trace is continuous. The fixed closed spectral cutoff is Borel by
`Matrix.measurable_spectralProjectionGE`, including at a threshold
eigenvalue. The local lift is continuous, so literal induction proves
measurability of the next product.

No eigenbasis is selected in this proof, and no measurability hypothesis
is assumed for the output projections. This does not yet prove
measurability of the final trimmed-subspace projector or a conditional
adaptive sampling law.
