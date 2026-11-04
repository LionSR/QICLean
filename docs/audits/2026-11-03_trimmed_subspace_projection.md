# The actual trimmed-subspace projection is Borel

`Entropy.measurable_projectionMatrix_trimSubspace` proves global Borel
measurability of the ambient orthogonal projection onto the existing
`Entropy.trimSubspace`. Its input is the entire finite vector family.
The cuts, threshold and number of steps are fixed. No orthonormality,
independence, positive-threshold, monotone-cut, fixed-rank or nonzero
hypothesis is added. Empty families and zero-dimensional ambient spaces
are included.

The retained vectors are exactly the old construction's
`toEuclideanLin (trimProj D xi u k) (u i)`. Their finite span is exactly
`trimSubspace D xi u k`. The proof first establishes a general Borel
orthogonal projection onto the span of arbitrary finite vectors, then
composes it with the actual retained family. It introduces neither a
second trimming operation nor a second support projection definition.

## Generic span and range identities

`FiniteSpanProjectionMeasurable` regards each vector as an actual
one-column matrix. The existing `familySupportProj` has precisely their
joint column span, by the previously proved range chain. The standard
`WithLp.linearEquiv` transports the ordinary `mulVecLin` range to the
Euclidean `toEuclideanLin` range. Since the joint support is an orthogonal
projection, it equals the ambient orthogonal projection onto this actual
span. The existing support map is Borel, including at rank changes.

Both the original true-closeness event and the finite-span proof use the
same projection/range identity of `ProjectionMatrixRange`.

For orthonormal input bases, the prior actual basis-invariance theorem
identifies the result with the basis-independent trimmed subspace.
Identification with a particular Borel canonical frame and composition
with an adaptive sampling law remain separate consequences. No arbitrary
standard-basis measurability premise is assumed here. Source: ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655.
