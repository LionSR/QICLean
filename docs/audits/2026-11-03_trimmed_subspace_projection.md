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

The private projection/range proof formerly in
`ViableSubspaceMeasurable` is moved, with its statement and proof unchanged
apart from visibility and namespace, into the thin Mathlib-only
`ProjectionMatrixRange`. Both the original true-closeness event and the
finite-span proof use the same public identity. The former module's three
public signatures remain unchanged and it has been freshly checked.

For orthonormal input bases, the prior actual basis-invariance theorem
identifies the result with the basis-independent trimmed subspace.
Identification with a particular Borel canonical frame and composition
with an adaptive sampling law remain separate consequences. No arbitrary
standard-basis measurability premise is assumed here. Source: ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655.

## Verification

The immutable provider was TNLean
`9ff185339e7556649699446504eda0c3e15bedf6` and its own QICLean package
`6878435c2a2483ba929687579b2575dd393d71bb`.
Strict actual-name checks passed with default options:

- `ProjectionMatrixRange`: 4.310 seconds, only Mathlib imports.
- `FiniteSpanProjectionMeasurable`: 4.668 seconds, 15 selected QIC pairs.
- `ViableSubspaceTrimmingProjectionMeasurable`: 4.852 seconds, 56 pairs.
- Refactored `ViableSubspaceMeasurable`: 4.870 seconds, two pairs.

Eight imported foundation inspections passed in 4.571 seconds with only
`propext`, `Classical.choice`, and `Quot.sound`. The temporary inspection
source was deleted. Selected sources, objects and build inputs were
guarded; all output objects are private. No shared cache mutation,
ordinary build or Mathlib source compilation was performed.

Reader registration, source synchronization, generated imports, prose,
pattern, integrity and whitespace checks are recorded in the external
manifest. The mathematical reader was rendered and visually inspected.
Canonical ordinary compilation and compiled blueprint checking remain
for coordinated integration.
