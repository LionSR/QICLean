# The actual affine filter on the full ground space

The canonical isolated-ground spectral projection of a Hermitian matrix
is identified with the orthogonal projection onto its actual closed
low-energy eigenbasis span. The full multiplicity is retained; the span
may also be zero. No ground vector, rank-one projection or uniqueness
hypothesis is supplied.

For spectrum contained in {mu} union [E1,M], with mu<E1<=M, the actual
matrix B=(M I-H)/(M-mu) fixes the full original ground span and preserves
its orthogonal complement. Put c=(E1-mu)/(M-mu). The proof derives
0<c<=1 and ||Bx||^2<=(1-c)||x||^2 on the entire complement. It applies
the existing isolated-energy spectral-power theorem at exponent one;
no second spectral approximation theorem is introduced. There is no gap
cap or spatial rank hypothesis in this supporting matrix statement.

The original private functional-calculus-on-eigenbasis proof is extracted
from GroundProjection to the lower HermitianEigenbasisFunctionalCalculus
leaf. Its proof is preserved, with matrix names qualified. It imports
the existing TraceCFC matrix identities, which themselves import only
Mathlib. The original rank-one ground-projection theorem calls the shared
identity and retains its public statement unchanged.

## Verification

Actual modules were checked separately with package linter options and
warnings as errors against ordinary TNLean 1f0087d553cec4bf20448b0358489716cec64caf
and its own immutable QICLean package
099049ed6805334c6517c66b4b9858480bc7e9c7. Selected sources, objects, root
inputs and the prebuilt Mathlib object were guarded before and after.
The lower functional-calculus leaf passed in 4.356 seconds, the original
GroundProjection consumer in 4.782 seconds, and the actual full-ground
affine-filter module in 6.176 seconds over 17 selected source-object pairs.
An unchanged physical power-filter importer was also freshly elaborated
against the modified original consumer.

The three new public statements and the preserved original ground-projection
theorem passed an imported foundation inspection in 4.635 seconds over
30 selected pairs, using only propext, Classical.choice and Quot.sound.
The temporary inspection source was deleted; no permanent fixture is added.

The isolated source worktree has no Lake directory. No provider or cache
was modified, no artifacts were copied and Mathlib was not rebuilt.
Combined ordinary library, regression, compiled blueprint and timing checks
remain required after integration. The physical norm-scale construction,
actual collective trim iteration and same-root Ritz extraction remain
separate applications; this matrix auxiliary does not complete the source
algorithm or establish its running time.
