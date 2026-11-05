# Borel closed cutoffs and Hermitian range projections

The new `SpectralProjectionMeasurable` module proves Borel measurability of
the existing `Matrix.spectralProjectionGE` at each fixed real threshold. It
also proves Borel measurability of the existing Hermitian `supportProj` on
the Hermitian matrix subtype. Both refer to the actual library definitions.

## Proof and endpoints

The scalar functions max(0,min(1,1+k(x-a))) are continuous. For x at or above
a they equal one for every k; below a they equal zero once k is at least
ceil(1/(a-x)). Every finite spectrum therefore has one common stabilization
index. The matrix functional calculi eventually equal the closed cutoff
exactly, rather than merely converge approximately. Mathlib continuity of
functional calculus and measurability of sequential limits prove the result.
No threshold-eigenvalue exclusion or fixed-rank hypothesis is introduced.

The whole-matrix Borel statement uses the existing functional calculus value
zero on non-Hermitian inputs. This convention is explicit in its signature
and documentation. The range-projection formula, in contrast, retains the
Hermitian hypothesis:

    supportProj(A) = I - spectralProjectionGE(A,0) spectralProjectionGE(-A,0).

The product is precisely the zero-eigenspace projection. This identity is not
asserted for non-Hermitian matrices, where the two cutoff values would both
be zero. The range-projection measurability theorem is on the Hermitian
subtype. Zero matrices, arbitrary multiplicity at zero and empty finite index
sets are included throughout.

## Scope

These are mathematical prerequisites for ALVV, arXiv:1602.08828v2,
`def:trimming`, lines 646–655. They do not choose a measurable varying
orthonormal basis, prove measurability of the complete collective-trim map,
construct a joint adaptive sampling law, or establish a running time. In
particular, no pointwise measurable hull of a sampling event is treated as a
joint measurable family.
