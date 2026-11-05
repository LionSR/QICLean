# Borel ordered frames for finite families and matrix ranges

The new `FiniteFrameMeasurable` module defines an actual ordered orthonormal
frame for every finite family whose span has dimension r. It applies the
existing normalized Gram–Schmidt map to all generators, removes the zero
vectors and enumerates the surviving indices in increasing order. The
resulting Fin r family is orthonormal and has exactly the original span.
Its dependence on the original family is Borel on each fixed-rank stratum.

The construction uses no arbitrary orthonormal-basis selector. In the
measurability proof, the domain is partitioned by its finite set of nonzero
Gram–Schmidt indices. Each piece is Borel, and on that piece the actual frame
is a fixed coordinate restriction of the normalized Gram–Schmidt map. The
existing Mathlib measurable-piecewise theorem is used only to prove this
explicitly defined frame measurable. The output itself remains the ordered
nonzero enumeration, rather than a newly chosen frame.

The algebraic assertions need no separability or measurability assumptions.
The Borel assertion is for separable real or complex inner product spaces.
Rank zero, empty inputs and dependent generating families are included. The
nonzero count equals the dimension of the original span, as derived from
Mathlib orthonormality, span preservation and dimension facts; it is not an
additional supplied condition in the public frame interface.

## Actual matrix-range specialization

`MatrixRangeFrameMeasurable` applies the same construction to the actual
Euclidean columns A(e_i). Its input is the rank-r finite complex matrix
stratum. The selected frame is orthonormal, spans exactly
range(Matrix.toEuclideanLin A), and is Borel as a vector family. The proof
uses Mathlib's basis-span identity, rank_eq_finrank_range_toLin and
continuous_uncurry_toEuclideanCLM. No parallel range projection is defined.
This works for every matrix of the stated rank, including non-Hermitian
matrices. In particular it provides the required frame on orthogonal
projection strata, including r=0 and empty ambient dimension.

These are mathematical prerequisites for ALVV arXiv:1602.08828v2, l:rs,
lines 530–558. No global continuity, jointly measurable adaptive tree,
finite-precision implementation or running time is asserted. The matrix
range frame is a Borel realization; its existence alone is not an efficiency
statement about operations on MPS representations.
