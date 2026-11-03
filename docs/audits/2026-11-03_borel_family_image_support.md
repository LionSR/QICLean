# Borel joint supports and exact operator-image ranges

The new `MatrixFamilySupportMeasurable` module proves Borel measurability of
the existing `Matrix.familySupportProj` on all finite rectangular complex
matrix families. Its actual represented range is proved equal both to the
range of the stacked column matrix and to the sum of the family ranges.
No new support or sampled-subspace definition is introduced.

The Borel proof uses the pointwise identity

    familySupportProj A = I - GE(familyColumnGram A,0) GE(-familyColumnGram A,0).

The actual Gram matrix is positive semidefinite. The existing Hermitian
support identity therefore gives this equality, and the established whole
matrix Borel cutoff theorem applies after the continuous Gram map. This
avoids unfolding the arbitrary spectral-coordinate construction in a
higher-order definitional equality. No desired measurability premise is
supplied.

An earlier direct composition exhausted the unchanged 200,000-heartbeat
normalization budget. Its source and diagnostic were preserved in the
private diagnostics directory, and the original untracked handoff source
was left unchanged in its worktree. The pointwise cutoff proof succeeds
with the default options. Only local decidable equalities for the family
and column indices are used where needed for the measurable topology;
the ambient-row decidable equality is not overridden. No budget was raised.

## Actual represented ranges

Absorption gives Q C=C for the actual support Q and stacked columns C.
The existing support factorization gives Q=(C C*)T=C(C*T). These prove both
range inclusions without assuming a missing rank or range theorem. The
columns of C are the union of the columns of the family members; span of
a union is the sum of the spans. Thus

    range(familySupportProj A) = range(familyColumns A) = sum_i range(A_i).

For a fixed family F_i, the same existing projector of the products F_i P
is Borel in every input matrix P and has exactly the range
sum_i F_i(range P). With P the orthogonal projector onto S, this is the
actual projector onto sum_i F_i S. The product is a continuous family map,
and the range identity uses the existing linear-map composition theorem.

All statements include zero and empty families and zero-dimensional input
or output spaces. No rank, nonzero or spectral-separation hypothesis is
added. These are mathematical prerequisites for the improving-family image
in ALVV arXiv:1602.08828v2, l:er, lines 597–622. They assert neither an
adaptive tree probability nor a running time.

## Verification

The isolated source-only worktree is based on frozen QIC
fd3a102b883f494ad70bf787bc51436cb197aab0. Private verification used immutable
TN e2706cbe715c49745d4399d37dabe3d2559cc494 and its own QIC
de8a9d1286709f39d8c37d4d52d6e336925863e5, with the exact checked cutoff
source/object override. The complete module passed strict checking in
4.422 seconds with thirteen protected source/object pairs. All eight public
declarations passed an imported foundation inspection in 4.293 seconds with
fourteen protected pairs; only propext, Classical.choice and Quot.sound were
reported. The temporary inspection source was removed.

Source blueprint synchronization, generated imports, reader-facing prose,
proof-token and whitespace checks pass. The existing mathematical source,
provider objects, dependency cache and Mathlib source were unchanged.
Ordinary compiled-library and blueprint checks remain integration gates.
