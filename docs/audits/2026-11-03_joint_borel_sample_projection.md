# Joint Borel projector of the existing canonical-frame sampler

The new result proves joint Borel dependence of the actual ambient matrix
of the existing `Submodule.randomSubspace` projection, with the constructed
canonical range basis, on a fixed-rank matrix and the coordinate unitary.
It does not introduce a different sampled-subspace definition or a separate
support projection.

## Exact geometric connection

For any fixed orthonormal basis b of a finite-dimensional subspace W, its
existing basis embedding is the finite ambient expansion
E_b(x)=sum_i x_i b_i. The existing randomSubspace b A U is exactly the span
of the retained rotated vectors E_b(Ue_j), j in A. Those vectors form an
orthonormal family, so its actual ambient starProjection is their rank-one
sum. These statements apply to every b, including the old standard-basis
specialization, and assert no varying-basis measurability.

The actual `rangeOrthonormalBasis P` restricts the ordered
range frame to the same matrix range. Its ambient coordinates are proved
equal to that frame. Thus the retained rotated vectors are exactly
z_j(P,U)=sum_i U_ij C(P)_i. The actual existing sampled projector has ambient
matrix sum_(j in A) z_j(P,U) z_j(P,U)*. This identity, rather than an assumed
range or projection formula, connects the Borel calculation to the sampler.

The frame coordinates are Borel, the unitary entries are continuous, and
finite sums, scalar products and conjugation preserve measurability. This
proves joint Borel measurability on the product of the rank-r matrix stratum
and U(r). The matrix need not be Hermitian; the selected basis spans its
actual range. The retained coordinate set A is fixed on that stratum, so
it includes the first min(s,r) coordinates. Rank zero, s=0, empty retained
sets and empty ambient dimension are included.

## Reuse and scope

The proof reuses Mathlib `OrthonormalBasis.span`,
`OrthonormalBasis.starProjection_eq_sum_rankOne`, `sum_repr_symm` and
`symm_toEuclideanLin_rankOne`. It uses the existing QIC randomSubspace,
basisEmbedding, coordinateSubspace and unitaryAction definitions unchanged.
The range-basis constructor uses `OrthonormalBasis.mk`, with the existing
proved frame's orthonormality and exact span. No arbitrary basis selector
is asserted measurable.

This supports ALVV arXiv:1602.08828v2, l:rs, lines 530–558, as one fixed-rank
sampling prerequisite. No comparison of Haar laws under basis changes,
measurability of the old arbitrary varying-basis function, adaptive tree
probability, finite-precision implementation or running time is proved here.
The joint matrix-projector statement concerns ambient coordinates, not a
measurable dependent space of basis objects.
