# Ground-state factors of exact excitation components

The source is Section 7, lines 441–456 of OpenAI's September 24, 2026
area-law manuscript at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The exact-excitation projection has the ground-complement projection on the
coordinates in B and the rank-one ground projection on the coordinates in
its complement. Expanding these actual rank-one factors gives the prescribed
ground vector on each good physical copy.

The remaining vector is defined by partial contraction against those ground
vectors. It keeps every bad physical coordinate and the entire auxiliary
coordinate. The existing finite-product coordinate equivalence gives the
canonical split; no second coordinate equivalence is introduced. The number
of good coordinates is k minus the cardinality of B, including the empty
and full regions.

The component factorization is derived directly from the actual projection.
The fixed-sector version assumes only that this projection fixes the vector.
It does not assume a product representation, a desired range inclusion, or a
chosen remaining factor. Ground-state normalization makes the contraction
recover the remaining vector and proves equality of norms. The zero vector
and zero-copy case are included without division by the component norm.

The auxiliary basis type is arbitrary and may represent all whole-copy
Schur labels and every other auxiliary factor. Nothing is contracted on
that coordinate. Permutation invariance, Schur-sector compatibility and the
subsequent metric comparisons are distinct statements and are not asserted
by this module.

All new mathematical proofs are independently written. The prior replica,
spectral cutoff and excitation-sector modules are used without alteration.
