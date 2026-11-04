# One scalar normalization identity for the affine filter

The existing normalization proof is factored into
`Matrix.normalized_affine_filter_eq_smul_raw`. The scalar identity needs
only a nonzero scale. The physical theorems still derive their positive
scale and denominator from the original data.

This is also the algebraic identity needed to compare the normalized
full-ground filter with the printed raw filter. Equality of the resulting
image subspaces uses Mathlib's nonzero-scalar invariance of submodule images.
It does not substitute separately chosen approximation subspaces.
