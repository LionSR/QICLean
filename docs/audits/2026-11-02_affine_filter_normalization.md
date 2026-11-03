# One scalar normalization identity for the affine filter

The existing normalization proof is factored into
`Matrix.normalized_affine_filter_eq_smul_raw`. Both physical spectral-power
consumers call the shared identity, and retain their public statements.
The scalar identity needs only a nonzero scale. The physical theorems
still derive their positive scale and denominator from the original data.

This is also the algebraic identity needed to compare the normalized
full-ground filter with the printed raw filter. Equality of the resulting
image subspaces uses Mathlib's nonzero-scalar invariance of submodule images.
It does not substitute separately chosen approximation subspaces.

## Verification

The three actual changed sources passed strict private checks against
immutable TNLean 1f0087d553cec4bf20448b0358489716cec64caf and its own
QICLean 099049ed6805334c6517c66b4b9858480bc7e9c7, with selected source,
object, root-input and prebuilt Mathlib hashes guarded before and after.
The shared matrix module passed in 5.642 seconds, the attained-gap consumer
in 5.069 seconds, and the lower-gap consumer in 5.590 seconds. The complete
selected importer chain was re-elaborated in dependency order.

An imported foundation inspection covers the new identity and all five
preserved public physical-power statements and passed in 4.373 seconds
over 32 selected source-object pairs, using only propext, Classical.choice
and Quot.sound. The temporary source was deleted. No permanent fixture, Lake directory or copied artifact is
introduced. No provider/cache is modified and Mathlib is not rebuilt.
Combined ordinary gates remain required after integration.
