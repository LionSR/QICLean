# Nested-target image composition and approximation helpers

`Submodule.viable_enlargement_of_close_nested_targets` is a conditional
finite-dimensional implication. It retains the actual image of one
prescribed initial space under one prescribed improving operator family.
It assumes the two target comparisons and the improving property, and does
not assert physical existence of that family. For `0 < delta <= 1`, the
comparison losses `delta/100` give initial error at most `1/20`, refined
error at most `delta/5`, and final error at most `21 delta/50 <= delta/2`.
The image dimension is bounded by the number of operators times the actual
initial dimension. Physical callers must derive the assumed family and
comparisons separately.

The normalization-distance proof used by several TNLean
approximation arguments is placed in the Mathlib-only module
`UnitNormalizationDistance`. Its root-namespace public identity is
`norm_inv_norm_smul_sub_le_two_mul`. It applies to every complex normed
space, unit reference vector and nonzero unnormalized vector.

`LogRankRounding` contains two scalar proofs from
TNLean's gapped global approximation:
`Nat.le_mul_ceil_exp_of_log_le` and
`Real.log_ceil_exp_le_add_one`. These proofs require no Hamiltonian,
spectral projector, tensor decomposition or target subspace.
