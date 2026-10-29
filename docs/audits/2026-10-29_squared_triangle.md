# Squared triangle inequality

The Mathlib-only leaf `QICLean/Analysis/NormSquaredTriangle.lean` exposes
`norm_sub_sq_le_two_mul_add` for a general seminormed additive commutative
group. It composes Mathlib's triangle inequality, monotonicity of squaring
nonnegative reals, and `add_sq_le`. No new tactic is introduced.

Three existing downstream AKLV calculations in TNLean's `Initialization`
and `VariableWindowRefinement` use this argument. Their refactor to the
shared inequality accompanies the next actual changing-target construction.
The generic inequality belongs in QICLean and has no TNLean dependency.
Keeping it in a separate leaf preserves the imports of the phase-distance
module.

The actual module passed a strict private check against the fully checked
QIC revision `4276de2eeb5c4122f4482ef5e4fa205be5b71bd9`, using the ordinary
objects in the fully checked TN mathematical snapshot
`da3ab8dcc9f9149cbbdcc56cae817ff783825f24` and its documentation-only successor
`f93bc77b3dddcc292125eea18b96af153225251b`. The exact source hash is
`8f01a0829125e1412ad5f625a203716dc5c41f907709892e55bd9e84dbcd6ed7`.
New objects were written only to a private temporary namespace; provider
sources and objects remained read-only. No Mathlib source was built and
no build artifact was copied. The imported foundation audit is kept under
the system temporary directory, outside the repository. It inspected the
new helper among 20 public declarations and found only the standard
foundations `propext`, `Classical.choice`, and `Quot.sound` (or a subset).

Ordinary build and compiled blueprint verification remain integration gates.
The new chapter may be placed with the elementary norm estimates in Chapter 1;
generated aggregators and chapter registration are excluded from this patch.
