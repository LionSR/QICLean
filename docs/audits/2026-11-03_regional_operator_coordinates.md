# Regional operators in tensor coordinates

`Entropy.regionTensorCoordinates_conjugation_localLift` identifies the
identity extension of an arbitrary regional matrix with that matrix tensored
with the environmental identity, in the actual canonical regional tensor
coordinates. `Entropy.localLift_middleFirst_conjugation` records the same
identity in the explicit exterior-first coordinates followed by tensor
exchange. Both forms have active consumers: the explicit form preserves an
existing dependent-coordinate statement in TNLean, while the canonical form
is used by regional energy arguments. Neither requires positivity or nonzero
local dimension.

The two coordinate calculations formerly private to TNLean's native regional
energy estimate are moved here, with the finite site set generalized from
Fin L to an arbitrary finite type. The entrywise calculation remains private.
The explicit conjugation proof is reused once; the canonical theorem follows
by the existing equality of the two coordinate maps. An obsolete final case
split is removed because the preceding simplification closes that goal.
The existing entry formula belongs to RegionUnion, which is explicitly
imported. There is no TNLean dependency and no new functional-calculus
calculation.

The TNLean consumer removes its old private definitions and calls the shared
explicit-coordinate theorem. Its public statement is byte-identical; its
remaining proof is unchanged. This supports the actual tensor-coordinate
variational argument, rather than introducing a different coordinate model.

The generic module passed strict private checking in 10.031 seconds and its
old physical consumer in 12.746 seconds, at default budgets. The imported
foundation audit covers both public coordinate identities and that consumer,
with only propext, Classical.choice and Quot.sound. Provider TNLean
e2706cbe715c49745d4399d37dabe3d2559cc494 and its own QICLean
de8a9d1286709f39d8c37d4d52d6e336925863e5 were immutable; selected source,
object, build-input and prebuilt Mathlib hashes were guarded. All new objects
and temporary foundation commands remain under /tmp. No provider or shared
cache was changed and no Mathlib source was built. Exact hashes and logs are
recorded in the manifest. Ordinary combined and compiled blueprint checks
remain required after adoption.
