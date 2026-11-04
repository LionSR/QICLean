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

The finite site set is an arbitrary finite type rather than Fin L. The
explicit conjugation proof is reused once; the canonical theorem follows
by the existing equality of the two coordinate maps. This supports the
actual tensor-coordinate variational argument, rather than introducing a
different coordinate model.
