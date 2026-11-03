# Normalized orthogonal projections from close subspaces

The contribution is based on QICLean `ba01733099b5a18bed5c9bfb62f95f175b4c9b57`.
For a unit target vector, closeness with error δ < 1 makes its orthogonal
projection nonzero. The normalized projection has squared overlap at least
1 − δ, a nonnegative real inner product with the original vector, and squared
distance at most 2δ. Its equality to the normalized actual projection is
retained in the conclusion.

The former private projection proof is reused in
`Analysis/ViableSubspaceUnitApproximation.lean`. The Schmidt-rank argument
calls this public theorem; its three public statements are unchanged. No
Hamiltonian, gap, rank or algorithmic assumption is introduced.

## Verification

The new theorem and the affected Schmidt-rank module passed strict private
compilation in 20.271 s and 19.465 s. The provider was the immutable warmed
QICLean revision `24a2ee589c5ff8da34a5cc6d8b7026dc7700e929`. Every selected
reused dependency source, together with the toolchain, manifest and package
configuration, was checked byte-identical to the declared base. The current
error-reduction, spectral-projector and coordinate modules were compiled
separately as explicit private dependencies, including unchanged importers
above changed source. Their times were 38.644 s, 38.157 s and 34.939 s.
All selected source, object and input hashes remained unchanged during each
check. Mathlib was neither rebuilt nor modified.

An imported inspection of the new theorem and all three public Schmidt-rank
consequences reported only `propext`, `Classical.choice` and `Quot.sound`.
The temporary inspection source was deleted after the check. No test or
foundation inspection fixture is added to the library. The coordinated ordinary
library and compiled-blueprint checks remain to be run before integration.
