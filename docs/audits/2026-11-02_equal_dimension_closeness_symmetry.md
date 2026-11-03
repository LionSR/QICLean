# Equal-dimensional subspaces have symmetric closeness

The new theorem `Submodule.IsCloseTo.symm_of_finrank_eq` proves that equal
finite dimensions make the squared projection-loss bound symmetric, with
exactly the same error. It is stated for real or complex inner-product
spaces and every real error, including zero-dimensional subspaces.

For errors below one, the actual projection from the target to the
approximating space is injective and hence bijective. Choose its inverse
image of a vector and combine the original lower projection bound with
Cauchy–Schwarz. Errors at least one give the reverse inequality directly.
The proof uses existing Mathlib projection and finite-dimensional results;
it does not repeat the compression-inverse proof or assume a norm bound
for an inverse witness. This is an auxiliary geometric consequence of
ALVV's definition of closeness, not the final Ritz or algorithm theorem.

## Verification

The actual module was checked against immutable warmed TNLean `5fc343a57d`
and its own QICLean `ba01733099b` dependency. The final cleaned proof passed
strictly in 24.28 seconds; the earlier complete proof with three scalar
ring normalizations also passed in 41.018 seconds. Cleanup replaces those
normalizations by associativity and commutativity and uses the direct real
coercion power lemma. No timing-only repeat was performed.

The imported public theorem uses only `propext`, `Classical.choice` and
`Quot.sound`; its separate audit passed in 19.317 seconds. The temporary
inspection source was deleted. Selected source, object and root-input
hashes stayed fixed. The source-only worktree has no Lake directory;
no provider, cache or artifact was changed or copied, and Mathlib was not
rebuilt. Ordinary combined dependency and blueprint gates remain required.
A consumer with a source-changing override of the existing closeness
module must first re-elaborate this new importer against that override.
