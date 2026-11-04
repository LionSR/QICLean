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
