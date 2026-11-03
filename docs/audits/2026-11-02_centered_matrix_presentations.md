# Canonical low-energy spaces of equal centered matrices

The new `Matrix.IsHermitian.spectralSpanLE_centered_ground_of_eq` applies
the existing centered-ground identity when a Hermitian matrix is presented
by an expression equal to $H-sI$. Equality elimination identifies the matrix
first; the existing theorem then identifies its canonical spectral spaces
for every real cutoff. Neither eigenvalue ordering choices nor selected
eigenvectors introduce an extra hypothesis. The original matrix minimum
is $E_0+s$, as certified by the actual normalized ground vector and
positive-semidefinite lower bound.

The existing scalar-shift declarations and proofs are unchanged. This
auxiliary supports the normalization across successive choices of regional
energy shifts in ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. It assumes no spectral gap or
simple spectrum. The nonempty index is the existing domain of the minimum
eigenvalue; the physical application derives it from the local dimension.

A strict actual-name check passed in 21.351 seconds against the verified
immutable TNLean hot provider `5fc343a57d70eefd2902780107851ab9b0753a82`
and its own QICLean package `ba01733099b5a18bed5c9bfb62f95f175b4c9b57`,
with the checked public coordinate exposure as an explicit override.
Selected source, object and package-input hashes were guarded. All output
is private. Ordinary integration and compiled blueprint checks remain
separate requirements.

The imported foundation inspection passed in 9.700 seconds jointly with
the actual physical corollary. Both declarations depend only on
propositional extensionality, classical choice and quotient soundness.
The temporary diagnostic source was deleted. Blueprint synchronization
and reverse coverage, prose, generated-import and whitespace checks pass.
