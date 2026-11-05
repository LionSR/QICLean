# Canonical low-energy spaces of equal centered matrices

The new `Matrix.IsHermitian.spectralSpanLE_centered_ground_of_eq` applies
the existing centered-ground identity when a Hermitian matrix is presented
by an expression equal to $H-sI$. Equality elimination identifies the matrix
first; the existing theorem then identifies its canonical spectral spaces
for every real cutoff. Neither eigenvalue ordering choices nor selected
eigenvectors introduce an extra hypothesis. The original matrix minimum
is $E_0+s$, as certified by the actual normalized ground vector and
positive-semidefinite lower bound.

This auxiliary supports the normalization across successive choices of
regional energy shifts in ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. It assumes no spectral gap or
simple spectrum. The nonempty index is the existing domain of the minimum
eigenvalue; the physical application derives it from the local dimension.
