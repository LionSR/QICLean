# The actual affine filter on the full ground space

The canonical isolated-ground spectral projection of a Hermitian matrix
is identified with the orthogonal projection onto its actual closed
low-energy eigenbasis span. The full multiplicity is retained; the span
may also be zero. No ground vector, rank-one projection or uniqueness
hypothesis is supplied.

For spectrum contained in {mu} union [E1,M], with mu<E1<=M, the actual
matrix B=(M I-H)/(M-mu) fixes the full original ground span and preserves
its orthogonal complement. Put c=(E1-mu)/(M-mu). The proof derives
0<c<=1 and ||Bx||^2<=(1-c)||x||^2 on the entire complement. It applies
the existing isolated-energy spectral-power theorem at exponent one;
no second spectral approximation theorem is introduced. There is no gap
cap or spatial rank hypothesis in this supporting matrix statement.

The physical norm-scale construction, actual collective trim iteration and
same-root Ritz extraction remain separate applications; this matrix
auxiliary does not complete the source algorithm or establish its running
time.
