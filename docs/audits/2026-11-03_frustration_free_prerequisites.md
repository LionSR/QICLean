# Projection products and the spectral gap above a kernel

Four elementary results supply the finite-dimensional estimates used in
the frustration-free truncation argument of Arad, Landau, Vazirani and
Vidick, arXiv:1602.08828v2, Section 6.1. They are auxiliary results; they
do not by themselves establish the physical truncation or its rank bound.

For orthogonal projections \(h_k\), put
\(P_n=(I-h_{n-1})\cdots(I-h_0)\), with \(P_0=I\).
The fixed space of \(P_n\) is exactly \(\bigcap_{k<n}\ker h_k\),
without a commutativity assumption. The proof uses the existing identity
for the total squared norm removed by the complementary projections.

For pairwise commuting bounded operators, the complementary product
splits into the products selected by a predicate and its complement.
This identity does not require the factors to be projections.

For an orthogonal projection \(P\) and arbitrary vectors \(x,y\),
Pythagoras and contractivity give
\[
\|x-Py\|^2\le\|x-Px\|^2+\|x-y\|^2.
\]
Finally, if every nonzero eigenvalue of a Hermitian matrix \(A\) is at
least \(\gamma\), then
\(\gamma\|x\|^2\le\operatorname{Re}\langle x,Ax\rangle\)
for every \(x\perp\ker A\). The kernel may have arbitrary dimension,
and \(\gamma\) may have either sign.

These four completed proofs are extracted unchanged from QICLean revision
`e51354163d2dd9cf2a15d65722c544c6b4736182`. Their imports already exist on
main `c4576824`; no dependency or toolchain change is made. The corresponding
blueprint statements are included. The arguments reuse existing projection,
eigenbasis and complementary-product lemmas and introduce no repeated
proof pattern requiring a separate abstraction.

Mathematical revision `6730782c` passes the hosted full build, strict checks
and compiled blueprint declaration checks on Mathlib 4.36. The four exact
source proofs also pass strict read-only elaboration on Mathlib 4.35; each
of the four new declarations uses only `propext`, `Classical.choice` and
`Quot.sound`. The new mathematical statements compile as a PDF excerpt,
and their rendering has been inspected. Source synchronization, imports,
prose, whitespace and LaTeX lint checks pass. Hosted blueprint validation
is recorded in the pull request checks.
