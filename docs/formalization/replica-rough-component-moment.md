# A rough exponential estimate for an excitation component

Let the five distinct tensor factors be \(Q,Y,V,C,R\), and let \(\Omega\) be a
unit vector on \(Q\otimes Y\otimes V\). Suppose the original vector \(u\)
is fixed by simultaneous permutations of its physical, \(C\) and \(R\)
copy strings. For a set \(B\) of bad copies put \(m=|B^c|\) and
\(w=(R_B\otimes I)u\). Let \(\Gamma\) be the actual density retaining all
five factors on the good copies and tracing only the bad copies of this
same component. The component mass is \(M=\|w\|^2\).

For each indicated subsystem \(T\), let \(P_T^\lambda\) be the central
Schur-label projection for permutations of its \(m\) copies, and let
\(d_\lambda\) be the dimension of the corresponding irreducible
representation. Define

\[
\begin{aligned}
F_T&=\sum_\lambda (\log d_\lambda)P_T^\lambda,\\
G&=F_Q+F_V-F_Y,\\
D_C&=F_Q+F_C-F_{QC},\\
D_R&=F_V+F_R-F_{VR},\\
K&=\frac{(m+1)^{(|Q|\,|C|)^2}+(m+1)^{(|V|\,|R|)^2}}{2}.
\end{aligned}
\]

For every \(0\le a\le 1/2\),

\[
\operatorname{Re}\operatorname{Tr}\!\left(
\Gamma\exp\!\left[a(D_C+D_R-G)\right]\right)
\le K\|w\|^2=KM.
\]

Both actual merge deficits commute with \(G\), and the actual density is
supported on its closed nonnegative spectral subspace. Spectral compression
therefore removes \(G\) from the exponential trace. The actual two-merge
moment bounds the remaining trace by \(KM\). Positivity of \(G\) on the
whole space is not required.

The mass is retained literally, including zero components, zero copies and
an empty set of good copies. The support and moment identities are derived
for the actual density from the unit one-copy vector and the original
simultaneous permutation invariance.

This proves the rough exponential pairing used in the September 24, 2026
area-law manuscript, Section 7, lines 513–555. It remains an auxiliary
estimate before the inverse metric and the good auxiliary scalar factor
are introduced. It does not establish the full component inverse comparison.
