# Centered Schur-label moments

Let a finite group act by permutations and let a positive semidefinite matrix
\(\rho\) commute with that action. Write \(F\) for the logarithmic
irreducible-dimension observable and \(L=-\log\rho\), evaluated on the support
of \(\rho\) and equal to zero on its kernel. For any real center \(s\), put
\(M_A(t;s)=\operatorname{ReTr}(\rho e^{t(A-sI)})\).

If \(\operatorname{Tr}\rho=1\), then \(M_F(u;s)\le M_L(u;s)\) for
\(u\ge0\). The comparison uses the actual joint resolution: a positive
eigenvalue \(r\) on a nonzero irreducible component satisfies
\(rd_\lambda\le1\). Thus \(\log d_\lambda\le-\log r\) on that component.
Zero eigenvalues contribute zero trace weight, so no full-space comparison
of \(F\) and \(L\) is required.

Without a trace-normalization or sign condition on \(u\),
\[
M_F(-u;s)\le\sqrt{M_L(-2u;s)\operatorname{ReTr}(\rho e^{2u(L-F)})}.
\]
This follows by applying the weighted commuting trace inequality to
\(-2u(L-sI)\) and \(2u(L-F)\), whose average is \(-u(F-sI)\).

For the actual copy-permutation action on \(Q^{\otimes k}\), with
\(q=\dim Q\), a permutation-invariant density matrix and \(0\le u\le1/2\),
\[
M_F(u;s)\le M_L(u;s),\qquad
M_F(-u;s)\le\sqrt{(k+1)^{q^2}M_L(-2u;s)}.
\]
The polynomial follows from the proved Schur remainder moment at \(2u\).
These are transfer estimates from actual surprisal moments to actual label
moments, as used in the September 24, 2026 area-law manuscript,
[Section 7, lines 227–237](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/07-comparators.tex#L227-L237).
The quantitative centered-surprisal moment bounds and their application to
the iid regional marginals are separate obligations. No resulting label
moment-growth bound is assumed here.
