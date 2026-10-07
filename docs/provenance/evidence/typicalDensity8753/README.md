# Density matrices restricted to a typical spectrum

The independently written formalization connects the typical-Schmidt estimates
`comparator:typical-entropies` to actual positive matrices. The source is OpenAI's
September 24, 2026 manuscript, *A two-dimensional area law from a global spectral
gap*, at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`build/sections/07-comparators.tex`, lines 39–55.

Let \(\rho\ge0\), let \(S=S(\rho)\), and choose eigenvalue indices \(E\) with
positive selected mass \(z=\sum_{i\in E}p_i\). Their eigenvectors determine an
orthogonal projection \(P_E\), commuting with \(\rho\). The actual matrix
\(\rho_E=z^{-1}P_E\rho P_E\) acts on the original Hilbert space, is positive,
and has trace one. For positive selected eigenvalues its rank is \(|E|\), and its
von Neumann entropy is the Shannon entropy of \((p_i/z)_{i\in E}\).

Under precisely the source's selected spectral window,
\(e^{-S-w}\le p_i\le e^{-S+w}\), the matrix theorem proves

\[
|\log\operatorname{rank}\rho_E-S(\rho)|\le w+|\log z|,
\qquad |S(\rho_E)-S(\rho)|\le w+|\log z|.
\]

Zero eigenvalues outside the selected set are allowed. For an original
trace-one density matrix, the selected mass is at most one; the entropy and rank
estimates also hold for arbitrary positive matrices satisfying the same window.
The construction selects eigenvalue indices rather than distinct eigenvalues,
so it allows choices within a degenerate eigenspace.

The proofs use the existing spectral theorem, preservation of rank under
invertible multiplication, and unitary invariance and the diagonal formula for
von Neumann entropy. They then apply the independently proved scalar
typical-spectrum theorem. They do not assume an entropy inequality for the
restricted matrix, construct the typical set from a physical gap, or prove the
auxiliary Schur-sector or norm comparisons of Proposition 8.1.

The proofs and account were prepared with OpenAI Codex. No upstream OpenAI Lean
proof text was read, copied, or adapted for these declarations. Human
mathematical review remains required.

The module build and every exported theorem's axiom audit are recorded in
`build.log` and `axioms.log`. Full-library and global blueprint verification are
performed in the combined integration branch. The new blueprint fragment is
`ch12_entropy_typical_density.tex`; its inclusion and the root import are left
to that coordinated integration.
