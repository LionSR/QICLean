# Residual comparisons relative to the actual least energies

A residual on a matrix's actual low-energy space controls the displacement of its least energy. Two residuals then give both directed spectral comparisons at cutoffs measured relative to the respective true ground energies. No order relation, spectral gap, ground-space dimension, supplied basis or spectral comparison is assumed in these matrix lemmas.

For Hermitian matrices with least energies \(a,b\), a residual bound \(\|(A-B)|_{G_B(\eta)}\|\le\xi\) gives \(a-b\le\xi\) whenever \(\eta\ge0\). The proof chooses a canonical unit ground eigenvector of the second matrix, proves its membership in its actual spectral window, and applies the first matrix's positive lower bound and Cauchy–Schwarz. Mathlib's equivalence between positive matrices and positive Euclidean linear maps supplies the quadratic-form inequality.

If both residuals are at most \(0<\xi\le1\), the least energies differ in absolute value by at most \(\xi\). For positive bandwidth, \(\xi\le w/2\), and the explicit counting budget \(2(\eta+2)\xi\le\delta w^2\), the finite-window perturbation theorem gives both directed comparisons. Its denominators are \(w-(a-b)+\xi\) and \(w+(a-b)+\xi\), each at least \(w\). The numerator uses \(N=\lceil\eta/(2\xi)\rceil\) and \(N(2\xi)^2\le2\eta\xi+4\xi^2\le2(\eta+2)\xi\). No subspace inclusion is inferred from matrix order.

The scalar order theorem chooses

\[
m=\left\lceil35+2\eta+16\log(80/\rho)\right\rceil
\]

for \(\eta\ge0\) and \(0<\rho\le1\). It proves the scalar correction \(\alpha=(m/2)2^{-m}\le1/4\), the cutoff condition \(m/2\ge17+\eta+\alpha\), and residual budget \(80\exp((17+\eta+\alpha)/8-m/16)\le\rho\). The order is independent of all physical data. The natural power bound is taken from Lean's existing \(k<2^k\) inequality; no duplicate induction is introduced.

## Reused scalar count and canonical-ground identity

The ceiling-count estimate is also shared rather than copied a third time. Its Mathlib-only analysis module supplies the sharp count and the existing coarser scalar budget. The two former private budget copies in TNLean’s physical low-energy closeness and filter-family modules are removed; their signatures and constants are unchanged. The new comparison uses the same sharp count. The tactic-pattern ledger records this promotion.

## Canonical-ground identity

The existing theorem identifying the canonical minimum from an attained centered ground vector is made public in its original analysis module. Its source file differs only in the removal of the private visibility modifier; this was checked byte for byte. The proof is unchanged. Physical callers can consequently identify the minima supplied by their actual normalized witnesses without repeating the eigenvalue argument.

## Source and scope

These are supporting matrix and scalar estimates for ALVV, arXiv:1602.08828v2, the finite-window argument following `lem:hard-trunc` (lines 955–968) and the corrected exponential-moment route following `lem:exp-approx` (lines 1195–1255). They do not assert the false first uniform energy estimate. The scalar profile concerns equal scale and order; physical applications must derive their actual residual bounds. The directed finite-window theorem requires positive bandwidth, while the ground-displacement bound allows zero bandwidth. No source gap prescription, efficient representation or low-density/tree induction is established here.

## Verification

The source-only branch is based on checked QICLean `34cb0c3a24a9cfb8073e1fe7bb1087bc409fb951`. Private strict checks imported the ordinary objects of that exact read-only provider, with temporary outputs for the changed modules and source/object guards before and after elaboration.

- `GroundEnergyBounds`: 12.95 seconds; SHA-256 `3150288f60d02589388d286869172fbe0f02aed9d7770357e1d11635e58a61a0`.
- `SpectralResidualGroundEnergy`: 4.332 seconds; SHA-256 `9b057b6311e725759b209f7ebc874b707ceedff809fb31b7312f40ad0d519f34`.
- `SpectralResidualComparison`: 6.233 seconds; SHA-256 `37a39612e4bf105a8ab5b18c5712daf506709f70fbadf602d52bc8eaea411617`.
- `SoftTruncationAccuracy`: 4.24 seconds; SHA-256 `9fc4a394168a92c2bc876932c08f5118b317f353bee8265e5729822019072abe`.
- `SpectralWindowCount`: 2.477 seconds; SHA-256 `cd7aee25c1d8f918eead4fd85f2e92c298a1b7881dcb2b4e8f0c78fd0d4cbdc5`.
An imported-object foundation audit checked all six public declarations, including the promoted identity. Every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. The evidence records are `/tmp/qiclean-alvv-soft-spectral-comparison-checks.json` and `/tmp/qiclean-alvv-soft-spectral-comparison-foundations.json`.

No local Lake environment was initialized, no dependency artifact was copied or changed, and no Mathlib source was compiled. The ordinary common build and compiled blueprint checks remain integration gates.
