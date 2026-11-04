# Support projections and finite-dimensional estimates for area laws

This submission extracts completed auxiliary results used in the AKLV and ALVV
area-law developments. It builds on the normalized-filter results of QICLean
PR #1006; its pull-request diff contains only the additional estimates.

For a positive contraction A, its spectral range projection P satisfies A ≤ P.
Replacing every summand of a finite positive family by its range projection
preserves the kernel of the sum. These are the finite-dimensional steps in
ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460.

For an operator supported on X in a finite tensor product, its operator
Schmidt rank across A and its complement is bounded by the minimum of the
squares of the configuration dimensions on X intersect A and X minus A.
For uniform local dimension q ≥ 1, this is at most q to the cardinality of X.
The proof exchanges the two tensor factors and applies the existing support
bound on both sides. No Hermiticity or positivity assumption is added.
This estimate supports ALVV's local operator expansion, `eq:rho-expansion`,
lines 1971–2013.

The Euclidean spectral-theorem identity is stated as a continuous linear
map equation. Two existing auxiliary proofs are made public: an attained
positive lower bound identifies the canonical least eigenvalue, and scalar
multiplication of a vector scales its rank-one matrix by the squared scalar
norm. Their proofs and existing callers are unchanged.

The transpose identity for the range projection reuses the new functional
calculus identity. Current-main matrix reindexing definitions are retained.
Verification results are recorded in the pull request.

## Verification

The targeted Lake build passed (3,225 jobs). Six principal results were checked
with `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` occur.
Blueprint/source synchronization, active mathematical references, generated
imports, and proof-token and file-length checks pass. Strict elaboration
results are recorded in the pull request.
