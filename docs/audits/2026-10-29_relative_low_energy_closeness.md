# Relative low-energy closeness from actual restricted residuals

Source: ALVV, arXiv:1602.08828v2, Lemma 4.5 (`lem:hard-trunc`), proof at
`local_alg_arxiv_v2.tex:955–968`, and the existing correction note
`docs/paper-gaps/alvv16_hard_truncation_windows.tex`.
Primary source: <https://arxiv.org/html/1602.08828v2>.

This child of #1011 supplies a generic finite-dimensional consequence of two
actual restricted residual estimates. It does not construct a hard-truncation
residual or assert the printed small-cutoff estimate for an actual chain.
Those physical production/application tasks have separate owners. In
particular the original and perturbed relative spectral windows use their own
actual ground energies; an absolute cutoff at the original ground energy is
not silently renamed as a relative perturbed cutoff.

## Exact public statement

For actual finite Hermitian matrices H,F on a nonzero coordinate space, assume
F ≤ H, η > 0, ξ > 0 and δ > 0. Derive the canonical eigenbases and actual minima
E,E' from the last decreasingly ordered eigenvalues internally. Suppose the
operator H−F has restricted operator norm at most ξ on both actual canonical
closed spectral spans at the same absolute cutoff E+η, one for H and one for F.
Let N = ceil(η/(2ξ)) and η' = η+ξ+2ξ sqrt(N/δ). Then:

- E' ≤ E ≤ E'+ξ;
- the actual F-space at E'+η' is δ-close to the H-space at E+η;
- the actual H-space at E+η' is δ-close to the F-space at E'+η.

No eigenbasis, ground energy, spectral comparison, closeness, residual-to-vector
map, or alternative low-energy predicate is supplied. The nonempty coordinate
assumption is required to take an attained actual minimum. Repeated eigenvalues
and arbitrary positive η,ξ,δ are allowed; no spectral gap or simplicity premise
is added.

## Proof and scope

Weyl monotonicity gives E' ≤ E. The #1011 min--max theorem at the last index,
using the actual low-F residual, gives E ≤ E'+ξ. Both spectral lower bounds
follow from antitonicity of the ordered eigenvalues.

The accepted finite-window closeness theorem is applied with window half-width
ξ. The source width is η, so its count is exactly N. The forward target
separation is nonnegative, and its perturbation denominator is at least
ξ+2ξ sqrt(N/δ). A single private scalar helper squares the nonnegative lower
bound and verifies N(2ξ)² ≤ δ times the denominator squared.

For the reverse direction, E' ≤ E gives inclusion of the actual F-space at
E'+η into the supplied low-F space at E+η. Restrict the actual residual to
that smaller space and interchange H,F in the same accepted theorem. The
reverse denominator is larger. Neither argument assumes an approximate basis,
a shifted ground energy, or a new physical cutoff theorem.

Base: #1011 head `c04b69cdc483bc79c2512bbf1aba33e03e111d3e`, itself based on
accepted main `86b3159b98a1608c5e66a875fa670a9687c9867d`. Lean v4.35.0-rc3 and
Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e` remain unchanged.

Root and independent native mathematical/pinned-API reviews passed the complete
135-line source, including both cutoff directions and the exact pinned window
API. Native imports, full Blueprint/source synchronization and reverse coverage,
unique new anchor ownership, ChkTeX, source width/size and integrity, active
references, repeated-tactic scan, and whitespace checks passed. Reader-facing
prose is checked on the final committed tree before publication. No local Lean, Lake, elaboration, build, or compiled
Blueprint check is run. The new Blueprint statement and proof remain
`notready`; exact-head hosted acceptance and dependency integration are separate.
