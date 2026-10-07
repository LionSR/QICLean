# Doubled gap and positive-gap uniqueness: combined render

The extended
[`doubled-system blueprint leaf`](../../../../blueprint/src/chapter/ch12_entropy_doubled_system_gap.tex)
has six mathematical entries and links all 16 public declarations: the 13
doubled-gap declarations and the three declarations in
[`PositiveGapUniqueness.lean`](../../../../QICLean/Analysis/PositiveGapUniqueness.lean).
This packet records the combined render. The original 13-declaration render
remains unchanged in [`8766-doubled-gap`](../8766-doubled-gap/README.md), whose
checker reads the frozen leaf from its public checkpoint.

## Strictly positive gap and the source assertion

The added theorem makes the uniqueness assertion in the unnumbered paragraph
after `eq:info-reset-overlap` precise. The paper source is
[`02-information.tex`, lines 415–425](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex#L415-L425).

For a normalized `Omega` and strictly positive `Delta`, positivity of
`H - E0 I - Delta(I - |Omega><Omega|)` forces every vector at energy `E0`
to equal `inner(Omega, psi) Omega`. The vector `psi` can be zero or
unnormalized, and this projection assertion requires no eigenvector equation
on `Omega`. Its proof evaluates the lower-gap inequality on `psi`, then uses
`||psi - inner(Omega, psi) Omega||^2 = ||psi||^2 - |inner(Omega, psi)|^2`.
Strict positivity makes the right side at most zero.

With `H Omega = E0 Omega` as well, the entire eigenspace is the complex span
of `Omega`. Normalization makes `Omega` nonzero, so the eigenspace has
dimension one. The final paragraph applies this theorem to the normalized
`Psi` and the actual partial-swap vector `Phi`, with common energy `2 E0`.
The generic swapped-Hamiltonian consumer in
[`PositiveGapUniqueness.lean` tests](../../../../QICLeanTest/PositiveGapUniqueness.lean)
uses the actual `doubled_gap_partialSwap` conclusions to prove dimension one.

This completes the uniqueness component under `Delta > 0`, without claiming
that `Delta` equals the actual spectral gap. The lower-gap results still admit
`Delta = 0`; both the prose and tests retain a degenerate zero-gap example.
Interaction range, degree, strength, boundary support, and later spectral
filtering are not established by this leaf.

## Render verification

The focused fixture contains the unchanged physical-buffer leaf and the
extended doubled-gap leaf, using the existing integrated Tenkz support.
It produced eight PDF pages and six static HTML pages. Checks verified:

- All 16 target declaration links in PDF and HTML, plus 43 reused links
- All labels and local HTML anchors, with no duplicate IDs or missing images
- Eleven checked statement/proof markers in the extended leaf
- No final LaTeX box warnings or unresolved references
- One unchanged Tenkz compression picture, with four internal physical
  contractions and the original two physical inputs and two outputs
- Matching PDF/standalone Tenkz records and a sweep with no hard or advisory
  findings; no hard equation-group identity check was claimed

Direct pixel review covered PDF pages 3 and 5–7, plus the actual generated web
SVG rasterization. The uniqueness hypothesis, projection identity, eigenspace
formula, proof, doubled/swapped consequence, and zero-gap exception are
legible and unclipped. The render records retain the known TeX environment
warnings and one initial duplicate-config-option failure in fixture
preparation, followed by the successful final builds.

Source and generated-artifact hashes appear in `verification.json`; normalized
logs, their original hashes, and commands are retained alongside it. Generated
PDF, HTML, SVG, and pixel binaries remain local and untracked. The separate
three-declaration [provenance packet](../8766-positive-gap-uniqueness/README.md)
owns the native proof/test/axiom evidence;
this documentation work did not execute Lean, Lake, or a cache command.

Run `python3 docs/provenance/evidence/8766-doubled-gap-uniqueness-render/check.py`
to check current source/guard/tag coverage and the committed evidence hashes.
This does not rerender or run Lean. No live-browser, MathJax, responsive-layout,
complete-book, full-root, hosted-CI, publication, or merge completion is claimed.
