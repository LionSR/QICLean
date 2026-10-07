# Gaussian reindexing: focused PDF and static HTML

The final fixture is bound to source revision
`2d8487576c0612f77208236d86b754bf95cd51b8`. It copies seven complete blueprint
leaves byte for byte: physical-buffer overlap, doubled-system gap, Gaussian
filtering, parameter choice, generic uniform approximation, physical-buffer
uniform approximation, and finite reindexing. Only the fixture's router and PDF
title change. The prerequisite definitions and dependency references are present.

[Verification](verification.json) passes for 17 PDF pages and six static HTML
pages. All 119 source labels resolve in both outputs, all 70 equation labels
have their own HTML display-block anchor and distinct PDF destination, and all
117 declaration links match the source. This includes all 58 public declarations
parsed from the Gaussian modules. All 471 HTML fragment links and 115 PDF
internal links resolve. There are no missing anchors, duplicate HTML IDs,
unresolved references, or final TeX layout errors. Parsing source declarations
checks identity and coverage; it does not check Lean proofs.

The [visual review](visual-review.json) covers physical PDF pages 15–16 (printed
pages 14–15), containing the complete new leaf. The inverse-coordinate formula,
six Lean badges, all seven equation numbers, full and restricted integral
equalities, edge-case statements, and proofs are readable without clipping or
overlap. Other pages were verified automatically, not visually, in this fixture.

The Tenkz sweep passes with one inherited picture, zero hard findings, and zero
advisories. Its inherited display has no equation-group scope, so no hard group
comparison is claimed. The source pin matches the existing Tenkz checkout. The
supported PDF-to-SVG fallback succeeds in this environment without `dvisvgm`.
[Commands](commands.json) records the existing font-map and title-page
destination warnings and the earlier unsuccessful attempts. In particular, an
initial static-HTML check caught two missing integral anchors; labeling the first
align row repaired them, and the fresh final fixture passed.

The [manifest](focus-manifest.json) binds exact source, support, and fixture
hashes. Generated PDF, HTML, SVG, page images, and raw logs remain in the
persistent external fixture named in `commands.json`; only text support and
verification files are tracked. The preliminary single-leaf PDF review is retained
as explicitly superseded evidence, not as the final validation result.

To reproduce, activate an existing blueprint Python environment, configure its
cached TeX formats, and set `TENKZ_ROOT` to the repository's pinned revision. Run:

```sh
bash docs/provenance/evidence/8766-gaussian-reindex/render/run.sh \
  "$SOURCE_ROOT" "$NEW_EXTERNAL_FIXTURE"
```

`prepare.py` refuses to overwrite an existing fixture. `run.sh` renders the PDF
and static HTML and runs the Tenkz sweep and final verifier. `verify.py` checks
current source hashes against the copied fixture before validating outputs.

This is focused PDF and static HTML verification. It does not establish
full-book rendering, live browser or MathJax behavior, responsive layout,
remote declaration-URL availability, or a new Lean/Lake/checkdecls result.
