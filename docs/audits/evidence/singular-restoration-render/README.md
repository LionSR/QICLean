# Focused singular-restoration render

Frozen final source: `8ecbed7f053226cd5f8b912514777d986e7cf702`.

This packet checks the two chapter-12 leaves for support-inverse order and
singular restoring operators. The fixture retains the repository's preambles,
macros, templates, bibliography, and configuration; only the chapter wrapper
selects these two byte-identical leaves. The installed texra-blueprint 0.3.8
render uses the existing font cache and unchanged tool/paper pins.

The final PDF and static HTML pass declaration-link, local-reference, and graph
checks. Every PDF page and the generated dependency graph were inspected as
pixels, and all six static HTML payloads were read. All 29 Lean declarations
(17 theorems and 12 definitions) are linked in the PDF, chapter HTML, and both
graph modals. The nine graph nodes and four rendered edges have the same
reachability as the five explicit dependencies.

The first render of `6a48f2bdefb417150b4a62fa1ce6e25350a25294` found a
9.67pt overfull permutation paragraph and three absent static equation anchors.
The source owner split the labeled equations and displayed the permutation;
the Gram positivity explanation was also made precise for merely Hermitian
`T`. Only the restoring blueprint leaf changed; all Lean sources, consumers,
and axiom guards retain their original bytes. `initial-findings.json` records
the original evidence; the original local artifacts and raw logs are retained.

The mathematical review checks the full-basis column sum (including zero-weight
coordinates), `(s,e),(X,Y)` factor order, adjoint orientation, arbitrary blanks,
selected positive inverse weights, weaker Gram hypotheses, the actual marginal
order, and the noncommuting singular support-inverse sandwich. The source is
Section 9, lines 324–446, of the official paper pinned at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

This is a focused two-leaf render, not a full-book build or live-browser/MathJax
runtime test. Remote Lean-document availability was not tested. The render
worker ran no Lean, Lake, checkdecls, or CI; 15 consumers and 29 axiom guards were
source-inspected only. The packet does not establish the paper's norm bound,
column-vector identity, adjoint cancellation, or actual ground-component
coefficient. No tensor diagrams were introduced, so Tenkz picture validation
is inapplicable.

## Records and replay

- `verification.json`: exact source/artifact hashes, declaration URLs, reference
  checks, and graph reachability
- `visual-review.json`: PDF-page, static-HTML, graph, and mathematical inspection
- `focus-manifest.json`: frozen input hashes, paper pin, and tool versions
- `commands.json`: replay commands and retained raw-log hashes, with private
  workspace paths replaced by `${WORKSPACE}`
- `initial-findings.json`: pre-repair artifact and raw-record hashes
- `packet-sha256.json`: compact text packet integrity

Run `python check.py` for a standard-library source/packet integrity check.
For rendering, set `WORKSPACE` to the retained workspace root, source
`$WORKSPACE/glm23-blueprint-env.sh`, and follow `commands.json` starting with
`prepare_fixture.py`. `SOURCE_REVISION` can override the frozen revision.
Binary artifacts and raw logs remain local; none are included in this packet.
