# Focused Poissonized-word decay render

Frozen final source: `8e0a72aa2ad07a02a5c5a13436b17607fdd5af61`.

The four routed leaves render successfully as a seven-page PDF and six static
HTML pages. All 52 public constants are linked in the PDF, chapter page, and both
graph modals: 50 explicitly named declarations and two generated measurable-space
instances in that render source. At current source
`3c911be1ccb1f35b97aa35e100e2d45af2ea0b0b`, those same two existing names
are explicit, so all 52 are source-discoverable. `source-transfer.json` verifies
that exact naming-only transfer; no new render is claimed. The four production
modules contain 639 lines. Source inspection also
counts 24 consumer examples and 52 axiom guards; this worker ran no Lean compiler.

All seven PDF pages and the generated dependency graph were inspected as pixels.
All 33 source labels, including 15 equation anchors, resolve in PDF and HTML.
The graph has 14 nodes and 16 rendered edges, with the same reachability as 24
explicit dependencies. Dashed statement edges and solid proof edges match their
source placement. There are no overfull/underfull boxes, missing glyphs, unresolved
references, duplicated HTML IDs, or visible formula defects. No tensor diagrams
were introduced, so Tenkz picture validation is inapplicable.

The initial exact-source render at `64cb622e9b786d0f5437c96212918474b8a2e20a`
found three missing static equation anchors, two unlinked generated instances,
and a 0.49863 pt overfull theorem heading. The leaf-only repairs expose the full
52-constant inventory, anchor the displayed formulas, and shorten that heading.
They also correct the manuscript citation by section title, separate arbitrary
Omega from the unit-vector projection corollary, and make the weaker large-gap
hypotheses explicit. Production Lean, consumers, guards, routers, and pins were
not edited by this worker. Original artifacts and raw logs remain unchanged.

The mathematical review checks the per-word mass exp(-Nt)t^m/m!, its length
normalization, nonnegative time including zero, latest-factor-on-the-left order,
arbitrary real gap and ground vector, the g>N vanishing branch, unit normalization
only for the complementary projection, arbitrary entangled spectators, and the
final exp(-gt) squared-norm bound. The cited passage is lines 237–253 of
`09-amplification.tex`, with chronology at lines 49–54, in the section
“Amplifying the collar estimate,” pinned at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

This proves a result for the concrete normalized Poissonized word law. The
identification with independent rate-one clocks, coupled-clock locality, and
full amplification remain separate unproved bridges. This packet is a focused
render, not a full-book build or live-browser/MathJax runtime test. Remote Lean
URL availability was not checked. Nonfatal installed-tool warnings about font
maps, the inherited title-page destination, and unavailable vector imagers are
retained in the raw logs; every final page and all local link destinations pass.

## Evidence and replay

`verification.json` records exact source/artifact hashes, all declaration URLs,
labels, and graph checks. `visual-review.json` records page, static-HTML, graph,
and mathematical inspection. `focus-manifest.json` identifies the frozen inputs,
unchanged tool versions, and manuscript source. `initial-findings.json` preserves
the original failed-quality record. `source-binding.json` records the comparison
between the original and final source. `commands.json` supplies replay commands
and genuine retained raw-log hashes, with machine paths normalized.

Run `python3 check.py` for source, the exact naming-only transfer, and packet integrity. A later checkout can select
this exact historical source using `--source-revision` with the frozen revision.
For a render replay, set WORKSPACE, source `$WORKSPACE/glm23-blueprint-env.sh`, and
follow `commands.json`. SOURCE_REVISION and RENDER_NAME can select another source
and a separate output directory. The installed texra-blueprint 0.3.8 environment
and existing font cache are reused. No downloads, external writes, binary/LFS
commits, or pin changes are involved. Seventeen final artifact hashes are retained;
all generated binary artifacts and raw logs remain local and outside this packet.
