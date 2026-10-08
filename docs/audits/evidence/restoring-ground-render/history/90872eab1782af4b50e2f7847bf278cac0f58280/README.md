# Focused physical ground-component render

Frozen render source: `90872eab1782af4b50e2f7847bf278cac0f58280`.

This separate fixture renders the six restoration leaves plus the exact existing
partial-trace definition as context. It covers all 76 public package declarations
across 1,740 production lines, including 20 new coefficient/ground declarations
and two promoted vector helpers. Four pre-existing partial-trace context links
are counted separately. The earlier 29- and 54-declaration evidence remains
historical.

The 12-page PDF and six static HTML pages pass. Every final PDF page and the
actual generated dependency graph were inspected as pixels. All 60 source labels
and all 80 PDF/chapter declaration links, plus both graph-modal inventories,
resolve locally. The graph has 29 nodes and 33 rendered edges, with reachability
equal to 44 explicit dependencies. No tensor diagrams occur. Final TeX has no
box, missing-character or undefined-reference warnings.

The first render found a missing static anchor for the ground definition and a
2.09pt overfull coefficient-theorem condition. The narrow repair moves the label
to its first align row and states the identical condition as “If M≥0, then.”
The mathematical statements and Lean source bytes are unchanged. Initial
artifacts and raw logs are retained separately and hashed in this packet.

The mathematical review checks the actual reduced density of Ω, ancillary
identities and spectator order, the coefficient M_yx/√p_x, the full row basis,
unit physical/vector blanks, diagonalization of the actual marginal, singular
weights, and the trace chain ending at one. A source-inspected nonreal +i
regression distinguishes the coefficient from its transpose or conjugate.
Only the density and Q must commute; no Q/(I⊗T) commutation or full-rank
hypothesis is added.

This remains a focused render, not a full-book build or live-browser/MathJax
runtime test. Remote Lean-document availability was not checked. The worker ran
no Lean/Lake/checkdecls or CI; all 44 consumers and 76 guards were source-inspected
only. The packet does not establish typical-projection existence, localization,
a purity-to-mutual-information identification, or the complete amplification
theorem.

## Evidence and replay

`verification.json` contains frozen input/artifact hashes, declaration URLs,
reference checks and graph reachability. `visual-review.json` records page,
static-HTML, graph and mathematical inspection. `focus-manifest.json` identifies
the context excerpt and unchanged tools/paper pin. `commands.json` records replay
commands and retained raw-log hashes with private paths scrubbed.
`initial-findings.json` preserves the first render, and `source-binding.json`
distinguishes the public historical checkpoint from the new local source.

Run `python check.py` for current substantive-source and packet integrity.
For a render replay, set WORKSPACE, source `$WORKSPACE/glm23-blueprint-env.sh`,
and follow `commands.json`. SOURCE_REVISION can override the frozen revision.
The installed texra-blueprint 0.3.8 environment and existing font cache are reused.
No binary artifacts, tool caches or raw logs are committed or uploaded.

The historical 54-declaration replay explicitly selects public ancestor
`2bddde9e49330bab20260b002b7f0ba7de51918e`. Its exact tree was materialized
and independently matched to every original source hash. Run:
`python3 docs/audits/evidence/restoring-norm-vectors-render/check.py --source-revision 2bddde9e49330bab20260b002b7f0ba7de51918e`.
Its original render/source/artifact records remain unchanged. The new checker
checks the current 76-declaration source; these two claims are kept distinct.
