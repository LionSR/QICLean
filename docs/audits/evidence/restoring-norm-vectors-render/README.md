# Focused restoring norm and vector render

Frozen render source: `947cfcb24904c7ba5c83e9723f9c0db994731935`.

The new norm/vector leaves render in a bounded fixture containing the two prior
restoration leaves and the exact existing partial-trace definition as context.
All 54 package declarations are checked, including all 25 new declarations:
six norm theorems and nineteen vector declarations. Four partial-trace context
links are inventoried separately. The historical core render remains separate.

The nine-page PDF and six static HTML pages pass. Every PDF page and the actual
generated dependency graph were inspected as pixels. All 39 labels, 58 PDF and
chapter declaration links, and the links in both graph modals resolve locally.
The graph has 20 nodes and 18 rendered edges, with reachability equal to its
25 explicit dependencies. There are no tensor diagrams. Final TeX has no box,
missing-character or undefined-reference warnings.

The initial render found three absent static norm-equation anchors. Commit
`fc2af2b56160113a03a65dc065102ff4eb118759` moves their labels/numbers to the
first align row and uses the repository reference style in the vector leaf.
Commit `947cfcb24904c7ba5c83e9723f9c0db994731935` removes an inaccurate
“twice” count from the tensor-order proof. No Lean sources, workflows or routers
were changed by the render worker. The earlier render stages and raw logs remain
locally preserved with hashes in this packet.

The review checks the actual weighted Gram bound, Euclidean operator norms,
independent unit-blank assumptions, the exponential coefficient, the full-basis
column identity, spectator coordinates, inverse-weight adjoint cancellation,
the copy isometry and the three-projection error bound. The scalar identity
identifying the exponential parameter is a hypothesis; no entropy/purity
identification is silently added. The paper remains pinned to
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Section 9, lines 324–446.

This is not a full-book build, a live-browser/MathJax test or a remote Lean-doc
availability check. The render worker ran no Lean/Lake/checkdecls or CI; the
30 consumers and 54 axiom guards were source-inspected only. It does not prove
existence of typical projections, localization, the ground-component coefficient
identity, or the complete amplification theorem.

## Evidence and replay

`verification.json` records the exact frozen input/artifact hashes, declaration
URLs, references and graph checks. `visual-review.json` gives the pixel, static
HTML and mathematical review. `focus-manifest.json` identifies the context
excerpt and tools. `commands.json` gives replay commands and raw-log hashes with
private workspace paths scrubbed. `initial-findings.json` and
`anchor-fix-findings.json` retain the earlier stages. `source-binding.json`
distinguishes the public base checkpoint from the later local render fixes.

Run `python check.py` for source/packet integrity. For rendering, set WORKSPACE,
source `$WORKSPACE/glm23-blueprint-env.sh`, and follow `commands.json`.
The fixture reuses the installed texra-blueprint 0.3.8 environment and existing
font cache. SOURCE_REVISION can override the frozen revision. Binary artifacts
and original raw records remain local and are not committed or uploaded.

The historical core checker was narrowly maintained for later router additions:
it still checks every substantive core source byte and preserves the historical
router/artifact hashes, while requiring both original core includes exactly once.
Its successful current-head run is recorded in this packet; the core was not
rerendered or relabeled as a new result.
