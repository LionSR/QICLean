# Focused conserved-operator evolution render

Frozen source: `64114a095e20b692dcbf56de9eaa385ecf201fc4`.

The expanded unitary-evolution leaf renders successfully with texra-blueprint
0.3.8 to a nine-page PDF and six static HTML pages. Every PDF page and the
actual generated dependency graph were visually inspected. All 19 declaration
links, 39 labels, 20 equations, 33 checked markers, 52 mathematical primes,
and dependency reachability pass. The new derivative has the sign
`i(CG-GC)`; conservation and commutation retain arbitrary fixed matrices,
signed time, and empty index sets. No source repair was needed.

This packet covers only the focused leaf. It does not claim a full-book build,
a live browser/MathJax test, remote documentation availability, physical-support
localization, or a Lean build. The earlier `render/` packet is retained as
historical 16-declaration evidence and is not overwritten.

`verification.json` records artifact/source hashes and structural checks;
`visual-review.json` records direct pixel, static HTML, and mathematical review.
`commands.json` records successful command segments and hashes of the retained
raw logs; executor-private paths are replaced with `${WORKSPACE}`. Binary
artifacts and raw logs remain local and are not part of this text packet.

Run `python check.py` for a standard-library packet/source integrity check.
For a render replay, set WORKSPACE to the retained workspace root, source
`$WORKSPACE/glm23-blueprint-env.sh`, then run `python prepare_fixture.py` and
follow `commands.json`. Preparation snapshots the frozen source and unchanged
preambles, macros, templates, bibliography, and configuration; only the
chapter wrapper selects this leaf. The recipe reuses installed tools and the
retained official paper source pinned to
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. It invokes no Lean/Lake/checkdecls.

Public replay source: `04afe6e7f96fb719f22cc4258798f8b24883edc5`, tree-identical to the frozen local source. `SOURCE_REVISION` can override this default.
