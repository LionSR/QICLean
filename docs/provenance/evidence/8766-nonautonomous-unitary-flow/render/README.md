# Focused unitary evolution rendering

The final frozen source is `220aa2735fbc5f1629c2782edb6b43ae8951ceb3`.
This packet records a successful focused PDF/static-HTML render of the new
unitary-evolution leaf with texra-blueprint 0.3.8. It is not a full-book,
live-browser, remote-documentation, or Lean build result.

The initial `2794faaae0faf0482d4533ed8168554b531903cd` render exposed an
amsmath/plasTeX math-prime serialization issue. The leaf-only repair uses
explicit mathematical primes. All 50 survive in HTML and all eight PDF page
PNGs are identical before and after the repair. See `initial-prime-finding.json`.

`verification.json` records source/artifact hashes and exhaustive structural
checks; `visual-review.json` records actual visual and mathematical findings.
`commands.json` replaces the executor-private root with `${WORKSPACE}` and
identifies retained original records and hashes. Raw logs and binary renders
remain in the workspace; none are included in this compact text packet.

Run `python check.py` from this directory for a standard-library packet/source
integrity check. To reproduce the fixture, set WORKSPACE to the retained
workspace root, source `$WORKSPACE/glm23-blueprint-env.sh`, and run
`python prepare_fixture.py`. Follow the PDF, bibliography-copy, web, raster,
and verification commands in `commands.json`, using `verify_render.py` as
the portable verifier. This requires the recorded installed render tools and
the retained pinned paper source. No Lean/Lake/checkdecls command is used.
