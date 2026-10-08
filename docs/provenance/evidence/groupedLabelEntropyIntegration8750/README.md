# Grouped-label operator inequalities: complete-library verification

The source is frozen at `d7fa8954efaa2a5842359206ee98a6c91946e84a`.
The mathematical proof was first committed at
`e15c46e0679bcddc122d1366b9363853a9df9441`; the later revision changes
comments only, with identical statement and proof tokens as recorded in the
individual verification. The unique generated import and chapter input are
frozen at `d3c2710149ae35128407a6ffcbd1d4d3e66311f0`, over accepted main
`4572774633055960f1f5296c2624324834b02b29`.

The single public theorem proves the two-sided order for the actual central
label observables under a specified split of the copies. It uses the actual
triple orthogonal resolution and the existing subgroup dimension theorem;
there is no supplied compatibility or dimension premise. The subsequent
bad-copy dimension and good-auxiliary support estimates are separate.

The complete library build passed with 9707 jobs. The exact-name kernel audit
through the complete library import gives only `propext`, `Classical.choice`
and `Quot.sound`. The frozen TNLean provenance checker at
`806099b4dddcce591b3a62ee1921926a6af5ad55` accepted the one original shard and
its one declaration. Generated imports, added reader prose, the paper-gap
registry, and the pinned prebuilt Mathlib guard all passed with exit 0.
No Mathlib source was built.

The first complete-library run exited 1 during global file-table exhaustion:
17 unchanged targets failed, including one killed Lean process. The initial
log and its actual exit record are retained. All 17 targets compiled in the
source-identical warm retry, and that complete build passed. No source
repair was made for this environmental failure.

The actual full PDF and strict web build passed. The native declaration
checker accepted all 3243 nonempty unique names; the declaration list lacks
a final newline, so the shell newline count is one less. The 417-page PDF
was inspected on physical pages 411–412, printed pages 410–411: section 17.6,
theorem 17.6.1 and equation 17.1. The statement, assumptions and entire proof
are legible, with no clipping, overlap, missing glyphs or unresolved new
citation. The corresponding desktop and mobile web views were inspected.
The wide three-observable display permits local horizontal scrolling on
mobile; its last observable was also inspected after scrolling. The
operator inequality and proof formula fit at mobile width. Focused reader
checks and the entire 38-page, 36392-mathematical-element web check passed.

`source-freeze.json` binds all production, documentation and inclusion
files. `leaf-evidence-binding.json` verifies all 66 original leaf files and
the shard remain byte-identical to the frozen inclusion. `verification.json`
contains actual commands, exits and raw-log hashes. Large integration logs
are committed as deterministic gzip archives with original and compressed
hashes in `compressed-logs.json`; original exit records remain verbatim.
The raw originals are retained locally. All original leaf logs remain
committed verbatim. `evidence-sha256.json` lists the portable committed
artifacts, excluding its own inventory and the archived raw originals.

The PDF artifact marker ran successfully exactly once immediately before
the first PDF build. The work is not pushed or published by this agent.
