# Area-law auxiliary results: complete verification

All three complete checks were run on QICLean source revision
`c6219ee822af21aa3db1168a8640d17ffa25b02f`: PDF generation (exit 0), web
generation (exit 0), and declaration checking (exit 0). The declaration check
followed the successful parent-owned full Lake build. Raw command logs, the
final LaTeX and bibliography logs, and a copy of the parent build log are
preserved here. Individual exit records give the actual command durations.

`render-inspection.json` records log and PDF hashes, visual inspection, and the
presence of every new mathematical entry and both manuscript citation targets
in generated HTML. The PDF has 410 physical pages. Visual review covers:

- physical page 14, printed page 13: all three positive regulator estimates;
- physical pages 394–395, printed pages 393–394: the typical pure vector,
  its two marginals, distance estimates and three-factor subsystem estimates;
- physical pages 395–396, printed pages 394–395: simplex necessary conditions,
  the actual diagonal objective and normalized weights, and the last-filter
  derivative and clipping theorem.

All inspected material is legible, without clipped or overlapping content,
missing formulas, broken citations or theorem links. The final PDF log has no
undefined references or citations. Existing overfull boxes remain elsewhere
in the full book; no overfull box occurs in the three new source fragments.
The review does not claim a visual inspection of every page of the book.

The PDF skill's artifact marker succeeded immediately before generation.
The final artifact is `output/pdf/area-law-analytic-integration-blueprint.pdf`;
page renders and extracted text were produced under
`tmp/pdfs/area-law-analytic-integration` and removed after inspection.
No production source, aggregator, or mathematical documentation was edited.
No commit or publication action was performed by this verifier.

The complete library build succeeded with 9,676 jobs. All 54 new public
declarations have exact-name kernel reports containing only `propext`,
`Classical.choice` and `Quot.sound`. The combined audit file disables only the
linter that forbids diagnostic `#print` commands; production proofs are not
modified. All seven owned provenance records passed the frozen TNLean policy,
including byte-for-byte binding to the recorded verification revisions.
`checks.json` records source, command and log hashes.

These are auxiliary results: regional information inequalities, purification
splitting, typical spectral truncation and its actual pure state, closed-simplex
necessary conditions, and positive-regulator estimates under explicitly stated
commutation and order hypotheses. The native patch stationarity argument, the
full area-law theorem and unconditional PEPS approximation theorem remain open.

The new regressions cover singular densities, empty index types, selection of
the entire spectrum, simplex boundary points and a noncommuting projection.
Their source revisions and passing commands remain in the individual component
evidence directories; the combined audit does not claim a second execution of
those unchanged tests.

After incorporating accepted filter-moment and designated-support marginal-tail
results from QICLean main, all seven production files remained byte-identical.
At source revision `09fdda4f`, the complete library build passed with 9,681 jobs;
PDF, web and declaration checks passed again, as did the combined 54-declaration
kernel and provenance audits. The new kernel output is byte-identical to the
preceding successful audit. `latest-checks.json` records this subsequent
verification; the earlier records remain unchanged.

The final book has 411 physical pages. An independent visual review of physical
pages 14 and 394–396 found their extracted text identical to the earlier inspected
pages and their formulas, citations and layout clear. The final artifact hash is
recorded in `latest-render-inspection.json`.

The remote blueprint job at head `3446fccd` stopped before rendering because
the new note's `openai` source key was absent from the paper-gap registry.
Configuration revision `12580498` adds that single source registration. The
actual `texra-blueprint paper-gaps check` then passed: all 60 referenced notes
resolve and their source keys are registered. `paper-gaps-check.json` records
the checked configuration and raw output hash. No mathematical source, note
path, blueprint text or proof-bound citation changed, so the preceding kernel
and full-book verification remain applicable. The remote job is rerun after
publication of the metadata correction.
