# Combined area-law auxiliary results

This record verifies compatibility of the eleven owned QICLean modules after
integration of the published regional truncation, shifted commutation,
spectral-tail, and selected-Schmidt-space constructions. It does not assert
that the complete ground-state area-law theorem has been formalized.

At source revision `23003bd89855d54a5645d0694accdeb70671c0f8`, the prebuilt
Mathlib cache fetch succeeded and the complete QICLean build passed all 9,685
jobs. The strict kernel audit produced exactly 73 distinct reports, each using
only `propext`, `Classical.choice`, and `Quot.sound`. The eleven provenance
records and every whole-file source binding passed the pinned validator.

The first complete PDF and web builds exited successfully, but their output
was rejected for publication: the combined chapter header placed the entropy
chapter command on a comment line. The resulting PDF omitted that chapter
heading and contained an undefined chapter reference. The failed publication
check and its unmodified logs are preserved. Revision
`4311709afbb0cc0441d68b1997d125c566ce8e65` restores exactly the parent chapter
header and retains every combined input. This is the only source change after
the full build and kernel audit; all Lean files, including the eleven audited
production files, remain byte-identical.

At this corrected revision, complete PDF and web generation, the native
3,121-name declaration check, generated import check, added-line prose check,
and 60-slug paper-gap registry check all passed. The final PDF has 414 pages
and no undefined references or citations. Its SHA256 is
`e8c2ea06e6940c40e89b9b3292050616de407b0828f5e7963847ded3be48fecd`.
The entropy chapter heading and all ten new statements and proofs were
visually inspected on physical pages 316 and 396–400. The formulas, source
citations, and hypotheses are legible without clipping. The generated web
contains all ten new entries and all nineteen corresponding declaration links.

A whole-repository prose scan exits 1 because nine older issue-reference
violations remain in six modules that are unchanged from the parent. The
added-line scan against `7b153216` exits 0. Both results are preserved; no
unrelated prose was changed.

`source-freeze.json` records the initial revision before commands were run.
`final-source-freeze.json` records the corrected publication revision and
unchanged mathematical source bindings. `verification.json` records actual
commands, exits, and artifact hashes; `render-inspection.json` binds the visual
review to the PDF and its rendered images. Large raw logs are preserved
losslessly in deterministic gzip files with modification time zero;
`compressed-logs.json` records both compressed and uncompressed SHA256 values.
The native declaration checker emits no stdout on success, so its empty raw
log is intentional.
