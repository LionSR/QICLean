# Typical widths under a linear cut budget

This record verifies the inclusion of the scalar estimate
`Entropy.exists_typical_tail_bound_of_linear_budget` into the full QICLean
library and entropy chapter. The mathematical source is revision
`317ecbd4478f243b844fb8d4a1d70fbbfd9c1f9a`; the inclusion source, frozen before
verification commands, is `6d9e055e0ab969a5fde3328f4581f6adc3a1f0fb`.

The independent mathematical review finds no additional hypothesis or missing
step in the stated numerical implication. For fixed theta and C, the bound
B <= Cn gives an exponent of magnitude at least c n^(1/10), with c > 0.
Stretched exponential decay then gives one threshold N >= 2, independent of B,
at which the expression is at most n^(-100). The geometric budget bound and
the actual ground-state marginal-tail estimate remain separate requirements;
this result does not prove either of them.

The pinned prebuilt Mathlib cache fetch and complete 9,683-job QICLean build
passed. The strict kernel audit produced 57 distinct reports, each using only
`propext`, `Classical.choice`, and `Quot.sound`. All 56 parent reports retain
identical contents. The nine provenance records, their whole-file immutable
source bindings, and all 166 recorded parent and leaf log bindings passed.
Every parent ledger is byte-identical to the published parent `ca3ab6e0`.

Complete PDF and web generation, the native 3,105-name declaration check, generated
imports, added-line prose, and 60-slug paper-gap registry check passed. The PDF
has 412 pages and SHA256
`e81ef022893fb6a867ab7cd7d3ba67588b14cd17c00ab52877af27f88961e77b`.
Physical pages 396–397 were visually inspected: the theorem, proof, cited
source, uniform quantifiers, exact tail expression, and separate physical
requirements are legible without clipping. The final book has no undefined
references or citations. The generated web contains the new section and
theorem labels, resolved source citation, and declaration link.

The earlier leaf audit that failed solely because its audit file lacked a
header and the hash-command linter allowance remains preserved in the leaf
evidence directory. It is excluded from the successful verification; no
production failure is hidden or removed. The previously pending library and
blueprint integration checks are completed by this record.

`source-freeze.json`, `mathematical-review.json`, and `verification.json` record
source bindings, review, actual commands, exits, and artifact hashes.
`render-inspection.json` binds the visual review to the PDF and both rendered
pages. Large raw logs are preserved losslessly as deterministic gzip files
with modification time zero; `compressed-logs.json` gives both compressed and
uncompressed SHA256 values. The native declaration checker emits no stdout
on success, so its empty raw log is intentional.
