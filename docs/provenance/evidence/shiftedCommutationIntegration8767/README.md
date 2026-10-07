# Shifted matrix-power commutation: integrated verification

The checked integration source is `0166379167f06562d5ee8f18b676f1ac511b3308`,
stacked on parent `3446fccdbe72e932aa9479c146c7f3d1b4faee88` (QICLean #605).
The proof source remains frozen at
`a85789dabd1a2c9f9966fa0b8fdcff160547e88b`; its strict proof and provenance
audits are preserved in evidence commit
`7d378b91b9c169e3d0f8c913af11d58372372b52`.

All four frozen source, regression, blueprint, and reader-note files were
compared byte for byte with the production commit. The inherited parent
integration evidence is unchanged. The only additional mathematical-library
and chapter changes are one generated import and one chapter input.

## Verification

- The complete Mathlib no-build preflight passed: 8,957 targets were already
  up to date. No Mathlib source compilation was needed.
- The import-generator check passed.
- The full QICLean build passed in 662.6 seconds (exit 0, 9,682 jobs).
  Existing warnings in the inherited game-theory dependency are preserved in
  the raw log.
- The full PDF build passed in 79.4 seconds (exit 0).
- The final full web build passed in 76.3 seconds (exit 0), after refreshing
  the local bibliography from the completed PDF build. The initial web pass
  also exited 0, but its missing-bibliography warnings are recorded separately;
  it is not the citation-valid verification pass.
- The full declaration check passed in 16.25 seconds (exit 0), after the
  complete library build and final web generation.

The combined strict kernel audit passed for all 57 exact declaration names.
Only the standard kernel axioms `propext`, `Classical.choice`, and `Quot.sound`
occur (definitions may use none). Narrow validation of the eight owned
provenance shards passed, including immutable source and proof-log bindings,
original notices, and the exact-name combined kernel reports. All seven
preceding production files (the 54-declaration verification) retain their
recorded byte hashes. The new leaf's public declaration set is complete;
unrelated historical shards and inherited auxiliary declarations outside the
recorded set are not newly claimed by this validation.

The raw logs and exit records are retained beside this note. The large PDF
command log is committed as deterministic `pdf.log.gz`; `compressed-logs.json`
records both original and archive byte counts and hashes. The original local
`pdf.log` is also retained. Original leaf proof-bound logs are unchanged. `inspection.json`
records immutable revisions, file hashes, final log hashes, and the rendered
artifact hash.

## Rendered statement

The new theorem and complete proof occupy physical page 396, printed page
395, in the 411-page blueprint. Visual inspection found no overlap, clipping,
or malformed mathematical notation in that entry. The final PDF has no
undefined references or citations. Its 71 pre-existing overfull horizontal
boxes occur outside the new fragment. The final web entry contains all three
public-declaration links and a resolved manuscript citation.

The result recovers commutation with a positive definite matrix from
commutation with a nonzero real power. Its shifted version assumes a positive
semidefinite matrix and a strictly positive scalar shift. The density matrix
argument is unrestricted. The result also applies to the square of a positive
definite filter. It does not derive the preceding commutation premise from
native patch stationarity and does not establish the full PEPS proposition.

The final PDF is retained locally under
`output/pdf/shifted-density-commutation-blueprint.pdf`; generated web, print,
and intermediate render outputs remain local artifacts. No remote publication
is part of this verification.
