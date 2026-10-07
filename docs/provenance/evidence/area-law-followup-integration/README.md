# Combined verification of four area-law proof components

The branch `feat/area-law-followup-integration` combines the original proofs in
`TypicalSpectrum`, `TypicalDensity`, `FiniteProductSplitting`, and
`FiniteProductInformation`. The immutable combined source revision and production
file hashes are recorded in `checks.json`. The per-declaration provenance shards
retain their earlier immutable source revisions; the production source bytes
agree with those revisions after integration.

The full QICLean build passed with 9,661 jobs. The package options apply the
standard mathematical linters. All 27 public declarations, including definitions,
were examined by the combined raw kernel audit. Their dependencies contain only
`propext`, `Classical.choice`, and `Quot.sound`. Both regression files passed with
the standard linters and warnings treated as errors, including empty regions,
unequal local dimensions and an unnormalized vector. The splitting test's module
header was completed before its final strict check.

The complete blueprint PDF and web builds passed, as did the declaration checker.
The new mathematical entries on physical PDF pages 390–393 were rendered and
visually inspected after the final heading correction. Bibliography entries and
references resolve. Existing warnings in imported dependency sources are retained
in the raw full-build log; the four new production modules introduce no warnings.

All four own provenance shards passed the current TNLean provenance validator
with the QICLean repository root supplied. This is validation of these new
records, not a retrospective audit of unrelated records. No manuscript Lean proof
text was copied or adapted. The prebuilt Mathlib cache was fetched and verified
before compilation; Mathlib was not rebuilt from source.

OpenAI Codex and three coordinated agents assisted with source comparison,
proof writing, review, documentation and verification. This assistance disclosure
is separate from the mathematical source and licensing records. Human review
remains independent of the recorded checks.

These results prove typical spectral restriction estimates, physical regional
splitting, and regional information inequalities. They do not establish the
uniform global-gap area law, the full amplification proposition, or the
polynomial PEPS approximation theorem.
