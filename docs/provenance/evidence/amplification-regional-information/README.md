# Verification of regional information inequalities

Immutable proof source: `e5fe5732e6c10a921793c1c03bee5403e5bf6362` in
LionSR/QICLean. The source adds three public theorems in
`QICLean/Entropy/FiniteProductInformation.lean`, a five-example regression file,
a mathematical chapter and a source comparison document. There are no new public
definitions. Private coordinate and strong-subadditivity lemmas are included in
the kernel dependencies of the audited public theorems.

The mathematical source is OpenAI's September 24, 2026 area-law manuscript,
`01-preliminaries.tex:19–25` and `09-amplification.tex:560–561`, pinned to
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. All new proof text is original.
The imported QICLean results retain their existing attribution.

- `build.log`: the exact production source passed the targeted Lake build with
  package options and standard linters, without warnings. The existing prebuilt
  Mathlib artifacts were used; no Mathlib source build was started.
- `Axioms.lean` and `axioms.log`: all three public declarations have complete raw
  kernel reports, containing only `propext`, `Classical.choice`, and `Quot.sound`.
- `regressions.log`: the regression file passed with the full standard linter set
  and warnings as errors. It checks a genuinely unnormalized product vector of
  norm two, conditional information, overlapping regions with unequal local
  dimensions, a proper discarded subregion, and empty regions/empty local bases.
- The source and changed prose checks, whitespace checks and proof-pattern scan
  passed. The scan found no pattern requiring another abstraction.
- Every public theorem has its own blueprint link. This contribution does not
  modify the generated import aggregator or the shared chapter input list;
  integration supplies those two additions and checks the combined blueprint.

The provenance shard is
`docs/provenance/openai-math.d/amplification-regional-information.json`.
It records the exact checked source, commands and SHA-256 hashes of the logs.
`provenance.log` records validation of all three own records using the immutable
policy identified in `policy-snapshot.json`. The validation is limited to this
shard; it does not repeat unrelated historical source audits.

No full-library build or complete blueprint declaration check is claimed here.
Those are checks of the combined integration. The global area law and the
amplification proposition remain separate mathematical objectives.
