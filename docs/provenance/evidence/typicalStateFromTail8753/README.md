# Typical states from a spectral tail

The source revision is `79b9d503971a4ff2409fa557e174b46b13fdbbda`, based on the
published 54-declaration analytic contribution at `3446fccd`. The two public
declarations use the accepted canonical typical set and the existing actual
normalized spectral restriction and pure vector. No new definitions are added.

For a trace-one positive density with entropy S, a spectral tail at most δ < 1
gives selected mass z between `1 - δ` and one, and positive mass. Its actual
normalized spectral restriction is positive semidefinite with trace one and
rank equal to the typical-set cardinality. Its logarithmic rank and entropy
are within `w - log (1 - δ)` of S. For a unit bipartite vector, the actual
selected first marginal obeys the same bounds, and the selected unit vector
has distance at most `sqrt (2δ)` from the original vector.

The reference is OpenAI, *A two-dimensional area law from a global spectral
gap* (September 24, 2026), at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, `07-comparators.tex`, lines 39–55
and 240–247, following Lemma 3.1. The tail estimate is an explicit premise of
these finite-dimensional consequences. The physical choice `w = n^(3/5)`
and the asymptotic bound `δ = n^-100` are separate applications.

`mathlib-cache.log` records a successful fetch of the pinned prebuilt cache;
the Mathlib olean was verified before compilation. `build.log` records the
successful module target with 3,275 jobs, with only the new module compiled.
`strict-source.log` records the full production source with warnings as errors,
standard Mathlib linters and strict implicit arguments. `axioms.log` records
the successful audit of both exact public declarations; only `propext`,
`Classical.choice` and `Quot.sound` occur. The diagnostic fixture disables
only the linter against hash commands.

`checks.json` records exact source and raw-log hashes. The two-entry shard
`typicalStateFromTail8753.json` contains the independent original notices and
whole-file source bindings. The frozen TNLean provenance validator checks both
bindings and exact-name kernel reports. The new blueprint fragment is
`ch12_entropy_typical_tail.tex`; no shared import aggregator or chapter
inclusion is edited in this contribution.

Codex (GPT-6) assisted this independently written formalization. No upstream
Lean proof text was copied or adapted. No push or pull request was made.
