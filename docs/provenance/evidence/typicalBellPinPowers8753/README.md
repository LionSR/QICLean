# Finite-copy Bell contraction verification

The production module is frozen at QICLean revision
`502d0f43d6e86d9f68692a74f92a6c2b1f427ec6`, over the exact one-copy source
`90e6071e32453006906390bd4e4f71ff4c5251a0`. A subsequent exposition-only
commit, `5f4a4a2b184836f441a8b3c63b39a7448f843f65`, displays three long
finite-product and coordinate formulas. It changes no Lean source or audit
statement. The production module remains byte-identical to its five immutable
verification bindings.

The five results use the actual one-copy selected Bell vector, projection,
prevector and postvector. They prove the coefficient `(sqrt z / |E|)^k`, unit
norm of the repeated Bell vector, the orthogonal projection property, copy
invariance, and canonical disjoint-auxiliary factoring for an arbitrary matrix.
The pin and normalization statements require only positive actual selected
mass; the original vector need not be normalized. The copy-invariance theorem
requires no selected-mass hypothesis. Empty-copy products are included.

The target build passed with standard package linters (3278 jobs), followed by
strict whole-source elaboration with warnings as errors. All five exact-name
kernel reports contain only `propext`, `Classical.choice` and `Quot.sound`.
Private proofs are checked by strict source elaboration and occur in those
public dependency closures. The audit disables only the linter against
`#print` commands; the production file changes no linter options. Text style
returned zero files with errors. The tactic-pattern scan of an exact owned
source copy found no repeated patterns.

The new isolated worktree was APFS-seeded from the idle one-copy worktree at
exactly the same source revision. The pinned prebuilt Mathlib cache was then
fetched and its aggregate artifact verified. Package revisions match the
manifest. No Mathlib source build or cross-revision QIC artifact copying was
used. `cache-isolation.json` records these facts; the actual later cache-fetch
output is retained verbatim.

The five-row original-provenance shard passes the frozen TNLean policy at
`806099b4dddcce591b3a62ee1921926a6af5ad55`. The narrow validator checks exact
whole-module source bytes, the complete public declaration set, the original
notices, actual log hashes and standard kernel axioms. It strips comments and
strings before checking prohibited proof tokens. Inherited shards and files
are preserved; `source-comparison.json` records the one-copy parent hashes.

The exact compression, one-copy Bell and finite-copy fragments were rendered
with their bibliography. All four physical pages were inspected. The new
finite-copy section is on physical page 3. The final rendering has no
unresolved references, overfull lines, clipping or illegible formulas. Its
wrapper and the new-section render are retained for reproduction. No shared
chapter or generated import is edited by this leaf contribution; full-library,
book, web and declaration checks belong to the subsequent integration.

`verification.json` records actual command exits and source revisions. Raw
logs are retained verbatim, with deterministic gzip companions and both
SHA-256 digests. Operational intermediate results are not reported as final
verification evidence.

These proofs and checks were prepared with assistance from OpenAI Codex
(GPT-6). Human mathematical review is separate from kernel verification.
