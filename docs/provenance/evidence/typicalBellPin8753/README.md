# One-copy Bell contraction verification

The production source is frozen at QICLean revision
`90e6071e32453006906390bd4e4f71ff4c5251a0`, over the published compressed-vector
revision `c8d6b2f7e576407d180c853a7ebb5ad84b342422` of draft #609.
The mathematical statement uses the actual selected spectral embedding and
compressed pure vector. Its only premise is positive selected mass; the
original vector need not be normalized. Tensor powers and complementary label
projections are subsequent results.

The target build passed with the package's standard linters. The entire source,
including all private definitions and proofs, also passed a separate strict
elaboration with warnings as errors. All seven public declarations, including
four definitions, have exact-name kernel reports containing only `propext`,
`Classical.choice` and `Quot.sound`. The kernel audit disables only the linter
that prohibits diagnostic `#print` commands. The production source contains no
such option change. The text style check returned zero files with errors; it
disables only the repository-wide Python style script, which QICLean does not
provide. The tactic-pattern check inspected an exact copy of the production
module and found no repeated patterns.

The isolated cache was seeded from the idle, fully built compression worktree,
then the pinned prebuilt Mathlib cache was fetched explicitly. Its aggregate
artifact was verified before elaboration. The raw seed and cache logs are
retained. Mathlib was not built from source.

The seven-row provenance shard is checked using the frozen TNLean policy
`806099b4dddcce591b3a62ee1921926a6af5ad55`. `check_provenance.py` asserts the
validator and schema hashes, validates immutable source bytes and log hashes,
checks the complete public declaration set and original notices, and rejects
proof holes or prohibited tokens after stripping comments and strings. The
policy's conservative declaration index includes private declarations; the
public-coverage check explicitly excludes those commands. Inherited shards are
unchanged and are not re-audited by this narrow check.

The exact Bell fragment was rendered together with the existing compressed-
vector fragment and bibliography. The standalone wrapper uses a page break
between the two sections and a small emergency stretch to prevent overfull
lines. All three physical pages were inspected; the new Bell section occupies
physical page 2. There are no unresolved references, overfull lines, clipping or
illegible formulas. The wrapper and render image are retained for reproduction.
The complete book, web pages and declaration synchronization remain integration
checks after including the new module and fragment. No shared chapter or root
import aggregator is changed here.

`verification.json` records the source, commands, exact names and artifact
hashes. `source-comparison.json` records the mathematical scope and the preserved
parent files. Raw proof-bound logs are retained verbatim.

These proofs and checks were prepared with assistance from OpenAI Codex
(GPT-6). Human mathematical review is separate from kernel verification.
