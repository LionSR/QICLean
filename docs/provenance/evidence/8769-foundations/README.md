# Compression foundations evidence

This packet addresses [TNLean #8769](https://github.com/LionSR/TNLean/issues/8769),
under [tracker #8733](https://github.com/LionSR/TNLean/issues/8733).
It contains 139 named public declarations in nine mathematical modules.
The distributed density-compression theorem, its circuit semantics, and its
operator tensor-network construction remain open.

The manuscript is the September 24, 2026 version of *Polynomial PEPS
approximation of gapped square-grid ground states*, Theorem 5.2, at
OpenAI/math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Eleven Gaussian declarations adapt OpenAI Lean source; 128 declarations use
original proof text. Every declaration has an explicit source notice and a
record in an issue-owned provenance shard. The unchanged upstream Apache 2.0
license is retained in `LICENSES/openai-math-Apache-2.0.txt`.

The proof revision is `8deb555c1fa91e9561720014fe4c3066c8402240`. Each shard
records the exact revision, commands, successful exit codes and SHA-256 hashes
of the build, compiled axiom and source-audit transcripts. Its `ported` status
applies to the recorded declaration; it does not assert that the paper's full
theorem or an entire cited equation has been integrated.

- `build.log`: targeted package build of the probability import frontier and
  the weighted rectangular and exterior-map modules, with project linters.
- `axioms.log`: all 139 declarations, with only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms. The audit disables the hash-command style
  linter because its purpose is to execute `#print axioms`; proof checks and
  other linters remain enabled.
- `regressions.log`: six strict suites covering coincident Gaussian indices,
  circular normalization, empty families, zero probabilities, different ket
  and bra dimensions, non-Hermitian exterior inputs and deterministic samples.
- `source-audit.log`: complete public-source mapping and absence of proof
  placeholders or custom axioms. The audit accepts the provenance parser as
  its argument; the parser used here is from TNLean revision
  `4e9d9c898a4401d51cf1eeeabcea8572242387fe`, `scripts/check_openai_provenance.py`.
- `style.log`, `imports.log`, `file-size.log`, `blueprint-sync.log`: the
  repository checks and exact Lean-name links pass.
- `mathlib-preflight.log`: the full Mathlib import closure of the targeted QIC
  modules is available from exact prebuilt artifacts before the final build.

The full QICLean build and full blueprint rendering are delegated to PR CI.
The new chapter separately passed standalone LaTeX/BibTeX compilation.

OpenAI Codex (GPT-6) assisted with proof generation, source review, testing,
documentation and coordination under the repository owner's direction.
Independent agent review is recorded; human mathematical review is pending.
