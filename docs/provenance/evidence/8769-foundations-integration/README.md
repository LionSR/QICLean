# Foundations integration evidence

This supplements the historical evidence in `../8769-foundations/` for
[TNLean #8769](https://github.com/LionSR/TNLean/issues/8769).

The full build of the first main integration exposed a duplicate global Lean
name. New main already contains the more general rectangular amplification
lemma `Matrix.l2_opNorm_kronecker_one_le` in `Analysis.RootChannel`. The original
square specialization in `Channel.RectangularTraceNormContraction` is renamed
`Matrix.l2_opNorm_kronecker_one_square_le`; its statement and proof are unchanged,
and its single production caller and kernel audit target use the new name.
Main's general lemma and callers retain their API.

The exact refreshed proof revision is
`0d7c56887caa60b3a0b1cf16df3a534c941f647a`. All four records whose source file
changed receive this revision and new build, kernel-audit, and source-audit
hashes. The other 135 records retain their exact historical source verification.
The earlier proof revisions and raw evidence remain in the branch history.

- `build.log`: targeted `lake build QICLean.Channel.RectangularTraceNormContraction`.
  Full library integration is verified in fresh PR CI.
- `axioms.log`: strict compiled kernel reports for all 139 foundations declarations.
- `regressions.log`: the six exact strict commands added to ongoing CI.
- `source-audit.log`: complete public-name and notice coverage for the nine owned
  modules, using the separately pinned provenance parser from TNLean revision
  `4e9d9c898a4401d51cf1eeeabcea8572242387fe`.

The scoped audit does not assert repository-wide notice completeness: main's
20 unrelated issue #8742 notices lack ledger rows, as recorded in #8737/#8742.
This packet remains 139 public declarations (11 adapted from marked OpenAI
source, 128 original). It does not complete compression Theorem 5.2, the PEPS
approximation theorem, or the ground-state area law.

OpenAI Codex (GPT-6) assisted under the repository owner's direction. Independent
agent review is recorded; human mathematical review remains pending.
