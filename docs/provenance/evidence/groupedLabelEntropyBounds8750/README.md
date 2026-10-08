# Grouped-copy label observable bounds

The complete production source is frozen at
`d7fa8954efaa2a5842359206ee98a6c91946e84a`, on verified main
`4572774633055960f1f5296c2624324834b02b29`. The statement and proof tokens
are unchanged from the independently reviewed mathematical source
`e15c46e0679bcddc122d1366b9363853a9df9441`; the later commit adds the required
independence notice and writes mathematical comment formulas in LaTeX.
`comment-only-refreeze.json` records this comparison using the frozen
provenance validator's comment lexer. `source-freeze.json` binds the entire
module, both private proofs, the unique fragment, mathematical reader note,
and tactic ledger.

The single public declaration is
`TensorPower.groupedCopies_labelEntropy_bounds`. It proves two matrix
inequalities on the whole finite permutation representation space. The
specified split is the only geometric datum. Label compatibility is derived
on every nonzero product of the literal three families of central projections;
the accepted subgroup dimension theorem supplies the scalar inequalities.
Positivity of the binomial coefficient is derived from the split. There is no
compatibility, dimension or desired operator-bound hypothesis. Empty groups
and vanishing sectors are included.

The pinned manuscript source is Lemma 6.1(4), `05-replicas.tex`, lines 116–123,
and its logarithmic use in `07-comparators.tex`, lines 455–467,
`comparator:restriction-dimensions`. Both actual local source files were
compared byte for byte with GitHub's immutable `openai/math` revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The digests and Git blob
identifiers are in `source-comparison.json`.

The final source-bound module build passed with 3,107 jobs. The entire source
passed strict elaboration with warnings as errors, the standard Mathlib
linters, and strict implicit arguments. The exact-name stock kernel report
contains only `propext`, `Classical.choice` and `Quot.sound`. The complete
public signature is printed separately. Text style reports zero violations.
The single original provenance entry passed policy revision
`806099b4dddcce591b3a62ee1921926a6af5ad55`. Actual commands, exits and raw
log hashes are recorded in `verification.json`.

The prebuilt Mathlib fetch and artifact guard passed before compilation.
Only dependency packages were seeded from an explicitly idle APFS source;
QIC artifacts from the different source revision were omitted. The actual
QIC dependencies were then compiled in this isolated worktree. No Mathlib
source build was performed. The preceding evidence directory
`groupedLabelEntropy8750` retains the preliminary mathematical-source checks,
including the initially incomplete audit-driver headers and missing source
independence notice. Those failures concern documentation and evidence
construction; all final source-bound checks in this directory passed.

The theorem does not yet prove the bound on the dimensions of labels occurring
on the actual bad copies, preservation of whole auxiliary labels by a
physical excitation component, or the inverse-metric estimate. Those are
subsequent mathematical steps.
