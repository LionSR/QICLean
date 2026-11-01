# Benchmark provenance canaries

These comment-only identifiers label public QICLean source modules relevant to
[Terminal-Bench Science PR #1283](https://github.com/harbor-framework/terminal-bench-science/pull/1283).
Each module carries one unique UUID in the form `-- qiclean-canary GUID <UUID>`.
The identifiers are stable provenance labels with no effect on Lean declarations,
proofs, imports, or build configuration. They contain no agent instructions and
perform no network access or telemetry.

A matching identifier in a trajectory or copied source is evidence that the
marked source text was encountered. It does not establish whether a proof was
copied, and an absent identifier does not establish independent derivation.
These comments do not prevent downloads, cover historical revisions, or mark
other repositories such as Lean-QuantumInfo. The coverage descriptions below
identify the modules; they do not claim that every benchmark target is proved
by this library. In particular, the sandwiched Rényi files cover the trace
functional and order-two comparison, rather than a general Rényi equality theorem.

| UUID | Source module | Coverage |
| --- | --- | --- |
| `c7f661a6-b00d-4bed-89b4-d4e68d4937cf` | [`QICLean/Analysis/LiebConcavity.lean`](../QICLean/Analysis/LiebConcavity.lean) | Lieb concavity and operator Jensen inequalities |
| `a6445712-b772-40f3-8646-12ce3296b4eb` | [`QICLean/Analysis/LiebOperatorConcave.lean`](../QICLean/Analysis/LiebOperatorConcave.lean) | Operator concavity used by Lieb concavity |
| `5fc8b945-f7c1-4deb-b219-31acebd1b220` | [`QICLean/Channel/Schwarz/RelativeEntropyDataProcessing.lean`](../QICLean/Channel/Schwarz/RelativeEntropyDataProcessing.lean) | Relative-entropy data processing under partial trace |
| `4ffddd49-c0d2-44b6-830c-fb0ce359bb15` | [`QICLean/Channel/Schwarz/StrongSubadditivityPosDef.lean`](../QICLean/Channel/Schwarz/StrongSubadditivityPosDef.lean) | Strong subadditivity, including singular states |
| `fc0f44f4-0a4d-4136-80b0-94ea50838d43` | [`QICLean/Channel/PetzRecovery.lean`](../QICLean/Channel/PetzRecovery.lean) | Trace-preserving Petz transpose-channel construction |
| `0f4cbd0b-dbf5-4e8a-b885-7874455615fd` | [`QICLean/Channel/Schwarz/WeylSupportPetzRecovery.lean`](../QICLean/Channel/Schwarz/WeylSupportPetzRecovery.lean) | Petz recovery from equality in partial-trace data processing |
| `61efdee6-0b78-4e17-9f54-62aaeb4a23ff` | [`QICLean/Channel/Schwarz/SSAEqualityPetzRecovery.lean`](../QICLean/Channel/Schwarz/SSAEqualityPetzRecovery.lean) | Petz recovery from equality in strong subadditivity |
| `3b0d1cd7-f37d-44bc-8d82-58aca0812a5d` | [`QICLean/Entropy/SSAEqualityCharacterization.lean`](../QICLean/Entropy/SSAEqualityCharacterization.lean) | Public SSA-equality characterization |
| `48deda7c-6f0c-4d88-bef3-8b77043770c4` | [`QICLean/Analysis/EntropyMarkovForward.lean`](../QICLean/Analysis/EntropyMarkovForward.lean) | SSA equality implies the HJPW decomposition |
| `32cae8be-1bde-43be-8402-8d842071839c` | [`QICLean/Analysis/EntropyMarkovReverse.lean`](../QICLean/Analysis/EntropyMarkovReverse.lean) | HJPW decomposition implies SSA equality |
| `c1f93e49-79bd-4b64-a712-d1a1086514da` | [`QICLean/Channel/KoashiImoto/NormalizedFamilyBlockForm.lean`](../QICLean/Channel/KoashiImoto/NormalizedFamilyBlockForm.lean) | Normalized invariant-family block decomposition |
| `f5aa4fdb-d8d3-479f-9acb-753e1fff1cb8` | [`QICLean/Channel/KoashiImoto/MarkovDilationBlockForm.lean`](../QICLean/Channel/KoashiImoto/MarkovDilationBlockForm.lean) | Markov recovery dilation in block coordinates |
| `375e7b6e-538d-4f21-84a1-d0a09edce4c9` | [`QICLean/Analysis/SandwichedRenyi.lean`](../QICLean/Analysis/SandwichedRenyi.lean) | Sandwiched Rényi trace-functional interface |
| `f7aacbbc-27a1-459c-a38e-9afcc970e045` | [`QICLean/Analysis/SandwichedRenyiTwo.lean`](../QICLean/Analysis/SandwichedRenyiTwo.lean) | Order-two sandwiched trace functional and entropy comparison |
