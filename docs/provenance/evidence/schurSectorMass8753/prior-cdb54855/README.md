# Actual Schur-sector mass selection

The two statements in `QICLean/Representation/SchurSectorMass.lean` prove a
generic mass estimate supporting the September 24 OpenAI area-law manuscript,
Section 7, lines 255–281, `comparator:high-label`. For every density matrix on
`(ℂ^q)^{⊗k}`, some actual Schur projector has trace mass at least
`(k+1)^{-q²}`. For an arbitrary unit vector with an auxiliary tensor factor,
the actual reduced density yields the same lower bound for the projected
Euclidean norm squared, and the projected vector is nonzero. Both statements
include zero copies and require no permutation invariance.

The mathematical source is frozen at
`cdb5485555253efc7156b619f9cec8c4153930fb`. The target build passes 3,101 jobs,
the complete source passes strict checking, and both exact stock-kernel
reports use only `propext`, `Classical.choice`, and `Quot.sound`. The one
owned original-provenance shard passes the TNLean validator and schema pinned
at `806099b4dddcce591b3a62ee1921926a6af5ad55`, with immutable complete-file
and raw-log bindings. The nine parent shards, their referenced production
files, and their bound raw evidence are byte-identical to main
`0c3485a499660de80843affa0b25b964c12a5193`. No fresh kernel audit of the 162
parent declarations is claimed.

The entropy-window and irreducible-dimension asymptotic, common Bell sequence,
positive occurrence on the initial uniform pair, auxiliary-label matching,
and energy assertions remain separate. The unique blueprint fragment states
only the generic mass estimates and is not yet included in the book at this
leaf revision.

The supplied initial cache metadata named the checkdecls revision as Mathlib.
That original record and raw log are preserved. A fresh successful prebuilt
cache fetch records the actual named Mathlib revision
`c55e6e786f49471c72fbddbec5415808896aec1e` and the `Mathlib.olean` guard.
The first kernel diagnostic failed the header and diagnostic-command linters;
its raw output and actual exit are preserved under `axioms-initial-header-failed`.
The final diagnostic has a proper module header and permits only the two
purposeful `#print` commands. Only its successful final output is used in the
provenance shard.

Complete library and blueprint inclusion checks are recorded separately in
`schurSectorMassIntegration8753` after the two inclusion lines are committed.
