# Shared short-window leaf count

The full dimension on four window lengths fits the common node count:
for q ≤ m, m ≥ 2, ell ≥ 1 and s ≥ 1, with
D = (m ell²)^(22 ell), one has q^(4 ell) ≤ D^6 s^3.
This pure natural-number proof is shared by both earlier physical tree
constructions and the actual canonical sampling-data construction. The
window length ell is distinct from the independent energy cutoff t.

The proof uses existing power monotonicity and the identity for a power
of a power. The library's repeated proof was extracted without changing
its mathematics. This is a numerical auxiliary for ALVV,
arXiv:1602.08828v2, initialization at lines 1650–1662, rather than a
statement about the dimension of a long physical region.

The source-only branch starts from QIC a6f67c7d. The final actual-name
strict check passed in 4.565 seconds against held TN 435cbe7fe5 / own
QIC b2ea12a0, using prebuilt Mathlib only and all exact source/object,
root-input and Mathlib guards. The combined nine-public inspection,
including the actual tree and the refactored earlier consumers, passed
in 7.785 seconds with 785 protected pairs. This arithmetic lemma uses
only propext and Quot.sound; every inspected declaration uses at most
the standard three axioms. The temporary inspection was deleted.

Generated imports, source blueprint synchronization, reader-facing prose,
proof integrity and whitespace checks passed. No proof budget was raised.
The worktree has no .lake. No provider or cache was modified, no compiled
artifact was copied and no Mathlib source was built. Canonical ordinary
and compiled-book gates remain part of the coordinated integration.
