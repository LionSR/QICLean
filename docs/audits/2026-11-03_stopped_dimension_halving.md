# A prescribed number of dimension-halving rounds

Let a sequence of nonnegative integers halve above a threshold h and not
increase below that threshold. If h is at least two and its initial value
is at most 2^R, then it is below h after R rounds. For a chain of L sites
of local dimension q, the ambient bound q^L permits the predetermined
choice R=qL. The cases q=0 and L=0 are included.

The proof keeps a single alternative: at round i the dimension is already
below h, or its product with 2^i is at most the initial dimension. The
chain consequence uses q<2^q. Both estimates use the existing natural-number
quotient and power lemmas.

These are numerical auxiliaries for repeated amplification associated with
ALVV, arXiv:1602.08828v2, section on the merge process, lines 711–736, and
the degenerate algorithm, lines 1783–1817. The theorem does not construct
random subspaces, establish viability or give a running-time bound. In
particular, it does not identify repeated resampling with the displayed
sample-once procedure.

## Verification

The production module passes strict elaboration in 2.433 seconds against
the fully built TNLean 8f85b0be / QICLean cc2569b6 pair. Its only import is
Mathlib.Data.Nat.Log. The check retains the standard linters, warnings as
errors and default proof-resource limits. An imported foundation inspection
passes in 2.409 seconds; both declarations use only propext and Quot.sound.
The temporary inspection source is deleted.

Complete source/blueprint synchronization and reverse coverage, generated
imports, reader-facing prose, forbidden-token and whitespace checks pass.
Both new entries are supporting lemmas. Their one-page mathematical excerpt
was rendered and inspected, with no overfull boxes. The tactic-pattern
ledger records the single induction shared by the two conclusions.

Ordinary combined build and compiled blueprint verification remain pending
for this new contribution. No held provider or ordinary build artifact was
changed by these private checks. No Mathlib source was built.
