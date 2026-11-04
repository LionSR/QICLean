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
