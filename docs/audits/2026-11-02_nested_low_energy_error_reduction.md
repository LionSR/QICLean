# Error reduction between two low-energy cutoffs

The operator, tensor-containment and spectral arguments now allow distinct
lower and upper targets. For $T\subseteq T_+$, the operator need only expand
on $T$ and contract $T_+^\perp$ into $T^\perp$. It is not required to
contract the intervening spectral band. The resulting error is
$\Delta/(1-\delta)^2$ for $\delta<1$.

This is an auxiliary step for ALVV, arXiv:1602.08828v2, Theorem
`t:aisgapless`, lines 1027–1041. It is not the physical construction of the
filter or a completion of the low-density area law. The new matrix
Chebyshev composition explicitly assumes a common finite polynomial
decomposition. The physical chain argument must derive that decomposition
from its supported interactions. Closed spectral cutoffs and the absence
of a positivity claim for an oscillating Chebyshev polynomial follow the
existing spectral-boundary and Chebyshev-positivity notes.

The single-target public statements are specializations. The old spectral
contraction statement also retains its explicit spectral-gap assumption;
the new two-cutoff statement needs none. The canonical-coordinate argument
uses coincident endpoints solely to identify the actual conjugated
eigenspaces, not to assert a gap between the new cutoffs.
