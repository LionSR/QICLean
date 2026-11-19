# The label observable under a split of the copies

Let a permutation representation of the symmetric group on \(k\) letters act on a
finite-dimensional coordinate space. Fix a decomposition of the letters into groups
of sizes \(m\) and \(r\), so that \(m+r=k\). Write \(F_g,F_b,F_w\) for the
central observables whose values are the logarithms of the irreducible dimensions
for the first group, the second group, and the full symmetric group. Then
\[
 F_g+F_b\le F_w\le F_g+F_b+\log\binom{k}{r}\,I.
\]
These are inequalities on the whole coordinate space. There is no hypothesis that a
specified triple of labels occurs.

The good, bad, and whole label projections commute and have sums equal to the
identity. Their products therefore give a joint orthogonal decomposition. Every
nonzero product corresponds to a compatible restriction triple. Lemma 6.1(4) gives
\(d_\alpha d_\beta\le d_\lambda\le\binom{k}{r}d_\alpha d_\beta\).
Taking logarithms proves the scalar inequalities on this joint component. Summing
over the components proves the two matrix inequalities. Vanishing components make
no contribution. The statement includes empty groups.

The source is *A two-dimensional area law from a global spectral gap*, pinned
`openai/math` revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`05-replicas.tex`, Lemma 6.1(4), lines 116–123, and `07-comparators.tex`,
lines 455–467, equation `comparator:restriction-dimensions`.

This result supplies the operator form of the subgroup dimension comparison. The
later good-auxiliary estimate also requires the bound on the dimensions of labels
that actually occur on the bad copies and the preservation of the whole-copy
auxiliary labels by a physical excitation projection. Those assertions are separate.
The inverse-metric estimate additionally needs the actual band metric and its
logarithmic approximation; it does not follow by commuting an individual excitation
projection through that metric.
