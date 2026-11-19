# Dimensions of labels occurring on the bad copies

Fix a split of the \(k\) copy coordinates into groups of sizes \(m\) and
\(r\), with \(m+r=k\). Let \(C\) be a finite coordinate set, and let
\(S_r\) act on \(\mathbb C^{C^k}\) by permuting the second group and
fixing the first. If the central projection of an irreducible label
\(\beta\) is nonzero for this actual action, then
\[
 d_\beta\le |C|^r.
\]
The good-copy factors remain present in the representation space.
Their multiplicity does not appear in the estimate.

The proof uses the actual entries of the permutation operators. In the
specified split, the label projection has entries
\[
 P_\beta(x,y)=\mathbf 1_{x_g=y_g}P^{(r)}_\beta(x_b,y_b).
\]
Consequently a nonzero projection on all \(k\) copies forces the actual
\(r\)-copy projection to be nonzero. Its range is a nonzero invariant
subspace of the \(\beta\)-isotypic component. The existing irreducible
dimension estimate therefore bounds \(d_\beta\) by the dimension of
this range, which is at most the ambient dimension \(|C|^r\).

The statement includes \(C=\varnothing\), \(m=0\), and \(r=0\).
No nonempty coordinate-set hypothesis or chosen irreducible copy is needed.

The source is *A two-dimensional area law from a global spectral gap*,
pinned `openai/math` revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`07-comparators.tex`, lines 490–493, equation `comparator:good-auxiliary`.
This establishes the bad-copy dimension estimate appearing in that argument.
It does not by itself establish the lower bound for the good auxiliary
observables: that step also uses preservation of whole-copy auxiliary
labels by the actual physical excitation projection and the whole-label
threshold. The logarithmic subgroup operator inequalities are proved
separately.
