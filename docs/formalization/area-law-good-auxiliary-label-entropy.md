# A whole-space bound for the good auxiliary labels

Let a finite coordinate set \(C\), of cardinality \(d\), carry the actual
copy-permutation action on \(\mathbb C^{C^k}\). Specify groups of \(m\)
good and \(r\) bad copies, with \(m+r=k\). Write \(F_g,F_b,F_w\) for
the logarithmic central label observables of these groups and of all copies.
Then the whole-space operator inequalities are
\[
 F_b\le r\log d\,I,\qquad
 F_w\le F_g+\left(r\log d+\log\binom{k}{r}\right)I.
\]
Use the real logarithm extended by \(\log0=0\). Empty coordinate sets and
zero copy groups are included. On positive-dimensional physical spaces,
this is the ordinary real logarithm.

The bad-copy dimension result bounds every label that actually occurs by
\(d^r\). Its irreducible dimension is positive, so logarithmic monotonicity
applies on each nonzero central projection. Summing the scalar bound over
the actual label resolution yields the first order inequality. Combining
it with the subgroup order comparison yields the second. No chosen
irreducible copy, scalar dimension estimate or projection resolution is
supplied as a hypothesis.

The source is *A two-dimensional area law from a global spectral gap*,
pinned `openai/math` revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`07-comparators.tex`, lines 481–493, equation `comparator:good-auxiliary`.
This result is its operator input before the physical excitation component
is selected. The whole-label threshold and the preservation of whole-copy
auxiliary labels under the actual physical projection are separate steps.
In particular, this result does not commute an individual excitation
projection through the band metric.
