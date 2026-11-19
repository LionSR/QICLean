# The good auxiliary observable on a whole label

For the actual copy-permutation representation on a finite coordinate
tensor power, let $P_\lambda$ denote a whole-copy central projection and
$F_g$ the good-copy logarithmic label observable. If $m+r=k$ and $d=|C|$,
then $F_g$ commutes with $P_\lambda$ and
\[
 (\log d_\lambda-r\log d-\log\binom{k}{r})P_\lambda
 \le P_\lambda F_gP_\lambda.
\]
This follows by compressing the derived whole-space bound
$F_w\le F_g+(r\log d+\log\binom{k}{r})I$. The actual central projection is
Hermitian and idempotent, and its whole-copy observable eigenvalue is
$\log d_\lambda$. Subgroup permutation operators commute with the whole
central projection; their central linear combination therefore does too.
No dimension inequality, commutation relation, occurrence assumption or
projection resolution is supplied as an extra hypothesis.

Labels that do not occur have zero projection. Empty coordinate sets and
zero copy groups are included using the total logarithm with $\log0=0$.
The source is *A two-dimensional area law from a global spectral gap*,
pinned `openai/math` revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`07-comparators.tex`, lines 481–493, equation `comparator:good-auxiliary`,
with the restriction comparison from Lemma 6.1(4), `05-replicas.tex`,
lines 116–123. This proves the whole-label support compression. Preservation
of that label on a physical excitation component, the numerical whole-label
threshold and the subsequent metric estimate are separate assertions.
