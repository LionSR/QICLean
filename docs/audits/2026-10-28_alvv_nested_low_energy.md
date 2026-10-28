# Nested-target error reduction for low-energy subspaces

The source is Arad, Landau, Vazirani and Vidick,
[arXiv:1602.08828v2](https://arxiv.org/abs/1602.08828v2), Theorem
`t:aisgapless`, lines 1027–1041 of `local_alg_arxiv_v2.tex`.
The exact source TeX has SHA256
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

The new operator theorem assumes nested finite-dimensional subspaces
$T_-\subseteq T_+$ and closeness of $U$ to $T_+$. The filter expands on
$T_-$ and contracts on $T_+^\perp$, preserving both spaces. It follows
that $KU$ is $\Delta/(1-\delta)^2$-close to $T_-$. No action on the
intermediate band is assumed. A tensor decomposition gives the corresponding
viable-space enlargement, with dimension multiplied by the number of terms.

The spectral consequence uses the two actual spectral spans at the filter's
lower and upper endpoints. It requires no spectral gap between them. This
removes the same-target gap requirement from the earlier spectral reduction
when applying it to low-energy states. The existing same-target results are
specializations of the generalized operator and tensor arguments, with their
statements preserved.

These are supporting theorems for a supplied finite tensor decomposition.
They do not assert a physical filter construction, the low-density area law,
or the binary-tree algorithm. The next physical tasks are one-sided
closeness at shifted energy cutoffs, the low-energy improving family, and the
dyadic minimal-dimension bootstrap in Proposition `prop:albootstrap-ld`,
lines 1111–1128. The efficient soft-truncation route also requires repair of
the separately documented false printed cluster-expansion estimate.

The work is based on exact QICLean revision
`af7e5c90650e5ddb06c2befac508df97fd20b2e3`. Changed modules are checked
separately with the strict production options, against prebuilt dependencies
and private outputs. Ordinary full-library and compiled blueprint verification
remain separate requirements. No permanent theorem-test files are added.
