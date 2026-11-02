# Soft truncation, heat expansions and spectral comparisons

This contribution supplies finite-dimensional estimates used in the corrected
one-interval soft truncation of Arad, Landau, Vazirani and Vidick. It does not
assert the printed uniform power estimate or a matrix product operator
construction. The latter is developed separately in TNLean.

## Mathematical statements

For the existing soft function
\(h_{m,t}(x)=t\sum_{j=1}^{m}(1-e^{-x/t})^j/j\), the geometric remainder
bound and its exponential majorant imply
\[
0\le x-h_{m,t}(x)\le16e^{x/8-t/16}
\qquad(x\ge0,\ m\ge1,\ 0<t\le4m).
\]
The matrix estimate factors the actual functional-calculus remainder through
an exponential of the same Hermitian matrix. Restricting to a subspace then
reduces the residual estimate to an exponentially weighted restriction norm.
Shifted hard-cutoff comparisons give the lower bounds needed on the reverse
spectral window.

The finite heat expansion retains every coefficient, including the constant
term:
\[
h_{m,t}(x)=\sum_{a=0}^{m}c_a e^{-ax/t},\qquad
c_a=t(-1)^a\sum_{j=1}^{m}\frac{\binom ja}{j},\qquad
\sum_{a=0}^{m}|c_a|\le t2^{m+1}\quad(t\ge0).
\]
An explicit logarithmic ceiling controls the geometric cluster tail. A
separate order choice at scale \(t=3m\) gives the prescribed residual budget
while every heat time is at most \(1/3\).

For Hermitian matrices \(A,B\), residuals bounded by \(\xi\) on their own
low-energy spaces of width \(\eta>0\) give
\(|\lambda_{\min}(A)-\lambda_{\min}(B)|\le\xi\). If
\(0<\xi\le1\), \(\xi\le w/2\), and
\(2(\eta+2)\xi\le\delta w^2\), each such space is approximated, with squared
distance at most \(\delta\), by the other matrix's space enlarged by \(w\).
No spectral gap or ground-space dimension is supplied.

The inclusion--exclusion estimate for required interaction labels retains
its energy normalization: when \(H\ge\lambda I\), \(H,h_i\) are Hermitian,
\(\|h_i\|\le1\), and \(t\ge0\),
\[
e^{t\lambda}
\left\|\sum_{D\subseteq S}(-1)^{|D|}
 e^{-t(H-\sum_{i\in D}h_i)}\right\|
\le(e^t-1)^{|S|}.
\]
The accompanying coefficient bound groups finite inclusion--exclusion by
the union of selected windows. Neither assertion identifies interaction
labels with minimal physical support.

## Source and scope

The source is arXiv:1602.08828v2, `def:ft` (lines 1152–1157),
`def:soft-trunc` (1178–1185), `lem:exp-approx` (1195–1255),
`lem:exp-approx-eff` (1262–1268), and the cluster argument (1935–1968).
The local TNLean source is `References/1602.08828/local_alg_arxiv_v2.tex`.
These are supporting estimates for a corrected argument, rather than
formalizations of the false printed energy and spatial-cluster bounds.
The existing scalar logarithmic-bound note is unchanged. The required-label
estimate cites the [TNLean cluster note](https://sirui-lu.com/TNLean/paper-gaps/alvv16_cluster_approximation.pdf).

The proofs are extracted from local QICLean revision
`e51354163d2dd9cf2a15d65722c544c6b4736182` onto public main
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`. Fifteen missing modules are added.
The additional scalar lemmas are appended to `SoftTruncation.lean`, retaining
main's stronger explanation of the logarithmic-bound counterexample.
Unrelated older definitions and proofs are not restored.

## Verification

The hosted Lean build and module-policy checks passed at revision
`b8a65f02` in [run 41484812574](https://github.com/LionSR/QICLean/actions/runs/41484812574).
Local compilation and compiled declaration and axiom checks are pending.
The blueprint source check passes. The first hosted blueprint run found a
missing author in the added bibliography entry; that entry is corrected, and
local bibliography generation now succeeds. The new estimates are supporting lemmas;
no source-labelled false claim is marked proved.

All 32 newly public declarations have active blueprint references. The active
blueprint has no duplicate labels, and every reference in the changed sections
resolves. The new sources contain no forbidden proof tokens. The changed
sections pass the pinned formatter and individual-file LaTeX lint checks.
