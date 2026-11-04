# Energy bounds on a common low-energy compression

`Analysis/CommonCompressionEnergy.lean` proves three abstract estimates used in
AKLV, arXiv:1301.1162v1, Section 6.3, Lemma 6.5. The estimates do not require an
upper bound on either exterior Hamiltonian or on the full Hamiltonian norm.

Let \(P\) be the orthogonal projection onto a subspace \(U\), and let \(Q=I-P\).
A lower bound \(tQ\le B\) gives
\(t\|Qv\|^2\le\operatorname{Re}\langle v,Bv\rangle\).
If \(B\ge0\), \(H\) agrees with \(B\) on \(U\), and \([P,B-A]=0\), then

\[
\operatorname{Re}\langle Pv,HPv\rangle
\le\operatorname{Re}\langle v,Bv\rangle+2\|A\|\|v\|\|Qv\|.
\]

For a unit vector of truncated energy at most \(e\ge0\), with \(t>0\), these give
\(\|Qv\|\le\sqrt{e/t}\) and projected original energy at most
\(e+2\|A\|\sqrt{e/t}\).

The proof splits \(v=Pv+Qv\). Commutation removes the contribution of \(B-A\)
from the off-diagonal block. Positivity controls the high-sector diagonal term,
and Cauchy--Schwarz bounds the remaining connecting operator by its actual norm.
No eigenbasis, perturbation residual or closeness estimate is assumed.

These are abstract auxiliary results, not the final physical statement of
Lemma 6.5. The common compression, equality on its range, commutation and high-sector
floor are explicit hypotheses. A physical application must derive them from the
actual two exterior clippings and use the source's bound on the two connecting
positive contractions. The new blueprint states these hypotheses explicitly;
it does not mark the physical source lemma as completed.

Production SHA-256:
`b8e75762816e61106dd6d1350b430acb3fbbfcf92507d8833856c78a28964824`.
All three imported public declarations have only `propext`, `Classical.choice`,
and `Quot.sound`; manual inspection passes in 13.70 seconds. Inspection commands
and objects remain temporary, with no permanent fixture. The source-to-blueprint
declaration and reader-facing prose checks pass.

The actual production source passes strict private compilation in 4.20 seconds,
with strict implicit arguments, Mathlib standard linters and warnings as errors.
It imports only Mathlib. Checks use the read-only TNLean provider
`8153728de51a3a489c932a8f377690c764892326`, with its exact prebuilt Mathlib toolchain
and companion context `b66600027b2e60ccafea43d041d563cdd00cf05b`. All new outputs are
private temporary objects; no dependency source is rebuilt and no cache is copied
or mutated. Ordinary verification in the current common QICLean integration tree
and compiled blueprint checks remain pending. No ordinary build is queued by this
contribution. Generated aggregators and chapter input registration are excluded.
