# Good auxiliary spectral support

Let the five finite-dimensional factors be $Q,Y,V,C,R$, in that order.
The one-copy physical vector \(\Omega\) lies in
\(\mathcal H_Q\otimes\mathcal H_Y\otimes\mathcal H_V\) and need not be
normalized. Let \(u\) be an arbitrary vector on the $k$ physical copies
and the two auxiliary copy registers. Suppose that its whole-copy auxiliary
labels are \(\lambda_C\) and \(\lambda_R\).

For an excited subset \(B\subseteq\{1,\ldots,k\}\), apply the literal
physical excitation operator to obtain the same component \(w_B\).
Write \(r=|B|\) and \(m=k-r\). The density \(\Gamma_B\) is obtained
from \(|w_B\rangle\langle w_B|\) by tracing the bad physical and auxiliary
copies. It retains all five factors on the good copies, including every
middle physical coordinate $Y$. The chosen enumeration of $B^c$ is the
same in each retained factor.

Let \(F_C\) and \(F_R\) denote the logarithms of the irreducible
representation dimensions in the good-copy auxiliary label decompositions.
Set

\[
 L_C=\log d_{\lambda_C}-r\log\dim\mathcal H_C-\log\binom{k}{r},
 \qquad
 L_R=\log d_{\lambda_R}-r\log\dim\mathcal H_R-\log\binom{k}{r}.
\]

The spectral-support conclusion is

\[
 \mathbf1_{[L_C,\infty)}(F_C)\Gamma_B=\Gamma_B,
 \qquad
 \mathbf1_{[L_R,\infty)}(F_R)\Gamma_B=\Gamma_B.
\]

The whole-copy auxiliary projections commute with the physical excitation
operator. Restriction of the auxiliary representations gives a lower bound
on each compressed good-copy observable. Because that observable commutes
with the corresponding whole-copy projection, the lower bound gives closed
spectral support at the stated threshold. Splitting the coordinates and
tracing the bad copies then preserves this support.

The assumptions concern the original vector's auxiliary labels. No
normalization, nonzero component, original permutation symmetry, or assumed
reduced-density identity is required. This statement is an auxiliary to
the component inverse estimate; it does not assert a comparison with a
band metric.

References: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 7, `comparator:good-auxiliary`, lines 441–456 and
481–493. The physical factors occur in lines 23 and 103–110, and the good-copy
reduction in lines 520–549, at manuscript revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
