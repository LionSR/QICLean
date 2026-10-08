# A sharp exponential estimate for an excitation component

Let \(Q,Y,V,C,R\) be five distinct tensor factors, and let \(\Omega\) be a
unit vector on \(Q\otimes Y\otimes V\). Suppose \(u\) is fixed by simultaneous
permutations of its physical, \(C\) and \(R\) copy strings. For a set \(B\)
of bad copies, define the physical excitation projection by

\[
R_B=\bigotimes_{i=1}^k R_i,\qquad
R_i=\begin{cases}
I-|\Omega\rangle\langle\Omega|,&i\in B,\\
|\Omega\rangle\langle\Omega|,&i\notin B.
\end{cases}
\]

Put

\[
m=|B^c|,\qquad w=(R_B\otimes I)u,\qquad M=\|w\|^2.
\]

Let \(\Gamma\) be the actual density of this component retaining all five
factors on the good copies and tracing only the bad copies. For each indicated
subsystem \(T\), let \(P_T^\lambda\) be its central copy-permutation label
projection and \(d_\lambda\) the irreducible representation dimension. Define

\[
\begin{aligned}
F_T&=\sum_\lambda(\log d_\lambda)P_T^\lambda,\\
G&=F_Q+F_V-F_Y,\\
D_C&=F_Q+F_C-F_{QC},\\
D_R&=F_V+F_R-F_{VR},\\
K&=\frac{(m+1)^{(|Q|\,|C|)^2}+(m+1)^{(|V|\,|R|)^2}}2.
\end{aligned}
\]

For \(T\in\{Q,Y,V\}\), let \(\sigma_T\) be the actual one-copy marginal of
\(|\Omega\rangle\langle\Omega|\), and write \(S_T=S(\sigma_T)\). Suppose
\(C_0\ge0\), \(c_0>0\), \(\mathcal B\ge1\), and, for every \(s\) with
\(|s|\le c_0/\sqrt{\mathcal B}\),

\[
\log\!\sum_{p>0} p e^{-s\log p}
\le sS_T+C_0\mathcal B s^2.
\]

where the sum runs over the positive eigenvalues of \(\sigma_T\), with
multiplicity. For \(a\ge0\) with
\(5a\le\min(c_0,1)/(2\sqrt{\mathcal B})\), the estimate is

\[
\begin{aligned}
&\operatorname{Re}\operatorname{Tr}\!\left(
\Gamma e^{a(D_C+D_R-G)}\right)\\
&\quad\le M K^{2/5}\exp\!\left\{
-am(S_Q+S_V-S_Y)+30C_0m\mathcal B a^2
+\frac{|Q|^2+|Y|^2+|V|^2}{10}\log(m+1)\right\}.
\end{aligned}
\]

The actual density is positive semidefinite. The seven regions
\(Q,C,QC,V,R,VR,Y\) are nested or disjoint, so their central observables
commute. Apply weighted five-factor Hölder to

\[
A_0=A_1=(D_C+D_R)/2,\qquad
A_2=-F_Q,\quad A_3=-F_V,\quad A_4=F_Y.
\]

The two half-sum moments at \(5a\) are each bounded by \(MK\), using the
actual sum-merge estimate at \(5a/2\). The three physical moments have
signs \(-5a,-5a,5a\). Each contributes \(50C_0m\mathcal B a^2\) and its
physical square dimension times \(\log(m+1)/2\) before taking the fifth
root. Thus their combined contributions are exactly \(30C_0m\mathcal B a^2\)
and the square-dimension sum times \(\log(m+1)/10\).

The argument never divides by \(M\). It includes the zero component and
zero good copies; when \(m=0\), \(K=1\) and the exponential factor is one.
The one-copy vector may be entangled across its three physical factors.

This is the auxiliary exponential estimate used before the inverse metric
and the good auxiliary scalar in OpenAI's September 24, 2026 area-law
manuscript, Section 7, lines 556–560. Its polynomial is obtained from the
arithmetic-mean sum-merge estimate. The analytic hypothesis is stated solely
for the three actual one-copy marginals, as in lines 75–85 and 227–238.
This estimate does not establish the full component inverse comparison.
