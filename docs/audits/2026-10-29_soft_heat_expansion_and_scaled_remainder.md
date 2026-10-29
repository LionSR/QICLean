# Finite heat expansion and independent-scale soft remainder

Date: 29 October 2026.

The existing soft function has the exact expansion

$$h_{m,t}(x)=\sum_{a=0}^m c_a e^{-ax/t},\qquad
c_a=t(-1)^a\sum_{j=1}^m\frac{\binom ja}{j},\qquad
\sum_{a=0}^m|c_a|\leq t2^{m+1}\quad(t\geq0).$$

The constant heat and the scale factor are retained. The binomial theorem, finite sum interchange and the exponential power identity prove the scalar equality; finite Hermitian functional calculus gives the equality for the same matrix. No local support, state or ground-energy hypothesis enters this finite algebra.

The exact scaling identity $h_{m,t}(x)=(t/s)h_{m,s}(sx/t)$ reuses the existing equal-scale weighted remainder. Choosing its weight $\theta=t/(8m)$ gives

$$x-h_{m,t}(x)\leq16e^{x/8-t/16}\qquad(m\geq1,\ 0<t\leq4m,\ x\geq0).$$

The common same-matrix factorization proves

$$\|(U-h_{m,t}(U))|_G\|\leq16e^{-t/16}\|e^{U/8}|_G\|$$

for positive $U$ and any subspace $G$. The existing equal-scale public theorem now specializes this result; its statement is unchanged. The factorization itself is public at arbitrary real scale and every order, for a Hermitian matrix. No physical moment is supplied or proved in this matrix result.

The existing reverse cutoff proof is generalized to independent scale with $\alpha=(t/2)2^{-m}$ and actual cutoff $t/2-10$; its old equal-scale public statement remains as a specialization. The elementary equal-scale correction bound $(m/2)2^{-m}\leq1/4$ is made public and reused for the new scale-three order. Its explicit logarithmic ceiling gives $\alpha\leq3/4$, the reverse cutoff and any prescribed positive residual budget at $t=3m$.

The separate general scalar ceiling theorem chooses an actual positive order for $W(e^{N^2b^\ell}-1)$ when $W>0$, $0<b<1$ and the target error is positive. It makes no computational complexity assertion. Together these results support the corrected one-interval physical construction in TNLean; they do not revive the false printed uniform energy or physical-support cluster assertions.

Source passages: ALVV, arXiv:1602.08828v2, `def:ft`, lines 1152–1157, `def:soft-trunc`, lines 1178–1185, and `lem:exp-approx-eff`, lines 1262–1268. The corrected physical scope is recorded in the existing TNLean notes at https://sirui-lu.com/TNLean/paper-gaps/alvv16_soft_truncation_energy_estimate.pdf and https://sirui-lu.com/TNLean/paper-gaps/alvv16_cluster_approximation.pdf. These TNLean-owned notes are not copied into QICLean.

There are four new generic analysis modules and three small existing-module refactors. They add twelve public declarations; all sixteen public declarations of the changed QICLean modules are included in the imported foundation audit. Only `propext`, `Classical.choice` and `Quot.sound` occur. The proof sources pass the repository strict flags against frozen QICLean `ec3434f7d6fbdfc5318dc55934feb9532e239b81` within checked TNLean `7f87bdc8f1b2354be4950ad515dedda7ee9bec96`, with selected source/object guards and temporary outputs.

No dependency cache or provider source is copied or changed, and no Mathlib source or ordinary build is run. The new mathematical book entries render cleanly, and the private audit commands are absent from the proposed production patch. Ordinary integration, complete companion regressions and common book gates remain pending.
