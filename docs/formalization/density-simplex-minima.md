# Regularized density-simplex minima

The finite simplex calculation in the polynomial PEPS patch construction is
proved in `QICLean/Analysis/DensitySimplex.lean`. The mathematical source is
OpenAI's September 24, 2026 manuscript, Section 4, `03-patches.tex`, lines
170–200, equations `eq:patch-simplex-derivative`, `eq:patch-kkt`, and
`eq:patch-clipped-eigenvalues`, at immutable source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The general theorem starts with a genuine minimum on the closed probability
simplex and a genuine Fréchet derivative
\(Df(x)v=-c\sum_i p_i v_i/(x_i+b)\), where \(b,c>0\) and both \(x,p\)
are probability vectors. Testing feasible directions from \(x\) to the
simplex vertices proves the necessary inequalities. Their weighted average
then proves equality on the positive support of \(x\). This gives a multiplier
\(0<\lambda\le1\) and the clipped equation
\(x_i+b=\max\{p_i/\lambda,b\}\). Neither interior feasibility nor strictly
positive marginal probabilities are required.

The concrete application is the actual last-filter squared norm
\[
F(y)=\sum_i r_i(y_i+b)^{-a},\qquad
p_i(x)=\frac{r_i(x_i+b)^{-a}}{F(x)}.
\]
Here \(a,b>0\), the initial weights are nonnegative with positive total mass,
and \(x\) is an actual simplex minimizer of \(F\). The derivative is proved,
not assumed. The filtered weights are nonnegative and sum to one; their
clipped equation follows from the general theorem with \(c=aF(x)>0\).
Initial total mass need not be one, since it cancels in the normalized output.

These results establish the diagonal last-filter calculation. They do not
establish descending commutation or the simplex derivative for an earlier
factor in a nested noncommuting chain. In that argument, only the derivative
at a minimizing tuple becomes a separable expression after trace stripping;
the coordinate objective is not asserted to be separable away from that tuple.
The full Proposition 4.1 remains a separate theorem.

The regression file checks a genuine boundary minimum with a zero input weight,
a feasible nonminimizer, and the necessity of a positive exponent: at exponent
zero a minimizer can have no positive multiplier satisfying the support equation.

All proof text is independently written from the mathematical manuscript and
Mathlib. No OpenAI Lean proof text was reused. OpenAI Codex (GPT-6) assisted with
proofs, source comparison, tests, and documentation. Human mathematical review
remains a separate requirement.
