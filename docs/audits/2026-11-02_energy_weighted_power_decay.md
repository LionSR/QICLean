# Energy-weighted decay for the final ALVV power step

This note contains two conditional scalar estimates for the final
power step in ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1811–1815. A finite
geometric sum proves

    x(1-x)^tau <= 1/(tau+1),        0 <= x <= 1.

Consequently, if A>0, 0<gamma<=s<=A and (tau+1)gamma>=A, then

    s(1-s/A)^(2tau) <= gamma(1-gamma/A)^tau.

The integer tau may be zero; the hypotheses force equality of A, gamma
and s in that case. The unit-interval endpoints are included.

The first estimate follows by comparing every term of the geometric sum
with its last term. For the second, apply it at x=s/A, bound A/(tau+1)
by gamma, and use the monotonicity of the remaining nonnegative power.
The proof uses existing Mathlib geometric-sum and power-order lemmas.

These are explicit scalar auxiliaries. They do not prove the operator
energy estimate, the repeated collective trimming sequence, the actual
compressed eigenvector extraction, or the final algorithm theorem.
No assertion that the source's overlap recurrence is false is made here;
the applicability of its not-yet-converged branch is a separate question.
