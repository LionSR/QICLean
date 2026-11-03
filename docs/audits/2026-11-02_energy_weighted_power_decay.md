# Energy-weighted decay for the final ALVV power step

This contribution contains two conditional scalar estimates for the final
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

The isolated worktree starts at exact QICLean revision
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57` and has no `.lake` directory.
The complete module passed a fresh strict actual-name check in 13.161 seconds.
A separate imported foundation audit passed in 15.637 seconds; both public
declarations use only `propext`, `Classical.choice` and `Quot.sound`. The guarded
provider was the fully warmed revision `24a2ee589c5ff8da34a5cc6d8b7026dc7700e929`;
all three build inputs were required to equal the target revision. The new
module imports only Mathlib, so it reuses no changed QIC declaration objects.
All outputs are temporary; no production or dependency cache was changed.
No Mathlib source was rebuilt. Ordinary full and complete-book checks remain
separate pending gates. Foundation commands are confined to a temporary
audit and are absent from the contribution.

The source and proof contain no unfinished proof terms or extra assumptions.
The added-prose, whitespace and generated-import checks pass. A scan of the
new source found no repeated tactic patterns at the configured thresholds.
