# Common parameters for two soft-truncation residuals

For every nonnegative ceiling B and positive error epsilon, the new scalar
lemma constructs one cutoff T >= B and a Taylor order m >= 2. The scale is
exactly t = 3m and satisfies t >= B. For every offset b <= B, it proves

    3[32 exp(-(T-b)/8) + (t/m)(T/t)^m] <= epsilon.

The proof first takes X = max(1,192/epsilon) and T = B + 8 log X.
Then 32 exp(-(T-b)/8) <= epsilon/6. Mathlib's
exists_pow_lt_of_lt_one supplies k with 2^(-k) < epsilon/18.
An integer m >= max(2,k,2T/3) gives T/(3m) <= 1/2, so the power
remainder is at most 3*2^(-m) <= epsilon/6. One general offset estimate
therefore controls both physical residuals without repeating the argument.

For arbitrary g,tau > 0, the specialization uses B = 156+2g and
epsilon = tau*g/1000000. It returns m,t,T with t,T >= 156+2g and
T >= g/40+24, and proves both residual budgets at the same cutoff T.
Thus the physical argument may set T0=T1=T. The equality t=3m implies
the required inequality t>=3m; the order m>=2 also implies t>0.
No spectral gap, residual bound, family or subspace comparison is assumed
by either scalar theorem. These are supporting numerical statements for
ALVV arXiv:1602.08828v2, lem:exp-approx and t:aisefficient, lines
1195-1255 and 1373-1420, rather than a claim about its running time.
No quantitative growth estimate for the chosen order is asserted.

## Verification

The complete Mathlib-only production module passes actual-name strict
checking at default limits in 4.040 seconds. The immutable provider is
TNLean 88ab31ce57bdbc4bcb65be00055d1db50df4f259 with its own QICLean
package e817ea0a8a46440eddc361d41cc46b9e61ba10f4. The source-only
worktree starts at QICLean 1ff75c9843ffd378fa98ea785d54bfc51fa01500;
its toolchain and dependency/build inputs are byte-identical to those of
the verified package. The new leaf imports no QICLean or TNLean module.
The shared private elaboration lock serialized its checks with those of
other agents. The initial incomplete proofs and one missing inequality
in a restricted arithmetic context are not counted as successful checks.

Both public declarations pass an imported foundation inspection in
3.596 seconds, with only propext, Classical.choice and Quot.sound.
The temporary command source was deleted after the inspection. Generated
imports, complete source/blueprint synchronization, reverse coverage of
both public declarations, reader prose, proof integrity, whitespace and
the tactic-pattern scan pass. The theorem and corollary were rendered
and their one-page layout was inspected. Ordinary combined compilation
and complete compiled blueprint declarations remain integration checks.
No provider, cache, dependency pin or Mathlib source was changed or built.
