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
