# Two-sided operator Schmidt bounds from designated supports

Date: 29 October 2026.

For a finite tensor product with arbitrary nonnegative local dimensions $n_v$, an operator $T$ supported on $X$ satisfies

$$ \operatorname{OSR}_A(T)\leq\min\left\{\left(\prod_{v\in X\cap A}n_v\right)^2,\left(\prod_{v\in X\setminus A}n_v\right)^2\right\}. $$

The existing left-side estimate is reused. The new factor-exchange identity follows because the realigned matrix is transposed. Complementary cut coordinates are related by that exchange and separate coordinate equivalences; consequently their operator Schmidt ranks agree. Applying the existing estimate to $A$ and $A^c$ proves the minimum bound. If the local dimensions all equal $q\geq1$, then twice the smaller part of $X$ is at most $|X|$, giving $\operatorname{OSR}_A(T)\leq q^{|X|}$.

There is no hypothesis about a state, a gap, Hermiticity or positivity. The minimum bound includes zero local dimensions and empty configuration spaces; the uniform exponential corollary explicitly requires $q\geq1$. These generic results support the actual interval calculation in ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013, without asserting the printed physical-support approximation. Matrix realignment is also the decomposition characterization in arXiv:1903.05373, equation (1).

The four new public declarations are `Matrix.operatorSchmidtRank_reindex_prodComm`, `Entropy.operatorSchmidtRank_cutOperator_compl_eq`, `Entropy.IsSupportedOn.operatorSchmidtRank_cutOperator_le_min`, and `Entropy.IsSupportedOn.operatorSchmidtRank_cutOperator_le_pow_card`. They extend the existing two source modules and reuse their existing public declarations. Their mathematical signatures are independently checked through a compiled import; all four use only `propext`, `Classical.choice` and `Quot.sound`.

Private strict checks use the frozen QICLean package `4276de2eeb5c4122f4482ef5e4fa205be5b71bd9` within checked TNLean `f93bc77b3dddcc292125eea18b96af153225251b`, with explicit source/object guards and temporary outputs. No provider/cache mutation, Mathlib source build or ordinary build is performed. The final modified source checks take 2.19 and 3.09 seconds. Both new mathematical book entries render cleanly and the private foundation audit commands are excluded from the production patch. Ordinary integration and complete common book gates remain pending.
