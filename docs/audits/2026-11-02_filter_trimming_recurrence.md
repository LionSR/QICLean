# A stable numerical recurrence for repeated filtering

The normalized projection estimate gives error
(1−c)δ/(1−δ+(1−c)δ) for a filter with squared-norm contraction 1−c.
For 0<c≤1 and 0≤δ≤1/2, this is at most (1−c/2)δ.
A weighted perturbation estimate with additional error ε≤c²η/40
therefore gives the upper recurrence

    δ′ ≤ (1−c/4)δ+cη/8.

For 0<η≤1 this preserves the upper bound one half and yields
δ_j≤(1−c/4)^jδ_0+η/2. In particular a finite number of rounds reaches
error at most η.

These four numerical results support the final repeated filtering in
ALVV, arXiv:1602.08828v2, Algorithm t:alg1, lines 1634–1640.
They do not assume or prove that collective trimming approximates every
vector in the entire filtered subspace.
The source argument instead uses a reference space of low Schmidt rank;
its target-relative trimming estimate, choice of reference accuracy,
actual sequence of retained subspaces, quantitative round count and
compressed spectral extraction remain separate tasks.
