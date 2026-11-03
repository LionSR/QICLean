# A logarithmic count for the final refinement recurrence

For 0 < c ≤ 1 and 0 < η ≤ 1, the previously proved recurrence gives
u_j ≤ (1 − c/4)^j u_0 + η/2. The new estimates bound the geometric
factor by exp(−cj/4), and therefore reach u_j ≤ η after the explicit
positive number ceil((4/c) log(1/η)) + 1 of steps.

These are numerical lemmas. They do not by themselves construct the physical
subspaces or identify η with the requested energy accuracy in Algorithm 1 of
ALVV, arXiv:1602.08828v2. In particular, they do not establish the printed
iteration count for the final spectral extraction. The energy-weighted
filter estimate is a separate ingredient of that comparison.
