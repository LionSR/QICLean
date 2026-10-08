# Typical Schmidt truncation of an actual pure state

The reference is OpenAI, *A two-dimensional area law from a global spectral gap*
(September 24, 2026), at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The selected Schmidt vector is defined in `07-comparators.tex`, lines 240–247;
the complementary marginal estimates are equation `comparator:post-marginal`.

For a normalized vector on a finite bipartite Hilbert space, the selected spectral
projection of its actual first marginal acts on the first tensor factor. Dividing
the resulting vector by the square root of the selected mass gives a normalized
pure state. No full-rank assumption or ordering of the two dimensions is required.
The unselected spectrum may contain zeros.

Writing the coefficient matrix as $C$, the complementary-marginal decomposition
is the identity

$$
C^*C=(PC)^*(PC)+((I-P)C)^*((I-P)C).
$$

Orthogonality of the selected and discarded subspaces removes the cross terms.
The normalized selected marginal is bounded in positive-semidefinite order by
the original marginal divided by the selected mass. Entropy concavity gives the
corresponding entropy estimate. The case of selected mass one does not require
normalizing the zero remainder.

For an additional tensor factor, a further partial trace gives the same exact
decomposition and inequalities on every subsystem of the complement. The
selected and discarded contributions remain positive, and their traces are
preserved. Entropy concavity applies directly to these actual subsystem
marginals; no spectral truncation on the enlarged region is assumed. This
covers the disjoint-subsystem quantifier in `comparator:post-marginal`.

All proof text is independently written from the manuscript. Codex (GPT-6) assisted
the formalization; no upstream Lean proof text was copied or adapted.
