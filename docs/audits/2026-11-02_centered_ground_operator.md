# Centering at the ground energy

For a Hermitian matrix H with spectral lower bound mu and mu ≤ ||H||,
the centered matrix C = H − mu I is positive and has norm at most
||H|| − mu. The proof uses Mathlib spectral order and its characterization
of the norm of a positive operator by scalar order bounds.

The full spectral span at cutoff mu lies in ker C: every selected
eigenvalue equals mu, and the kernel contains their span. No simplicity
or gap hypothesis is used. These facts supply the operator hypotheses of
the projected trial-space energy estimate for the final extraction in
ALVV, arXiv:1602.08828v2, lines 1814–1817. They do not choose the final
candidate space or prove the final approximation theorem.
