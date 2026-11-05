# Buffered spectral comparison from a global norm estimate

The new matrix theorem derives both directed low-energy comparisons from an
actual global norm error. It uses the existing finite-window perturbation
theorem and the canonical Hermitian eigenbasis, rather than imposing a gap,
an eigenvalue count, a supplied subspace comparison, or a unique ground
state. The explicit common lower endpoint uses `U = norm H + xi`, so its
loss is independent of the approximating matrix. Eigenvalue norm bounds
supply the required lower spectral bound. The empty matrix index is allowed.

This is an auxiliary for ALVV, arXiv:1602.08828v2, the spectral-window proof
at lines 955–968 and the approximating Hamiltonian at lines 1412–1420. It is
not the physical hard-truncation theorem or the efficient-filter theorem.
The corrected finite window count remains explicit; see the existing
`docs/paper-gaps/alvv16_hard_truncation_windows.tex`.
