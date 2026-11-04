# The actual image of an approximated orthonormal basis

The new module `Analysis/ApproximateBasisImage` constructs the linear map
that takes an actual target orthonormal basis to prescribed ambient vectors.
Finite Cauchy–Schwarz and Parseval give its squared error from inclusion,
controlled by the sum of the squared basis errors. This first estimate does
not require finite ambient dimension.

When that sum is below one, the map is injective. Its actual range is the
span of the prescribed vectors and has exactly the target dimension.
The best-approximation property of orthogonal projection gives forward
subspace closeness. The existing equal-dimensional symmetry theorem gives
reverse closeness with the same squared error. Zero-dimensional targets
and empty basis index sets are included.

These are conditional finite-dimensional lemmas. Their prescribed-vector
error bounds must be derived by physical callers. The errors are full vector
distances, retaining their complex phases;
absolute overlaps alone are not substituted for them. No Hamiltonian, filter,
MPS, reference family or sampling claim is assumed or constructed here.
They support the mathematical basis consequence in ALVV,
arXiv:1602.08828v2, line 288 and Theorem `thm:al-ld`, lines 1096–1105;
they are not a formalization of the probabilistic algorithm `t:alg2`.
