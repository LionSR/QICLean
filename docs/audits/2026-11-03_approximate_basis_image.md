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
error bounds must be derived by physical callers. The errors are full vector distances, retaining their complex phases;
absolute overlaps alone are not substituted for them. No Hamiltonian, filter,
MPS, reference family or sampling claim is assumed or constructed here.
They support the mathematical basis consequence in ALVV,
arXiv:1602.08828v2, line 288 and Theorem `thm:al-ld`, lines 1096–1105;
they are not a formalization of the probabilistic algorithm `t:alg2`.

The generic algebra belongs in the companion library and imports no TNLean
source. Existing Mathlib basis constructions, finite Cauchy–Schwarz,
Parseval, orthogonal projection minimality and the companion closeness
symmetry theorem are reused; no parallel basis or closeness predicate is
introduced.

Actual-name strict checks use the immutable TN provider
`20cad76ebfa6e770263c4a5d5333917c5b226ed9` and its own exact QIC package
`98ba564e3c9603dc93d2173e3dc87a85ce750456`. Only the two selected existing
QIC sources and objects are read, with guarded hashes and build inputs.
The new source writes its checked objects only under `/tmp`. The module
passes with default options in 4.541 seconds. The two public declarations pass imported foundation inspection with only
`propext`, `Classical.choice` and `Quot.sound`; the joint six-name inspection
takes 19.720 seconds. Temporary inspection commands are deleted.
Ordinary companion integration and compiled blueprint declarations remain
separate gates. No dependency pin, provider or cache is changed.
