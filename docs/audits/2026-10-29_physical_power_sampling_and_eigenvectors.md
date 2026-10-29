# Physical power sampling and Euclidean spectral coordinates

The normalized nearest-neighbour power sampler is constructed from the actual
positive-contraction interactions and a specified gapped ground energy. It returns
one sample with both operator-norm approximations and simultaneous letter counts.
No successful sample, mean identity or concentration estimate is assumed.

Let n be the number of original interactions plus one, and let the ground energy
be E0. The normalization C = (1-E0/n)^(-1), word length
m = ceil((n-E0) log(Q)/Delta), and explicit positive sample count retain the factor
exp(2 E0 log(Q)/Delta). The energy bounds 0 <= E0 <= n-1 follow from the unit
ground vector and the original positive-contraction bounds. The proved count is
not polynomial with a degree independent of the ground energy. The published
supplement to LVV Proposition 1 is distinguished from the earlier arXiv version.

The source commit was integrated as 5ff133a695f8f7e9255a33a1d276722897dd28d9.
Its ordinary full library build completed 10,347 jobs. Strict checks of the
changed sources, an imported foundation audit of five public declarations,
blueprint source synchronization and compiled declaration checks all passed.
Only propext, Classical.choice and Quot.sound occur in those foundation audits.
The build compiled no Mathlib source.

The subsequent checked mathematical snapshot is
637184a66a8c2215adec3bd28fc1a872ca382836. It adds the Mathlib-only theorem
Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis, the continuous Euclidean form
of Mathlib's Hermitian eigenvector equation. The statement applies to any RCLike
field and finite matrix index, with no nonempty-index or spectral-gap hypothesis.
It replaces the repeated coordinate calculation used in seven TNLean proofs.

At that snapshot, the ordinary full library build completed 10,348 jobs.
Strict source checks, the imported foundation audit of the new theorem,
blueprint source synchronization and compiled declaration checks all passed.
The foundation audit again used only the three standard axioms. No Mathlib
source was rebuilt. Dependency inputs and the Lean toolchain are unchanged.

Verification records are /tmp/qiclean-physical-sampling-gates.json and
/tmp/qiclean-euclidean-eigenvector-gates.json in the local working session.
Both checks used the previously seeded common worktree and the prebuilt Mathlib
cache. Normal builds and cache operations were serialized through TNLean's
repository lock. The small helper contribution had no .lake directory and was
checked with read-only existing objects and private outputs; no cache was copied
from a modified worktree. The completed source checks do not establish the
TNLean spatial-rank or viable-set applications, which are verified separately
in the consuming library.
