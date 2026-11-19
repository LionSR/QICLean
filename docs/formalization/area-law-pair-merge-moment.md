# Merge moments on paired copy spaces

Let Q and C be finite-dimensional spaces with specified finite orthonormal
bases. On Q to the tensor power m tensored with C to the tensor power m,
consider the separate copy-permutation actions and their simultaneous
product. Their central Schur projectors give three labels λ, μ and ν.
For any positive matrix invariant under both separate actions, the joint
label moment of (d_λ d_μ / d_ν)^b is bounded by
(m + 1)^((dim Q · dim C)^2) times the actual trace, for every b ≤ 1.
The trace-one case has no mass factor.

This is the paired-coordinate form of the merge-moment estimate in
OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 6, equation (replicas:merge-moment),
05-replicas.tex, lines 112–115. Its homogeneous form retains the component
mass that occurs in the application in 07-comparators.tex, lines 520–549,
equation (comparator:merge-moments). The source is pinned at
adc7f1241b42e322a6451854ab7e4b4c146bf78a.

The coordinate bijection groups the two factors of each copy into the two
literal copy strings. It preserves the density, trace and all three
projectors. The joint moment therefore equals the moment in the existing
finite-family theorem. The one-copy dimension is exactly dim Q · dim C;
no new multiplicity estimate is assumed.

For an unnormalized matrix, total trace normalization produces a trace-one
positive matrix. If the trace vanishes on a nonempty basis, the matrix is
zero and the total normalization is the maximally mixed state, which
commutes with every action. Multiplication by the original trace recovers
the matrix. An empty basis also gives the zero matrix. Thus the homogeneous
bound includes zero mass and empty spaces without a positive-mass premise.
Zero copies are included as well.

The positive component, its separate permutation invariance and the
identification of this label moment with an exponential deficit must still
be derived in the physical application. The present statement supplies the
auxiliary moment estimate; it assumes no compatibility, multiplicity or
moment certificate.
