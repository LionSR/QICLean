# Physical replica energy and exact excitation components

The source is OpenAI, *A two-dimensional area law from a global spectral gap*
(September 24, 2026), `07-comparators.tex`, lines 130–147 and 421–456, at
`openai/math` revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

`ReplicaDefect.lean` constructs the sum of the physical Hamiltonians and the
sum of the actual ground-complement operators on the replica space. The
one-copy positive semidefinite gap inequality implies the replica inequality
by tensoring with identities and summing. This operator conclusion does not
require a normalized ground vector or a ground-eigenvector equation. A unit
ground vector makes the defect count positive semidefinite. For a unit vector
on the replicas and any finite auxiliary space, positive gap, copy count and
threshold give the actual spectral cutoff mass from the mean excess energy.
The cutoff is the spectral function of the actual physical defect count,
tensored with the identity on the auxiliary space.

The same module proves that the literal product of one-copy eigenvectors has
the summed eigenvalue. For a positive number of copies, tensoring with any
auxiliary vector gives the one-copy eigenvalue for the physical mean
Hamiltonian. Neither eigenvector conclusion assumes normalization or a
supplied product-eigenvector identity.

`ReplicaExcitationDecomposition.lean` defines the sector projection by putting
the actual ground complement on the selected copies and the actual ground
projection on all other copies. These operators partition the identity; for
a unit ground vector they are orthogonal projections. The defect count acts
on each sector by the cardinality of the excited subset. Finite spectral
calculus then identifies its literal spectral cutoff with the sum of the
retained sectors. Every vector in that actual cutoff range decomposes into
the retained physical sectors, with the whole auxiliary space preserved.
The sum of the squared component norms is the original squared norm; a unit
vector gives the unit total mass stated in the manuscript.

These statements prove the physical gap, cutoff mass and orthogonal component
steps. They do not assert the complete lower comparison in Section 7. The
compatibility with simultaneous copy permutations, the component invariance
under good-copy and bad-copy stabilizers, the factorization of ground physical
copies, the preservation of specified Schur labels and the metric comparison
estimates remain subsequent steps. No hypothesis asserting any of those
conclusions is used in the present proofs. The two mathematical blueprint
fragments state exactly the assumptions and conclusions of this contribution.

All new proofs were independently written from the manuscript. No upstream
Lean proof text was reused. Codex assisted the formalization.
