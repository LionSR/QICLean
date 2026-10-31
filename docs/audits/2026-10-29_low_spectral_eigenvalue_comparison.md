# Ordered eigenvalues from an actual low-energy residual

The bounded extension in `QICLean/Analysis/WeylMonotonicity.lean` proves
`Matrix.IsHermitian.eigenvalues₀_le_add_of_norm_domRestrict_low_le`.
For actual Hermitian matrices H and F, let G be the span of the canonical
eigenvectors of F with eigenvalues at most c. The input is the operator norm
of the actual restriction `(H - F)|G`, bounded by ξ. If the ith decreasing
eigenvalue of F is at most c, the corresponding eigenvalue of H is at most
that eigenvalue plus ξ.

No basis, coordinate identification, spectral gap, order comparison, physical
truncation formula, or residual for a different operator is supplied. The
canonical basis comes from the existing finite spectral theorem. Repeated
eigenvalues, arbitrary cutoffs, arbitrary real ξ satisfying the norm bound,
and zero-dimensional spaces are allowed. In zero dimension there is no index
to which the conclusion applies. Existing Weyl monotonicity separately gives
the lower comparison when F ≤ H.

The proof reuses the existing private intersection argument in the same
module: the upper i+1 eigenvectors of H and lower d-i eigenvectors of F have
a common nonzero vector. Antitonicity puts the latter span inside G. The
existing quadratic spectral expansion and Cauchy--Schwarz compare the two
energies on that vector, and its positive squared norm can be cancelled.
The new imports have no cycle through the low-energy subspace module.

This is finite-dimensional auxiliary mathematics for the perturbation step
in ALVV, arXiv:1602.08828v2, `lem:hard-trunc`, source lines 955–968. It does
not claim that any particular clipped Hamiltonian satisfies the residual,
or repair any source cutoff convention by adding an unstated hypothesis.
Physical instances and cutoff corrections remain downstream obligations.

The isolated source base is accepted QICLean main
`86b3159b98a1608c5e66a875fa670a9687c9867d`. Mathlib is pinned to
`c55e6e786f49471c72fbddbec5415808896aec1e` with Lean v4.35.0-rc3.
No Lean, Lake, build, elaboration, or compiled declaration check was run.
The new blueprint statement and proof remain `notready` pending hosted
verification and review.

Root and independent peer review passed the complete mathematical statement,
intersection proof, canonical-span inclusion, restriction/subtype coercions,
continuous/ordinary linear-map transport, and final positive-norm cancellation.
Native generated-import, full blueprint/source synchronization, unique ownership
of the new anchor, ChkTeX, source-size, source-width, integrity-token, and
whitespace checks pass. These source checks are not Lean elaboration or hosted
verification. The actual dependency versions remain those of the accepted base.
