# Nested targets under a weaker orthogonality hypothesis

- `Analysis/ViableSubspaceErrorReduction.lean`: for nested targets
  T contained in Tplus, the sufficient hypothesis is that the filter sends
  Tplus's orthogonal complement into T's orthogonal complement. The
  stronger invariance of Tplus's complement implies this condition, since
  T is contained in Tplus. The proof uses precisely the resulting
  orthogonality to T. The error conclusion is unchanged. This
  is a generalization of the sufficient hypothesis, not an assumed spectral
  gap or a stronger invariant-subspace assertion.
- `Analysis/ViableSubspaceSpectralProjector.lean`: the corresponding nested
  tensor consequence uses that weaker sufficient orthogonality condition.
  The spectral-cutoff application explicitly derives the orthogonality
  required by the generalized theorem.
- `Analysis/ChebyshevWordPower.lean`: the extended theorem returns the
  actual filter, its complementary tensor factors, low-space invariance,
  minimum gain and high-space contraction before every input space. The
  ordered-word conclusion is a corollary with the same mathematical
  hypotheses.

These results carry the hypotheses stated in their signatures. They do not
assert the complete physical algorithm, its printed running time, or the
physical regional-energy estimates.
