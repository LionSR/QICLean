# Viability reduction between two spectral cutoffs

The low-energy construction in ALVV, arXiv:1602.08828v2, Theorem 4.8
(`t:aisgapless`, source lines 1027–1041), uses two nested target spaces.
It requires expansion on the smaller space and contraction outside the
larger space. No spectral gap or contraction estimate is required in the
intermediate band.

This contribution extracts four completed auxiliary results from local
QICLean revision `e51354163d2dd9cf2a15d65722c544c6b4736182`:

- closeness improves under an operator preserving the smaller target
  and the orthogonal complement of the larger target;
- a finite tensor decomposition transfers this estimate to viability;
- a spectral filter supplies the two norm estimates at distinct cutoffs;
- the resulting family improves viability from the upper spectral
  space to the lower spectral space, with error
  \(\Delta/(1-\delta)^2\) and dimension at most the number of tensor
  factors times the initial dimension.

The existing results with one target or a spectral gap are special cases
of the generalized arguments. Their statements are retained. The existing
finite-image dimension lemma is reused in both tensor arguments.

The operator and tensor decomposition are hypotheses of these auxiliary
results. Their physical construction is a separate theorem in TNLean's
low-energy interval contribution. These estimates do not by themselves
prove the complete low-density area law. The previously documented closed
cutoff and absolute-value filter conventions are retained.

The four new statements and their proofs have mathematical blueprint
entries. Compilation and compiled declaration checks are pending.
