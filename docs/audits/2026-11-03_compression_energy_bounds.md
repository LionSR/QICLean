# Scalar lower bounds and actual compressed eigenvalues

The new module `QICLean/Analysis/CompressionEnergyBounds.lean` contains
three finite-dimensional variational statements used by native regional
energy estimation.

* A positive scalar shift B-aI and a normalized eigenvector with real
  eigenvalue b imply a<=b.
* Suppose A has an actual unit eigenvector at e, K is Hermitian on a
  nonzero finite space, K-eI is positive and A-min(K)I is positive.
  Then e=min(K). The two matrices may act on different finite spaces.
* If K-eI is positive, every actual ordered eigenvalue of the orthogonal
  compression of K to any subspace S is at least e. Invariance of S
  under K is not assumed. Empty S has no indexed eigenvalue, as required.

The first assertion evaluates the positive shifted quadratic form on
the given eigenvector. The second applies it to the actual minimum
vector of K and the supplied attained eigenvector of A. The third
evaluates the original positive form on the actual unit eigenvectors
of the compression, using agreement of its quadratic form with that
of K. No compressed eigenvalue or successful low-energy vector is
supplied as an extra assumption.

These are explicitly stated auxiliaries supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631-1632 and the
correctness argument at lines 1793-1807. They make no assertion about
constructing physical candidates or about an energy-estimation algorithm.
They were separated from the physical TNLean proof so that the generic
matrix statements remain in QICLean.

## Verification

The exact source passed a private actual-name strict check in 4.954
seconds against TNLean 478e8a08f8d97cec4064070a29170a0953362d3e and
its immutable QICLean dependency 9578336a5123a76001a1218e271132091c828de2.
An imported audit of all three public statements passed in 4.088
seconds, with only propext, Classical.choice and Quot.sound.
Selected source and object files, build inputs and the prebuilt Mathlib
object were guarded. New objects were written only under /tmp; no
provider or shared cache was changed and no Mathlib source was built.
Ordinary combined and compiled-book verification remain integration checks.
