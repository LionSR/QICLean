# Quadratic-form gap above the full kernel

For a Hermitian complex matrix A, a lower bound gamma for every nonzero
real eigenvalue gives gamma times the squared norm as a lower bound for
the quadratic form on the orthogonal complement of ker A. The statement
uses Mathlib's actual real spectrum and applies in every finite dimension.
The real bound may have either sign; positivity is required only by the
later detectability contraction.

The proof uses the existing Hermitian eigenbasis action and quadratic-form
identity. Kernel orthogonality makes the coefficients at zero eigenvalues
vanish, and the remaining coefficients satisfy the supplied spectral bound.
Mathlib's norm identity supplies Parseval's equality.

The physical consumer constructs the even/odd product from the original
supported projection terms and uses its proved kernel invariance and energy
estimate. Its contraction is homogeneous, with squared factor 4/(4+gamma),
for arbitrary ground-space dimension. The reduction from positive local
contractions to range projections and the regional truncated Hamiltonian
remain separate.

Both exact private modules passed strict checking and an imported audit
of their two public declarations. Only propext, Classical.choice and
Quot.sound occur. The local manifest is
`/tmp/tnlean-kernel-detectability-20261029/manifest.json`.
Ordinary combined-library and blueprint checks remain pending at this
source preparation stage.
