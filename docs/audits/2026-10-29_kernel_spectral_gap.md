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

## Ordinary verification

At mathematical revision `d41577c2965094ee0f1067fce107aa59088d653e`, the full 10,353-job library build,
strict checks of all five changed production files, and the imported audit
of all eleven public declarations in the four changed mathematical modules
passed. The only foundations used are propext, Classical.choice and
Quot.sound. Source synchronization, compiled blueprint declaration checks,
added-prose and compilation-time checks also passed. No job reached the
25-second warning threshold, and no Mathlib source was compiled. Existing
prebuilt artifacts and the repository lock were used; no permanent Lean
fixture was added.

The complete local record is `/tmp/qiclean-soft-hard-kernel-gates.json`,
with the additional prose log `/tmp/qiclean-soft-hard-kernel-prose.log`.
This completion record changes documentation only. The physical soft
spectral/subspace comparison remains separate.
