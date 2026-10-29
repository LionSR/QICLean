# Scalar soft truncation and exponential remainder bounds

The scalar definition and its basic bounds recover QICLean draft 981 at
`9ec7bc71cf701615b332cdb4e58c8587d6167b49`. The derivative calculation now
uses the explicit simplification lemmas accepted by the strict linter.
No theorem statement from that draft was weakened. Its permanent test
fixtures are not carried over.

The corrected upper bound is t(1+log m). The printed t log m bound is
false already at m=1. The corresponding paper-gap note remains a local
correction; the polynomial remainder and order bounds are preserved.

Two additional scalar estimates are proved. The geometric remainder is
x-h_(m,t)(x) <= x(1-exp(-x/t))^m. When scale and order agree, for m>=1,
x>=0 and 0<theta<=1/2, the exponential estimate is

    x-h_(m,m)(x) <= (2/theta) exp(theta*x-theta*m/2).

The proof separates x<=m from x>=m and uses only elementary exponential
bounds and the geometric remainder. It does not infer higher moments of a
regional Hamiltonian from its mean energy. Applying it to a physical
spectral measure requires a separately established exponential moment.
The physical spectral comparison and efficient cluster approximation
remain open.

The exact module passed strict private checking and an imported audit of
its four public declarations. The audit uses only propext, Classical.choice
and Quot.sound. Direct imported Mathlib source and object hashes were
unchanged before and after the final check; no Mathlib source was compiled.
The private record is `/tmp/tnlean-soft-truncation-20261029/manifest.json`.
Ordinary combined-library and blueprint checks remain pending at this
source preparation stage.

## Ordinary verification

At mathematical revision `1aa1011b4f5518d59de4ef462b71d84ad4ec33ea`, the full 10,350-job library build,
strict checks of all four changed production files, and an imported audit of
all six public declarations in the two new modules passed. The audit uses
only propext, Classical.choice and Quot.sound. Source synchronization,
compiled blueprint declaration checks, added-prose and compilation-time
checks also passed. No job reached the 25-second warning threshold, and no
Mathlib source was compiled. Existing prebuilt artifacts were used under
the repository lock. No permanent Lean test fixture was added.

The complete local record is
`/tmp/qiclean-filter-normalization-soft-gates.json`, with the separate
added-prose log `/tmp/qiclean-filter-normalization-soft-prose.log`.
This completion record changes documentation only.
