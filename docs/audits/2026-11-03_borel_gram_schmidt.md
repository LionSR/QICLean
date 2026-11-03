# Borel Gram–Schmidt transformations

The new Mathlib-only `GramSchmidtMeasurable` module proves that the existing
Gram–Schmidt transformation and its normalized version are Borel maps on
all finite families in a separable real or complex inner product space.
There is no independence, nonvanishing or finite-dimensional-space premise.
Empty families and dependent families are included. When a Gram–Schmidt
vector is zero, the existing normalized definition keeps it zero.

The proof uses the actual Mathlib recurrence and the existing singleton
orthogonal-projection formula. An induction over the finite ordered indices
reduces measurability to finite sums, scalar products, norms, real-to-scalar
coercion, division and scalar multiplication. Reciprocation is measurable
with its existing value zero at zero. No orthonormality or span proof is
repeated, and no arbitrary basis selector is asserted measurable.

Mathlib scouting found the recurrence, normalization and measurable scalar
operations but no existing measurability theorem for these transformations.
The new result supports the eventual construction of Borel varying frames
in ALVV, arXiv:1602.08828v2, l:rs, lines 530–558; it does not construct that
frame, a complete collective-trim map, or a joint adaptive sampling law.

## Verification

The source-only worktree is based on frozen QIC
fd3a102b883f494ad70bf787bc51436cb197aab0. Private strict checking used the
immutable TN e2706cbe715c49745d4399d37dabe3d2559cc494 and its own QIC
de8a9d1286709f39d8c37d4d52d6e336925863e5. The new module imports only
Mathlib and passed in 4.017 seconds. Its two-declaration imported foundation
inspection passed in 3.899 seconds and reported only propext,
Classical.choice and Quot.sound. The temporary inspection source was removed.
The source blueprint, generated imports, reader-facing prose and whitespace
checks pass. No provider source, compiled object, dependency cache or Mathlib
source was changed. Ordinary compiled-library and blueprint gates remain
separate integration checks.
