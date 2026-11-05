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

The new result supports the eventual construction of Borel varying frames
in ALVV, arXiv:1602.08828v2, l:rs, lines 530–558; it does not construct that
frame, a complete collective-trim map, or a joint adaptive sampling law.
