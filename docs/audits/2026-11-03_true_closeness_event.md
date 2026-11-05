# The true closeness event in projection coordinates

The actual predicate `Submodule.IsCloseTo delta U T` is exactly the
positive-semidefinite inequality on the orthogonal projection matrices
`P = P_U` and `Q = P_T`: `Q * P * Q - (1 - delta) • Q` is positive
semidefinite. This is the original definition in ALVV,
arXiv:1602.08828v2, Definition `d:close`, lines 469–474.

The new result `Submodule.isClosed_setOf_isCloseTo_projectionRange`
proves that, on the space of actual orthogonal projection matrices,
the set of candidates whose actual range is `delta`-close to the fixed
target is closed. Thus both true success and true failure are Borel
measurable. No substitute hull or independent success predicate is used,
and no desired measurability property is assumed. The real error
parameter is unrestricted; zero-rank candidates and zero targets are
included. Measurability of an actual random output projector remains a
separate input before taking the inverse image of this fixed Borel set.

The proof uses Mathlib's existing closed positive-semidefinite cone;
no generic positivity theorem is duplicated. The standard star-algebra
matrix representation gives the exact equivalence with the library's
operator inequality. Mathlib identifies each candidate orthogonal
projection with the orthogonal projection onto its actual range.
