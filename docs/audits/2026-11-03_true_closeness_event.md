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

## Verification

Private checks used the immutable TNLean provider
`e2706cbe715c49745d4399d37dabe3d2559cc494` and its own QICLean package
`de8a9d1286709f39d8c37d4d52d6e336925863e5`. There is one selected QIC
source/object dependency, the unchanged original closeness module.
Strict actual-name checking passed in 4.919 seconds with default
options. The three-name imported foundation inspection passed in
4.133 seconds; each theorem uses only `propext`, `Classical.choice`,
and `Quot.sound`. The same temporary inspection also checked both
success and failure measurability with the standard complex Borel
structure; that source was deleted afterward.

No ordinary build, shared artifact copy, cache mutation or Mathlib
source compilation was performed. Reader registration, source
synchronization, generated imports, prose, pattern, integrity and
whitespace checks are recorded externally. The mathematical reader
was rendered and visually inspected. Canonical ordinary compilation
and compiled blueprint checks remain for integration.
