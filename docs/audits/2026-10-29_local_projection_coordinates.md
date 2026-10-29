# Local range coordinates for retained projections

A projection supported on a physical region is first written as the lift of an
actual local projection. An orthonormal basis is then chosen for the local
range, after removing the identity on the exterior. For two disjoint child
regions and a fixed parent range frame, the parent coefficient matrix is the
adjoint of the tensor product of the child frames, multiplied by the parent
frame. This matrix is an isometry whenever the lifted parent range is contained
in the product of the lifted child ranges.

These are auxiliary coordinate results for Hastings,
*Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3, Section III,
lines 630–685 of `proj3new.tex`. They do not themselves construct the physical
spectral hierarchy or prove its amplitude contraction. The source explicitly
leaves quantitative bounds on intermediate retained dimensions open at
lines 104–109. No polynomial intermediate bond bound is asserted here.

## Statements and hypotheses

`SupportedProjectionCoordinates` constructs a local orthogonal projection and
an actual rectangular range isometry. The retained dimension equals the rank
of the local projection and is at most the number of local configurations.
A global configuration is explicit data: it makes the local lift injective by
fixing the exterior configuration. Empty physical regions and zero retained
ranges are allowed.

`LocalProjectionTensorCoordinates` uses fixed range frames. Its unary result
descends a containment identity between lifted range operators. Its binary
result derives that identity from the actual tensor product of the child
columns and constructs the coefficient matrix. It proves the matrix
factorization, isometry, product dimension bound, and the expansion of each
parent column on every physical configuration. No successful decomposition or
coefficient array is supplied as a hypothesis.

## Ownership and verification

The declaration `Entropy.localLift_injective` has moved from `FilterPower` to
`LocalLift`. Its name, signature and proof are unchanged. The complete moved
text has SHA256
`aab0607659d472ba531d2a24a5a34f87e91ddf20aae634d1ac19af1d66970099`.
There is exactly one definition. The private checks override both `LocalLift`
and the rebuilt `FilterPower`, so the former owner cannot reintroduce an old
copy of the declaration.

The source-only worktree is based on checked QICLean commit
`e51354163d2dd9cf2a15d65722c544c6b4736182`. Strict actual-module checks passed
for the modified `LocalLift` and `FilterPower` and both new modules. The new
modules took 30.114 and 6.481 seconds, respectively. The relocation checks took
52.730 and 38.460 seconds during external build contention; ordinary compilation
timings remain to be checked by the canonical integration gates.

A separate imported audit of the moved declaration and all five new public
theorems passed. Every declaration depends only on `propext`,
`Classical.choice` and `Quot.sound`. The temporary audit is outside the
repository; no permanent theorem fixture is added.

Every private check guarded the exact provider revision, selected production
source and object hashes, build inputs and the prebuilt Mathlib root object.
Only temporary objects were written. No provider, package cache or Mathlib
source was changed or rebuilt. The updated mathematical section was compiled
twice as a two-page excerpt and both pages were visually inspected.

The ordinary full build, generated-import check, compiled declaration check and
complete book checks belong to the next coordinated integration. The physical
hierarchy contraction remains separate work.
