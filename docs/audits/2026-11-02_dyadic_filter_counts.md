# Scalar ceiling and dyadic count estimates

This source-only contribution is based on accepted QICLean revision
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`. It adds only the two scalar
modules `PolynomialFilterCeil` and `PolynomialFilterCounts`, with the
same public statements and proof texts as preserved revision
`c15787d256b42289c5037252ab1381b23b1919ca`.

For A≥100 and a fixed natural m with log m≥100, put

    u_g = 1 + log m + log(1/g),
    ell_g = ceil(A*u_g²/g),
    D_g = (m*ell_g²)^(22*ell_g).

If 0<g,h≤1 and g≤2h, the actual natural ceilings satisfy
ell_h≤(21/10)ell_g, and the actual counts satisfy

    100 ≤ log D_g,       log D_h ≤ (13/6)log D_g.

Integer rounding is included. The scalar modules import only Mathlib
and each other. They assume no physical filter, count estimate or
suppression bound, and prove no low-density dimension or sampling theorem.
The source context is ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. The explicit finite thresholds
belong to these supporting numerical statements.

The shared two-sided ceiling proof is unchanged from the private estimate
still present in TNLean revision
`5fc343a57d70eefd2902780107851ab9b0753a82`,
`MPS/AreaLaw/PolynomialFilterParameters.lean:85`. Its sole call is at 268.
After this companion contribution is accepted and pinned, the minimal TNLean
follow-up imports `PolynomialFilterCeil`, removes the private copy and
replaces that one call by the shared theorem. No public TNLean statement
or other dependency needs to change. That follow-up is separate from this
companion source contribution.

The reader-facing numerical statements are appended to the existing
bootstrapping chapter. No ancestor integration batch, physical low-energy
module, test fixture or parallel definition of the count is introduced.

## Verification

Fresh strict checks target accepted source revision
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`, using only selected immutable
compiled dependencies from the warmed QICLean revision
`24a2ee589c5ff8da34a5cc6d8b7026dc7700e929`. The toolchain, Lake configuration
and manifest are byte-identical. PolynomialFilterCeil has no QICLean
imports; PolynomialFilterCounts imports only the newly compiled ceiling
module through an explicit private override. The remaining imports are
Mathlib. No existing importer is left above a changed dependency.

- PolynomialFilterCeil passed strict checking in 30.451 seconds.
- PolynomialFilterCounts passed strict checking in 23.834 seconds.
- A combined imported inspection of these three public declarations and
  the four independent canonical-window declarations passed in 25.410 seconds.
  Every declaration depends exactly on `propext`, `Classical.choice` and
  `Quot.sound`.

The ceiling measurement exceeds the 25-second review threshold and remains
below the unchanged 50-second limit. It is retained without a timing-only
retry or a raised limit. Ordinary integration timings remain pending.
The source hashes are unchanged from the preserved proofs:
PolynomialFilterCeil has SHA256
`ef90958c6e87b6dfecd6cf9f254f5c8b661f7241e1bd594a28530158ad1b0870`, and
PolynomialFilterCounts has SHA256
`7fac4305b2f68807d1e3c1c549853dce87793c2de782ceb8fcf20313092dd4af`.
Evidence is below `/tmp/qiclean-alvv-dyadic-counts-ba017-20261102`
and `/tmp/qiclean-alvv-ba017-public-inspection-20261102`.
The temporary diagnostic source was deleted after the imported inspection;
no permanent fixture is included.

The check runner guards every selected source/object and build-input hash
before and after each invocation. No provider source, provider artifact or
cache was changed. No ordinary build or Mathlib source compilation was
started, and the source worktree has no Lake directory. Ordinary full-library
and compiled blueprint verification remain coordinated integration gates.
