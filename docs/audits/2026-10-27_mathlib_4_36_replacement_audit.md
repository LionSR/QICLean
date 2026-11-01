# Mathlib 4.36 release-candidate replacement audit

Date: 2026-10-27. This is a draft upgrade audit, not a completed-build report.

## Exact comparison and inputs

- Old Lean and Mathlib: `v4.35.0-rc3`; Mathlib commit
  `c55e6e786f49471c72fbddbec5415808896aec1e`.
- New Lean: `leanprover/lean4:v4.36.0-rc1`, compiler commit
  `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`.
- New Mathlib: `v4.36.0-rc1`, commit
  `625d8914199bc567cca9b91f90e8e5afafa5ae51`.
- Matching doc-gen4: `v4.36.0-rc1`, commit
  `0656b7ebd305f089c8d6bd8684a0797f19414cc2`.
- QICLean base: `a312be61cb523872c33b0c583554b7af670cface`.
- Gametheory remains `ec93e4daed4ad8b4784a9d760e492832e7711433`;
  checkdecls remains `3d425859e73fcfbef85b9638c2a91708ef4a22d4`.

The upstream release lists and tag objects identify this as the latest
published release candidate on the audit date. It is not Mathlib `master`.
The source search examined the 529 non-merge commit titles in the comparison
range, the relevant new declarations, and the required algebraic-structure
areas below. Absence findings are limited to these searches.

## Replacements included

### Geometric power bounds

Mathlib's new `norm_pow_le_mul_pow_of_gelfandRadius_lt` in
`Mathlib/Analysis/Normed/Algebra/GelfandRadius.lean`, together with
`spectrum.spectralRadius_eq_gelfandRadius` in `GelfandFormula.lean`, replaces
the eventual estimate and finite-prefix sum in
`geometric_bound_of_spectralRadius_lt`.

Upstream commit: `56307dd73d687e33014af41b4234b3ff6cd13591` (#42607).
The conclusion still supplies one positive real constant bounding every
natural power, including zero. The conversion from extended nonnegative
reals uses `ENNReal.ofReal_lt_coe_iff` and `gelfandRadius_nonneg`.
No nontriviality, norm-one, or additional spectral hypothesis is added.

### Full row rank and surjectivity

The new `Matrix.mulVec_surjective_iff_rank_eq_card` in
`Mathlib/LinearAlgebra/Matrix/Rank.lean` (#43956) replaces:

- the manual injectivity and equal-finrank comparison in
  `Matrix.IsIsometry.isUnitaryBetween_of_card_eq`, using its existing
  `IsIsometry.rank_eq_card` theorem and cardinality equality;
- the manual range-dimension argument in
  `stinespringW_mulVec_surjective_of_minimal`, using the rank equality already
  obtained from the Choi Gram identity.

Both changes retain empty finite index types. All three public theorem
headers are unchanged, and no definition, local type, compatibility alias,
or new proof automation is introduced. The production diff removes 53 lines
net. `QICLeanTest/Mathlib436Replacement.lean` supplies standard-axiom guards,
empty coordinates, zero-dimensional ancilla, zeroth powers and a subsingleton
algebra application; these checks still require target-version compilation.

## Other candidates and downstream ownership

The new `LinearIndependent.mulVec_surjective` removes the explicit inverse
construction in TNLean's private `range_mul_transpose_of_injective` in
`PEPS/ParentHamiltonian/InjectiveRegionSupport.lean`. That change belongs in
the later TNLean upgrade, not this repository.

`Matrix.submatrix_equiv_mem_unitary` (#44336) covers the existing reindexing
statement in `Algebra/MatrixReindexUnitary.lean` and a private TNLean proof in
`MPS/MPU/Examples/ShiftStrictEquivalence.lean`. The public QICLean wrapper has
live TNLean consumers; this patch does not delete it or introduce a breaking
cross-repository rename. Its existing proof is already a short application
of the library's rectangular-unitary result.

## Required structural coverage recheck

This records the areas required by TNLean's `docs/project_conventions.md` and
[tracker #8315](https://github.com/LionSR/TNLean/issues/8315).

| Area | Finding at the exact new Mathlib pin |
| --- | --- |
| Multiplicative third cohomology | `LowDegree.lean` still supplies the degree-one and degree-two multiplicative interfaces, not `IsMulCocycle₃` or `H3π`. General degree-three cochains remain available. |
| Group-cohomology universes | The shared `{k G : Type u}` restriction remains in `Basic.lean` and `LowDegree.lean`. |
| Projective representations, twisted group algebras, circle versus complex-unit coefficients | No newly matching implementation was identified in the inspected range. |
| Weak/pre-bialgebras and C*-Hopf structures | New `HopfAlgebra.ofAntipodeOfAdjoin` (#41828) assumes an ordinary unital, counital bialgebra. It does not replace the MPO coproduct with projector-valued unit image or missing counit. The `ofSurjective` relocation (#41052) does not supply that structure. |
| Rigid, pivotal, spherical, fusion and module categories; Frobenius–Perron dimensions | Existing rigid and monoidal-action foundations remain available; no newly matching pivotal, spherical, fusion or Frobenius–Perron implementation was identified. |
| Based/fusion rings and NIM representations | No newly matching implementation was identified. |
| Star-closed matrix-algebra semisimplicity | No exact replacement for TNLean's star-subalgebra theorem was identified. Inner-product semisimplicity for an individual operator is a different statement. |

These findings do not discharge previous migrations. Tracker
[#8317](https://github.com/LionSR/TNLean/issues/8317) was closed after the
predicate and arbitrary-cochain quotient changes in
[#10233](https://github.com/LionSR/TNLean/pull/10233) and
[#10235](https://github.com/LionSR/TNLean/pull/10235) merged. Its closure does
not establish completion of all requested deletions: the cohomology-relation
migration in [#10238](https://github.com/LionSR/TNLean/pull/10238) and the raw
cochain/helper namespace migration remain outstanding. The other deferred
parts of #8315 likewise require their own resolution. The coordinated TNLean
draft must distinguish preparation from satisfaction of these migration
requirements; this QICLean change does not discharge them.

## Protocol and remaining validation

The ordinary QICLean `update.yml` workflow was not dispatched. It has no
target input, and `mathlib-update-action@v1` defaults to every newer release
and `master`, exceeding the requested latest-RC-only change. This manually
prepared draft follows the QICLean-first dependency order while limiting
the version target. It does not claim the workflow ran.

The dependency manifests were generated by the target Lake version. The
root and documentation toolchains and shared dependency revisions agree;
the unrelated direct pins listed above are unchanged. Production theorem
headers remain identical, and source review found no additional hypotheses.
These checks do not establish target-version compilation. Package builds,
strict Lean checks, axiom guards, complete regressions, executable text lint,
blueprint declaration checks and web/PDF builds remain unverified.

Before this draft is ready, the exact-head hosted checks and the upgrade
runbook's full build, strict tests and blueprint checks must succeed, with
any migration errors repaired without weakening tests or hypotheses.
The existing generic blueprint filter now includes toolchain and dependency
inputs, so an upgrade requests compiled declaration checks and full renders
rather than silently taking the Lean-only fast path. No per-module CI step
or test exemption is added.
Only after authorized review, merge and publication of a matching immutable
QICLean semantic-version tag and release archive may TNLean consume this
upgrade in one lockstep PR. No such tag, archive or TNLean bump is asserted
to exist. The observed TNLean bare-SHA pin and older QICLean `v0.2.1`
semantic release are pre-existing departures from the runbook's release
pinning convention, not evidence that this release step can be skipped.
