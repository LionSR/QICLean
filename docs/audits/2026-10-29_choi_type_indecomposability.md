# Full-range Choi-type indecomposability

This completes the mathematical acceptance criteria of QICLean issue #18 at
base `87cb104a853153751bc4932cf3c55427a1d99724`. The original implementation and audit commits are preserved locally.
Publication is a draft pull request; no issue-state mutation, readiness
transition, or merge is authorized.

## Mathematical boundary

The three public declarations are:

- `Matrix.choiTypeMapFin_not_isDecomposablePositiveMap`;
- `Matrix.choiTypeMap_not_isDecomposablePositiveMap`;
- `Matrix.choiTypeMap_isIndecomposable`.

Their only mathematical hypotheses are `3 ≤ d`, `1 ≤ n`, and `n ≤ d - 2`.
The index instance `[NeZero d]` is required by the existing map definition
and follows from `3 ≤ d`; an independent regression derives it internally.
There is no supplied positivity, witness, decomposition obstruction, or
atomicity premise.

Source: Wolf, Example 3.1, Equation (3.20),
`Notes/WolfNoteTexSource/ch03_positive_not_completely.tex:357–365`; cyclic
shift convention in Chapter 2, Equation (2.24); Ha, *Atomic Positive Linear
Maps in Matrix Algebras*, Theorem 2.1, pp. 593–595. The existing local source
audit `docs/paper-gaps/ha98_choi_type_witness_scope.tex` records Ha's one-based
to zero-based translation and the Eom–Kye orientation. Actual witness,
block-transpose, pairing, and positivity proof bodies were read.

The proof selects `γ = 1/2` internally and uses `ρ = A_γ^σ`, with
`ρ^{T₁} = (A_γ^{T₂})^σ`. Both matrices are PSD by their established
Schmidt-number-at-most-two decompositions. If the ampliation were PSD, its
normalized-Ω quadratic form multiplied by `d` would be nonnegative. The
established exact value is `γ² - 1 = -3/4`. The PPT preservation criterion
therefore excludes decomposability in the `Fin d` basis. Reindexing Kraus
operators preserves CP, and the entrywise reindexing commutes with transpose,
so a hypothetical decomposition in `ZMod d` would contradict this detector.
Full-range positivity is supplied by `Matrix.choiTypeMap_isPositiveMap`.
No stronger atomicity conclusion is claimed.

Only the existing `Indecomposable.lean` production module is edited. Its
three direct imports are the witness, full positivity, and PPT criterion
owners. Foundational witness modules are unchanged. No new public transport
infrastructure overlaps the active matrix-reindexing PR.

## Independent native-agent review

A separate native reviewer returned **PASS, no mathematical blockers**. It followed the actual root-average and
block-transpose proofs, the pairing calculation and factor `d`, positivity
assembly, detector, and CP/cocopositive transport. It read the synchronized
Blueprint statement, proof, and dependencies.

Reviewed and independently strictly elaborated production SHA256:
`766786c0610055652eeec15e92bd184a18d51d53175eb92f657ad586943b3c02`.
It also independently ran the retained regression file and a separate fixture
covering the smallest dimension, a middle parameter, arbitrary upper endpoint,
arbitrary exact source parameters with `NeZero` derived from the dimension
bound, generic transpose/reindex commutation, and an actual swapped PPT
witness at `γ = 1/3` with scaled quadratic value exactly `-8/9`.

All three public declarations have transitive axiom sets exactly
`propext`, `Classical.choice`, and `Quot.sound`. The reviewer checked the
58-module repository import closure: acyclic, with no prohibited proof tokens.
This is an automated mathematical audit, not a human or GitHub approval.

## Validation performed

- Matching prebuilt Mathlib artifacts were verified before builds.
  Lean is `v4.35.0-rc3`, Mathlib is
  `c55e6e786f49471c72fbddbec5415808896aec1e`. Every Git dependency was checked
  against the manifest, and toolchain/dependency pins are unchanged.
- `lake --fail-fast build QICLean.Channel.ChoiTypeMap.Indecomposable` passed
  (3562 jobs). No Mathlib Lean module was rebuilt. Changed production is
  clean under strict flags.
- `python3 scripts/ci_lean_checks.py strict --base 87cb104a --jobs 1` passed
  after the implementation commit: exactly one changed production file and
  one test file. It uses all repository strict flags, standard linters, and
  warnings as errors.
- `QICLeanTest/ChoiTypeIndecomposable.lean` checks `d=3,n=1`, `d=5,n=2`, the
  arbitrary upper endpoint, arbitrary-parameter nondecomposability and
  indecomposability, actual smallest-dimension PPT witness, middle-parameter
  negative scaled quadratic form, and all three transitive axiom guards.
- Native `lake exe lint_style` passed. No Mathlib Lean source module was
  rebuilt.
- All 52 Python unit tests discovered under `scripts/test_*.py` passed after
  fetching the pinned tenkz dependency and installing the repository's
  `texra-blueprint@v0.3.8` tooling in a temporary virtual environment.
- Generated import check passed: 40 aggregators cover 1329 production modules;
  no generated import changes are needed.
- Blueprint synchronization, regenerated ignored `lean_decls`, changed-public-
  declaration reverse coverage, reader-facing prose check, and paper-gap
  reference/name checks passed. The exact full-range entry and coverage ledger
  now describe the completed proof; the Ha note retains the stronger atomicity
  boundary.
- Oversized-file and numbered-module policies, proof-integrity scan, and
  `git diff --check` passed.

## Hosted validation and integration follow-up

The first hosted run for PR #999 at
`a10490aeab9d715dd4fbd8b7e2d53e8f5928ca2f` passed the full library build,
strict affected-source and regression checks, compilation-time gates, text
style, compiled global Blueprint declaration checking, and module policies.
Paper-gap PDFs also passed. The Blueprint job then stopped at bibliography
generation because the new entry used the absent key `Wolf2012QChannels`.
The correction uses the registered key `Wolf2012Quantum`; the ordinary
`texra-blueprint bbl` check passes locally. No check was weakened or skipped
to accommodate the failure.

Main `4a4ba880ae0f20cdfbe7723e3ac2cfc26073a2d5` was integrated with a normal
merge, preserving the other authors' peripheral-spectrum and block-injectivity
changes. The proof, dedicated regressions, foundational witness modules, and
dependency pins are unchanged. Narrow strict, generated-export, Blueprint
source synchronization, and prose checks were rerun after integration.

Evidence: [initial hosted run](https://github.com/LionSR/QICLean/actions/runs/40917177135).
Full Blueprint PDF/web and browser checks require a successful subsequent
hosted run. No downstream TNLean build or local Blueprint visual inspection
was performed. No mathematical blocker remains; final hosted integration
results must be checked before any readiness transition or merge.
