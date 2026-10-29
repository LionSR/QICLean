# Convex trace functions on arbitrary intervals

Original implementation and guard commits are preserved locally.
Publication base: `14ecc5b64bb61cccb01a6583bbab3252bee1486b`.
The proof source and tests are unchanged from the independently reviewed version.

## Source and mathematical boundary

Wolf, convex trace-functions corollary following Theorem 5.17,
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 1081–1088.
The issue and all four comments were reread, and open pull requests refreshed
before edits. No competing arbitrary-interval trace-corollary work was found.
The active entropic Jensen and convex Ando–Lieb contributions were left alone.

`Matrix.convexOn_trace_cfc` proves that the real trace of the functional calculus
of an arbitrary scalar-convex function is convex on precisely the Hermitian
matrices with real spectrum contained in the given convex real set. This includes
all real intervals, open or closed, including those excluding zero.
`Matrix.convex_hermitianSpectralDomain` proves the domain is convex;
`Matrix.IsHermitian.trace_cfc_convex_le` supplies the binary inequality with
nonnegative weights summing to one; `Matrix.trace_cfc_sum_le` gives both domain
membership and the trace bound for finite probability mixtures.

There is no positivity, operator convexity, commutation, continuity, invertibility,
nonempty-dimension, function-at-zero or zero-in-interval premise. Unit-vector
expectations are finite scalar convex combinations of the input eigenvalues.
Applying that fact to each mixture eigenvector proves spectral membership.
Scalar Jensen, followed by summation in that eigenbasis, gives the trace bound.
Arbitrary functions have the usual finite-spectrum Hermitian functional calculus;
its agreement with generic functional calculus is used explicitly. Empty index
types have empty spectrum and zero trace, including for an empty interval.

Theorem 5.17 / weighted Equation (5.51), the other source environments, and the
full issue umbrella remain outside this completed corollary.

## Owned files

- `QICLean/Analysis/TraceConvexFunctions.lean`: seven public declarations.
- `scripts/Tests/TraceConvexFunctions.lean`: actual-name endpoint, exact
  `t,1-t`, empty-dimension/empty-interval, arbitrary-function, finite-mixture,
  standard-axiom and kernel-body guards.
- `scripts/Tests/TraceConvexFunctionsReview.lean`: independently authored
  negative noncommuting matrix regression on `[-2,-1]`.
- `blueprint/src/chapter/ch06_trace_convex_functions.tex`: focused mathematical fragment.
- `blueprint/src/chapter/ch06_operator_convexity.tex`: one fragment input.
- `QICLean/Analysis.lean`: one generated import.
- `docs/wolf_numbering_coverage.md`: localized corollary disposition; historical tally retained.
- This audit note.

The QICLean import closure is acyclic and consists only of the new module,
`Analysis.SpectralQuadraticForm`, and `Analysis.TraceCFC`.

## Independent native review

A separate native agent read the exact source, actual statements and proof bodies,
spectral-weight and trace dependencies, and the Blueprint/coverage changes.
Verdict: **PASS; no blockers**. It independently reran strict production and both
regressions, and authored the explicit negative noncommuting regression. This is
an automated mathematical review, not a human review or a submitted approval.

The reviewer traversed 37,113 kernel declarations and 35,135 bodies, including
31 opaque bodies, with no missing, unsafe or partial declarations. The axioms
were exactly `propext`, `Classical.choice`, `Quot.sound`. Its audit code was then
retained in the main permanent regression alongside the seven actual-name guards.
The reviewed production source SHA256 is
`7f758743108b0ce8b861370bb9b7d0107432f70aa091b5740e5024eae793d9ba`.

## Validation and reproducibility

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.
Root/docbuild toolchain and dependency files are unchanged.
`lake exe cache get` reported no downloads and
8,943 already decompressed files before any build. Matching cached Mathlib
artifacts were used; no Mathlib Lean source module was rebuilt. The native text
linter compiled native objects from cached generated C.

Passed:

- `lake build QICLean.Analysis.TraceConvexFunctions` (2,733 jobs, cached Mathlib).
- Strict direct Lean elaboration of production, both QICLean prerequisites and
  both focused regressions, with `autoImplicit=false`, `relaxedAutoImplicit=false`,
  `pp.unicode.fun=true`, `maxSynthPendingDepth=3`, `linter.mathlibStandardSet=true`,
  `warningAsError=true`.
- All seven public actual-name standard-axiom guards; independent full kernel
  type/body audit described above.
- Explicit endpoint weights zero and one, exact requested mixing form, empty
  interval and empty matrix dimension, arbitrary functions including unrestricted
  value at zero, and a three-term mixture with a zero weight.
- Explicit noncommutation and non-PSD evidence for both negative matrices,
  actual spectra in `[-2,-1]`, and the theorem for every convex function on that
  interval and every mixing parameter.
- `lake exe lint_style`, generated-import check, numbered/oversized module
  policies, proof-integrity token scan across the three-module QICLean closure,
  changed reader-facing prose check, and whitespace checks.
- Source-level Blueprint synchronization and reverse coverage for every public
  declaration. The seven referenced declarations also pass compiled-name guards.
- Two-pass XeLaTeX rendering of the focused fragment using the repository's
  actual common/print macros, with all new entries visually inspected. It has
  one minor 1.75-point overfull-box warning and ordinary unicode-math warnings.

Reproduce focused checks from the repository root with the pinned Lean toolchain:

```sh
lake exe cache get
lake build QICLean.Analysis.TraceConvexFunctions
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 -Dlinter.mathlibStandardSet=true -DwarningAsError=true QICLean/Analysis/TraceConvexFunctions.lean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 -Dlinter.mathlibStandardSet=true -DwarningAsError=true scripts/Tests/TraceConvexFunctions.lean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 -Dlinter.mathlibStandardSet=true -DwarningAsError=true scripts/Tests/TraceConvexFunctionsReview.lean
lake exe lint_style
python3 scripts/generate_import_aggregators.py --check
python3 scripts/blueprint_lean_sync.py --ci --warn-missing-blueprint --diff-base origin/main --changed-files QICLean/Analysis/TraceConvexFunctions.lean
python3 scripts/check_reader_facing_prose.py --diff-base origin/main --ci
```

## Initial local validation limits

The repository strict selector was actually run with `--base origin/main`.
The new production module and both regressions passed. Its generated
`QICLean/Analysis.lean` check failed because the unrelated preexisting
`QICLean/Analysis/AdjointEigenvalues.olean` is absent in this targeted setup.
At that stage, no full-library/Analysis build was started to fill the unrelated artifact.
The generated import is checked by the repository generator; successful compiled
elaboration of the whole aggregator is not claimed.

The full library build, global compiled Blueprint declaration checking, complete
Blueprint PDF/web builds and browser tests, hosted CI, and performance timing
gates were not run. `leanblueprint` and `chktex` are not installed here.
A direct interpreted text-linter attempt hit a Lean interpreter assertion; the
normal native `lake exe lint_style` invocation then passed without exceptions.
The focused excerpt was rendered locally and visually inspected. Local validation
logs are retained with the working copy; executor-specific locations are omitted.

## Publication preparation

The original proof commits remain on the local feature branch. Publication uses
a separate branch based on refreshed main and the account's established public
noreply identity. The mathematical source, regression tests and dependency pins
are unchanged. The only shared-file edits are one generated Analysis import,
one Blueprint fragment input, and the localized coverage subsection. Other open
contributions touch different entries in the coverage ledger; they are not copied
or replaced here.

No ready-for-review transition, review approval, merge, account/security change,
or paid evaluation is part of this contribution. Keep the pull request in draft;
the parent coordinator handles integration and readiness.

Publication validation refresh: the matching pinned Mathlib cache was reverified,
and a targeted `QICLean.Analysis` export build was started to fill the missing
QICLean prerequisites. Its result and hosted CI are pending; no full validation
success is claimed by this note.
