# Wolf Theorem 5.15: convex exponent region

Source: [Theorem 5.15, Equations (5.47)–(5.48)](https://github.com/LionSR/QICLean/blob/87cb104a853153751bc4932cf3c55427a1d99724/Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex#L967-L989).
Owning package: [issue 27](https://github.com/LionSR/QICLean/issues/27).

The issue and its comments, and all seven currently open pull requests, were
read before implementation. No open pull request covered this convex region.
The issue remained open and unassigned when rechecked. No GitHub mutations,
collaborator messages, pushes, pull requests, or merges were made.

Worktree: `/workspace/QICLean-wolf515`, branch `codex/wolf-5-15-convex`, based on
`87cb104a853153751bc4932cf3c55427a1d99724`. The original worktree remains clean.

## Proved statements

`QICLean/Analysis/LiebConvexity.lean` proves:

- `lieb_convexity_variational_le`: the completed-square variational bound on
  positive semidefinite `A` and positive definite `B`.
- `lieb_convexity_posSemidef_posDef`: for arbitrary complex `K`, every
  $x\in[1,2]$, $y\in[1-x,0]$, and $t\in[0,1]$, the joint convexity inequality
  for $\Re\operatorname{tr}(K^\dagger A^xKB^y)$ on $A\geq0$, $B>0$.
- `lieb_convexity_posDef`: its positive definite pair specialization.
- `convexOn_re_trace_conj_rpow_mul_rpow`: convexity on the actual product of
  positive definite cones, with fixed arbitrary complex `K`.

There are no commutation assumptions, supplied convexity premises, nonzero
dimension restrictions, omitted exponent endpoints, proof holes, or new axioms.

The proof reuses `lieb_concavity_subboundary` at exponents $2-x$ and $-y$.
The quadratic variational expression has optimizer $A^{x-1}KB^y$.
Positivity of $\operatorname{tr}((X-H)^\dagger A^{2-x}(X-H)B^{-y})$ supplies
the bound, and evaluation at the optimizer of the mixed pair supplies convexity.
This is a direct trace alternative to the suggested perspective/tensor route;
no new operator-Jensen theorem or tensor transpose identity is needed.
Only powers of the positive definite second argument are cancelled against
negative powers. Nonnegative exponent laws allow singular first arguments.

## Validation

Lean and Mathlib remain pinned to `v4.35.0-rc3`; Mathlib revision is
`c55e6e786f49471c72fbddbec5415808896aec1e`. The isolated worktree reuses the
existing dependency directory. `lake exe cache get` succeeded before builds:
8943 cached modules were already decompressed; no downloads were needed.

Passed:

- Targeted ordinary build of `QICLean.Analysis.LiebConvexity` and its imports.
- Direct strict production elaboration with `autoImplicit=false`,
  `relaxedAutoImplicit=false`, standard Mathlib linters, and warnings as errors.
- The same strict elaboration of
  `QICLeanTest/Analysis/LiebConvexityAxioms.lean`.
- All four public results use exactly `propext`, `Classical.choice`, `Quot.sound`.
- Fixtures for all three exponent vertices, the empty matrix algebra, a
  singular first argument, and failure of the zero-valued singular inverse.
- `lake exe lint_style`, generated import checks, Blueprint source synchronization,
  new-prose checks, module-name and size policies, and whitespace checks.
- Focused rendering and visual inspection of the two exact new Blueprint entries.

The mathematical build used cached Mathlib object files and elaborated only
QICLean modules. Building the style executable additionally generated native
`:c.o` facets from cached Mathlib IR; it did not re-elaborate Mathlib Lean sources.
Logs are retained under `/tmp/wolf515-*` in this environment.

Not run: the full repository build, full compiled `leanblueprint checkdecls`,
or the complete Blueprint web/PDF build. The test imports the actual new compiled
module and checks all four referenced declaration names. Canonical standalone
rendering of `wolf_ch5_lieb_convexity_domain.tex` failed because the pre-existing
shared `command.tex` requires unavailable `dsfont.sty`; this is a missing TeX
dependency, not an approval denial. The focused Blueprint PDF is
`/tmp/wolf515-paper/blueprint-excerpt.pdf`.

## Scope and documentation

The Blueprint, bibliography, generated Analysis import, numbering coverage,
existing Jensen/Lieb note, and proof-pattern ledger are synchronized.
`docs/paper-gaps/wolf_ch5_lieb_convexity_domain.tex` records the invertible
domain and the scalar counterexample to using a zero-valued inverse at singular
`B`. No extended-real or support-dependent singular extension is asserted.
The containing issue and unrelated Chapter 5 environments remain open; no
aggregate named-environment count is reclassified by this local milestone.
