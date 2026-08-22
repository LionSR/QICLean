# QICLean-local convention addenda

The canonical convention documents live in the `lean-conventions` skill of
[texra-ai/texra-lean-skills](https://github.com/texra-ai/texra-lean-skills)
(auto-installed for Claude Code sessions via `.claude/settings.json`; other
agents: `npx skills add texra-ai/texra-lean-skills`). This file holds only
QICLean's project-local facts — it restates no shared rule, and shared rules
never move here.

## Style (MATHLIB_style)

QICLean exercises the repository-local pass-through exception described in
the deprecation section: a public declaration that merely forwards to an
existing theorem, exposes a bundled-structure field, or names a proof step
now written at the use site may be removed without a transition declaration,
provided all non-`Archive` uses are migrated, no blueprint `\lean{...}` tag
cites the old name, and the PR body plus an audit note name each removed
declaration with its replacement.

## Proof integrity (PROOF_INTEGRITY)

### Sanctioned-axiom history

There are no sanctioned axiom declarations in this repository; any new
`axiom` declaration is a blocker. Historically,
`hayashi_ssa_equality_characterization_forward` in
`QICLean/Axioms/Entropy.lean` was sanctioned for issue #632 / gate #236. It is
now a theorem proved in `QICLean/Analysis/EntropyMarkovForward.lean`; the
compatibility module was relocated to
`QICLean/Entropy/SSAEqualityCharacterization.lean`, which retains the
established public name. The reverse direction is proved in
`QICLean/Analysis/EntropyMarkovReverse.lean`, and the biconditional combines
the two proved implications.

`QICLean/Analysis/LiebConcavity.lean` (formerly
`QICLean/Axioms/OperatorConvexity.lean`) declares no axioms: the operator
Jensen inequalities for the concave real power, convex real power, and
logarithm (`posMap_rpow_concave_jensen`, `posMap_rpow_convex_jensen`,
`posMap_log_concave_jensen`) and Lieb's concavity theorem
(`lieb_concavity_posDef`) are all proved there. The former
`trace_rpow_concave_axiom` / `trace_rpow_convex_axiom` were discharged
earlier; see `QICLean/Analysis/OperatorConvexity.lean`. The `QICLean/Axioms/`
directory held only proved theorems and was dissolved: its four modules
were relocated to their subject homes and the `_axiom` suffix was dropped
from the one declaration name that still carried it.

## Prose (prose_style)

- No migrated docstring region is currently designated (the monorepo this
  library was extracted from designated `TNLean/MPS/ParentHamiltonian`).
