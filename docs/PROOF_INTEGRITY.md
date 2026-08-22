<!-- Pointer: the canonical document lives in the lean-conventions skill of
     texra-ai/texra-lean-skills, installed automatically in Claude Code
     sessions by .claude/settings.json (other agents: see the install
     instructions in that repository's README). Only the project addendum
     below is repo-local. -->

# Lean Proof Integrity Rules

Canonical text: the `lean-conventions` skill —
[PROOF_INTEGRITY.md](https://github.com/texra-ai/texra-lean-skills/blob/main/skills/lean-conventions/references/PROOF_INTEGRITY.md).
Consult it through the installed skill; do not restate its rules here.

## Project addendum (QICLean)

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
