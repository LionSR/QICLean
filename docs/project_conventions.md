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

Configurations with one local alphabet `Fin (n v)` per site are written with a named region and a
raw site type: `ManyBody.RegionConfig (fun v ↦ Fin (n v)) D` for a region, `(∀ v, Fin (n v))`
for all sites. The raw region type `(v : {v // v ∈ D}) → Fin (n v)` stops the `ManyBody` lemmas
from inferring the family (`?X ↑v =?= Fin (n ↑v)` is not a pattern), and the named site type
`ManyBody.Config (fun v ↦ Fin (n v))` leaves `σ v : (fun v ↦ Fin (n v)) v` unreduced, so
`rw [h] at hv` with `h : n v = 0` fails.

### Decidability and finiteness instances in the Sites and Circuit layers

The definitions of `ManyBody/Sites` and `Circuit` (matrices, operators, subspaces and
predicates on finite configurations) do not compute, and their values do not depend on a choice
of decidability or finiteness instance. They follow three rules.

1. A definition takes instance arguments only on the site type `V` and on the basis types
   `X v` (`[Fintype V]`, `[DecidableEq V]`, `[∀ v, Fintype (X v)]`,
   `[∀ v, DecidableEq (X v)]`). An instance it needs on configurations, regions, complements or
   environments is derived inside it, from these instances or by `classical`, and is not an
   argument.
2. When the type of a definition contains an instance on configurations, the instance cannot be
   derived inside and is an argument at the type that carries it. This is the case of the
   homomorphisms of matrix algebras, whose unit depends on a decidable equality of the
   configurations: besides `[DecidableEq W]` on its sites, `ManyBody.placeAlongHom` takes
   `[DecidableEq (Config fun u ↦ X (w u))]` and `[DecidableEq (Config X)]`, so that it exists
   for every choice of them, including the classical one.
3. A lemma takes the instances on configurations that its statement mentions as arguments, at
   the type that carries them, and holds for every choice. Its proof first identifies them with
   the canonical ones, as in `ManyBody.place_one`:
   `obtain rfl : ‹DecidableEq (RegionConfig X D)› = Fintype.decidablePiFintype :=
   Subsingleton.elim _ _`; for `Fintype` the canonical instance is `Pi.instFintype`.

A predicate that quantifies existentially over basis types with their instances, such as
`QuantumCircuit.IsUnitaryDilation` over the environments `E s` and `F s`, satisfies rule 1: the
instances are part of the witness, chosen by whoever proves the predicate and received by
whoever uses it, so no mismatch can arise. The proof of `QuantumCircuit.Layer.isUnitaryDilation`
supplies named classical instances for its environments rather than calling `classical`,
because instance search on those environments, products and functions of the dilating bases,
runs into the heartbeat limit.

## Proof integrity (PROOF_INTEGRITY)

### Sanctioned-axiom history

There are no sanctioned axiom declarations in this repository; any new
`axiom` declaration is a blocker. Historically,
`hayashi_ssa_equality_characterization_forward` in
`QICLean/Axioms/Entropy.lean` was sanctioned for issue #632 / gate #236. It is
now a theorem proved in `QICLean/Entropy/StrongSubadditivity/EntropyMarkovForward.lean`; the
compatibility module was relocated to
`QICLean/Entropy/StrongSubadditivity/MarkovChain.lean`, which retains the
established public name. The reverse direction is proved in
`QICLean/Entropy/StrongSubadditivity/EntropyMarkovReverse.lean`, and the biconditional combines
the two proved implications.

`QICLean/Channel/Convexity/LiebConcavity.lean` (formerly
`QICLean/Axioms/OperatorConvexity.lean`) declares no axioms: the operator
Jensen inequalities for the concave real power, convex real power, and
logarithm (`posMap_rpow_concave_jensen`, `posMap_rpow_convex_jensen`,
`posMap_log_concave_jensen`) and Lieb's concavity theorem
(`lieb_concavity_posDef`) are all proved there. The former
`trace_rpow_concave_axiom` / `trace_rpow_convex_axiom` were discharged
earlier; see `QICLean/Analysis/Convexity/OperatorConvexity.lean`. The `QICLean/Axioms/`
directory held only proved theorems and was dissolved: its four modules
were relocated to their subject homes and the `_axiom` suffix was dropped
from the one declaration name that still carried it.

## Prose (prose_style)

- No migrated docstring region is currently designated (the monorepo this
  library was extracted from designated `TNLean/MPS/ParentHamiltonian`).
