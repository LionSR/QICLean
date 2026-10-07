# Typical-state estimates on physical regions

The mathematical reference is OpenAI, *A two-dimensional area law from a global
spectral gap* (September 24, 2026), at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, `07-comparators.tex`, lines
240–247 and equation `comparator:post-marginal`. The production source revision
is `9366e598b122bab020558c3fbbe3f1bd55e7a990`.

The existing actual marginal of one fixed physical region X determines the
spectral selection. The corresponding normalized projected vector is expressed
in the original global configuration basis, and depends only on X and the
selected eigenvalue indices. Its norm is one and its actual X marginal is the
normalized spectral restriction when the selected mass is positive.

For every disjoint physical region B, the actual selected B marginal is bounded
in positive-semidefinite order by the original B marginal divided by the
selected mass. For a unit original vector, its entropy obeys the same upper
bound. Both conclusions use internally proved canonical-coordinate identities
and the existing three-factor theorems. No supplied coordinate or marginal
certificate, enlarged-region spectral assumption, full rank, or assumed entropy
inequality occurs. Empty regions and arbitrary finite local basis types remain
in the signatures.

`build.log` records the successful module target after the pinned Mathlib cache
was fetched and verified. `strict-source.log` records the complete source with
warnings as errors, standard Mathlib linters, and strict implicit arguments.
`axioms.log` records all six exact public declarations, including the global
vector definition; every report uses only `propext`, `Classical.choice`, and
`Quot.sound`. The diagnostic file disables only the linter against hash commands.
`regressions.log` records a kernel-checked uniform consequence: one vector is
chosen before all disjoint observed regions, and has unit norm and both bounds
simultaneously for every such region. All four commands exited successfully.

The unique blueprint fragment is `ch12_entropy_regional_typical_state.tex`.
Shared imports, fragment inclusion, full combined builds, and global blueprint
checks belong to the integration branch. This new source and its evidence are
independent of the existing typical-density and three-factor source records;
those production files have not changed.

Codex (GPT-6) assisted this independently written formalization. No upstream Lean
proof text was copied or adapted. Exact per-declaration original notices and
hashed verification records are in `regionalTypicalState8753.json`.
