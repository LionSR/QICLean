# Rectangular entropic Jensen inequality

The source is Wolf, Chapter 5, Corollary 5.1, Equation (5.33), in
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 699–705.
The baseline is `87cb104a853153751bc4932cf3c55427a1d99724`.

`IsPositiveMap.entropic_jensen` proves the source statement for a positive
unital map between arbitrary finite matrix algebras and any PSD input.
`IsPositiveMap.entropic_jensen_subunital` proves its valid subunital
strengthening. Neither statement assumes complete positivity, trace
preservation, trace normalization, or invertibility. Empty index types are
permitted. This completes this corollary, not the general package in issue #28.

The proof takes the right derivative at exponent one in the existing square
power Jensen inequality. Zero eigenvalues have identically zero difference
quotient. Finite spectra give norm convergence. Extending the rectangular map
between complementary diagonal blocks then gives the general statement. This
direct proof uses the established special-function theorem and does not assume
the still-open arbitrary-function Jensen theorem invoked in Wolf's exposition.

## Independent review

A separate native agent, `entropic_semantic_review`, read the exact source,
actual statements, proof bodies, and load-bearing dependencies at local proof
commit `60c79779e1ab9d0aa4198711222ef72c08ddd28e`. Its verdict was PASS, with no
hidden hypotheses or proof-integrity blockers. It independently ran strict
elaboration, checked the logical axioms, and instantiated unequal dimensions,
zero inputs, and empty indices. A second review of the integration changes
found the Blueprint proof, coverage entry, scope note, generated import, and
permanent tests faithful. The production proof remained unchanged.

This is an independent automated review, not a human review or a GitHub
approval. No merge-readiness claim follows from it.

## Validation

- Lean `v4.35.0-rc3`, Mathlib
  `c55e6e786f49471c72fbddbec5415808896aec1e`; the matching prebuilt cache was
  fetched successfully before building. No Mathlib Lean source module was
  rebuilt. Building the text-linter executable compiled native objects from
  cached generated C artifacts.
- Targeted `lake build QICLean.Channel.Schwarz.EntropicJensen` passed.
- Production and permanent test elaboration passed with standard Mathlib
  linters and warnings treated as errors.
- `QICLeanTest/EntropicJensen.lean` guards both public theorems' axioms and
  checks zero input, a rank-one singular projection at unequal dimensions,
  empty source and target indices, and the rectangular zero map. Both
  theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Text style, generated imports, source-level Blueprint synchronization and
  reverse coverage, added prose, module policies, and whitespace checks passed.
- Both new Blueprint entries rendered successfully in a focused one-page
  excerpt and were visually inspected.

The full library build, compiled global declaration check, full Blueprint
web/PDF, and canonical scope-note PDF were not run locally. The local TeX
installation lacks `dsfont.sty`; hosted CI supplies the complete TeX stack.
These full checks remain CI gates.

## Integration boundaries

Fresh remote `main` and the thirteen active PR file lists were checked before
publication. No duplicate entropic theorem or PR was found. PRs #990, #991,
#993, and #994 also change `docs/wolf_numbering_coverage.md` in other sections.
This contribution adds a localized Chapter 5 entry and preserves the dated
audit tally; merge ordering must retain all independent coverage additions.

The proof reuses `Matrix.cfc_fromBlocks_diag` from
`Analysis/OperatorMean/BlockDiagonal.lean`. This import adds thirty QICLean
modules beyond the eighteen-module `LiebConcavity` prerequisite cone. Moving
that general functional-calculus result to a smaller owning module could
reduce dependencies in a separate change. It is not duplicated here.

OpenAI Codex assisted with implementation, documentation, and validation.
